#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Keep the public Lean toolchain and dependency lock mutually consistent."""

from __future__ import annotations

import copy
import json
import re
import tempfile
import tomllib
from pathlib import Path
from typing import Any


ROOT = Path(__file__).resolve().parent.parent
LEAN_TOOLCHAIN_RE = re.compile(r"leanprover/lean4:(v[0-9]+\.[0-9]+\.[0-9]+)")
COMMIT_RE = re.compile(r"[0-9a-f]{40}")
MATHLIB_URL = "https://github.com/leanprover-community/mathlib4"
RELEASE_VALIDATOR_REQUIREMENTS = (
    ("Jinja2", "3.1.6"),
    ("MarkupSafe", "3.0.3"),
    ("attrs", "26.1.0"),
    ("boolean.py", "5.0"),
    ("certifi", "2026.7.22"),
    ("cffconvert", "2.0.0"),
    ("charset-normalizer", "3.5.1"),
    ("click", "8.5.0"),
    ("docopt", "0.6.2"),
    ("idna", "3.19"),
    ("jsonschema", "3.2.0"),
    ("license-expression", "30.4.4"),
    ("pykwalify", "1.8.0"),
    ("pyrsistent", "0.20.0"),
    ("python-dateutil", "2.9.0.post0"),
    ("python-debian", "1.1.1"),
    ("python-magic", "0.4.27"),
    ("requests", "2.34.2"),
    ("reuse", "6.2.0"),
    ("ruamel.yaml", "0.19.1"),
    ("setuptools", "84.0.0"),
    ("six", "1.17.0"),
    ("tomlkit", "0.15.1"),
    ("urllib3", "2.7.0"),
)
RELEASE_INSTALL_COMMAND = (
    "python3 -m pip install --disable-pip-version-check --no-cache-dir "
    "--require-hashes "
    "--requirement requirements-release.txt"
)
REQUIREMENT_PIN_RE = re.compile(
    r"^([A-Za-z0-9][A-Za-z0-9_.-]*)==([^\s#]+)"
    r"(?:\s+--hash=sha256:[0-9a-f]{64})+$"
)


def encode_manifest(manifest: dict[str, Any]) -> str:
    return json.dumps(manifest, ensure_ascii=False)


def dependency_lock_errors(
    toolchain_text: str,
    lakefile_text: str,
    manifest_text: str,
) -> list[str]:
    """Return proof-environment identity and pinning failures."""
    errors: list[str] = []
    toolchain = toolchain_text.strip()
    toolchain_match = LEAN_TOOLCHAIN_RE.fullmatch(toolchain)
    if toolchain_match is None:
        errors.append("lean-toolchain lost the exact Lean release identity")
        lean_release = None
    else:
        lean_release = toolchain_match.group(1)

    try:
        lakefile = tomllib.loads(lakefile_text)
    except tomllib.TOMLDecodeError:
        errors.append("lakefile.toml is not valid TOML")
        return errors
    try:
        manifest = json.loads(manifest_text)
    except json.JSONDecodeError:
        errors.append("lake-manifest.json is not valid JSON")
        return errors

    if manifest.get("name") != lakefile.get("name"):
        errors.append("Lake project name drifted between lakefile and manifest")

    mathlib_requirements = [
        row
        for row in lakefile.get("require", [])
        if row.get("name") == "mathlib"
    ]
    if len(mathlib_requirements) != 1:
        errors.append("lakefile must declare exactly one direct Mathlib requirement")
        expected_mathlib_input = None
    else:
        requirement = mathlib_requirements[0]
        expected_mathlib_input = requirement.get("rev")
        if requirement.get("scope") != "leanprover-community":
            errors.append("Mathlib requirement lost its leanprover-community scope")
        if expected_mathlib_input != lean_release:
            errors.append("Mathlib input revision drifted from the Lean toolchain")

    packages = manifest.get("packages")
    if not isinstance(packages, list) or not packages:
        errors.append("lake-manifest.json lost its pinned package list")
        return errors

    names = [row.get("name") for row in packages]
    if any(not isinstance(name, str) or not name for name in names):
        errors.append("manifest package lost its nonempty name")
    if len(names) != len(set(names)):
        errors.append("manifest package names are not unique")

    for row in packages:
        name = row.get("name", "<unnamed>")
        if row.get("type") != "git":
            errors.append(f"manifest package {name} is not a Git dependency")
        if COMMIT_RE.fullmatch(str(row.get("rev", ""))) is None:
            errors.append(f"manifest package {name} lacks a full commit revision")
        if not str(row.get("url", "")).startswith("https://"):
            errors.append(f"manifest package {name} lacks an HTTPS source URL")

    mathlib_packages = [row for row in packages if row.get("name") == "mathlib"]
    if len(mathlib_packages) != 1:
        errors.append("manifest must contain exactly one Mathlib package")
    else:
        mathlib = mathlib_packages[0]
        if mathlib.get("inherited") is not False:
            errors.append("Mathlib manifest package must remain a direct dependency")
        if mathlib.get("scope") != "leanprover-community":
            errors.append("Mathlib manifest package lost its canonical scope")
        if mathlib.get("url") != MATHLIB_URL:
            errors.append("Mathlib manifest package lost its canonical source URL")
        if mathlib.get("inputRev") != expected_mathlib_input:
            errors.append("Mathlib manifest input revision drifted from lakefile")
    return errors


def release_validator_lock_errors(
    requirements_text: str,
    workflow_text: str,
) -> list[str]:
    """Return release-validator lock and workflow-install failures."""
    errors: list[str] = []
    parsed: list[tuple[str, str]] = []
    for line_number, raw_line in enumerate(requirements_text.splitlines(), 1):
        line = raw_line.strip()
        if not line or line.startswith("#"):
            continue
        match = REQUIREMENT_PIN_RE.fullmatch(line)
        if match is None:
            errors.append(
                "requirements-release.txt line "
                f"{line_number} must be an exact name==version pin"
            )
            continue
        parsed.append((match.group(1), match.group(2)))

    if parsed != list(RELEASE_VALIDATOR_REQUIREMENTS):
        errors.append(
            "requirements-release.txt must contain exactly the pinned "
            "release-validator package set"
        )

    if RELEASE_INSTALL_COMMAND not in workflow_text:
        errors.append(
            "release workflow must install metadata validators from "
            "requirements-release.txt with the pinned command"
        )
    if "pip install cffconvert reuse" in workflow_text:
        errors.append(
            "release workflow must not resolve metadata validators from "
            "moving package names"
        )
    return errors


def require(condition: bool, message: str) -> None:
    """Keep contract checks active when CI invokes Python with ``-O``."""
    if not condition:
        raise AssertionError(message)


class UnsafeDependencyInput(ValueError):
    """A release-lock input escaped the checkout or is not a file."""


def safe_dependency_file(root: Path, relative: str) -> Path:
    """Read only regular, non-symlink files beneath the asserted checkout."""
    path = Path(relative)
    if path.is_absolute() or ".." in path.parts:
        raise UnsafeDependencyInput(f"non-relative dependency input: {relative}")

    candidate = root / path
    root_resolved = root.resolve()
    current = root
    for component in path.parts:
        current /= component
        if current.is_symlink():
            raise UnsafeDependencyInput(f"symlinked dependency input: {relative}")

    resolved = candidate.resolve()
    if resolved != root_resolved and root_resolved not in resolved.parents:
        raise UnsafeDependencyInput(f"dependency input escaped checkout: {relative}")
    if not candidate.is_file():
        raise UnsafeDependencyInput(
            f"dependency input is not a regular file: {relative}"
        )
    return candidate


def main() -> int:
    toolchain = safe_dependency_file(ROOT, "lean-toolchain").read_text(
        encoding="utf-8"
    )
    lakefile = safe_dependency_file(ROOT, "lakefile.toml").read_text(
        encoding="utf-8"
    )
    manifest = safe_dependency_file(ROOT, "lake-manifest.json").read_text(
        encoding="utf-8"
    )
    requirements = safe_dependency_file(
        ROOT, "requirements-release.txt"
    ).read_text(encoding="utf-8")
    workflow = safe_dependency_file(
        ROOT, ".github/workflows/lean.yml"
    ).read_text(encoding="utf-8")
    require(
        not dependency_lock_errors(toolchain, lakefile, manifest),
        "the live Lean dependency lock must satisfy its contract",
    )
    require(
        not release_validator_lock_errors(requirements, workflow),
        "the live release-validator lock must satisfy its contract",
    )

    lake_rev_drift = lakefile.replace('rev = "v4.29.1"', 'rev = "v4.29.0"', 1)
    require(
        any(
            "drifted from the Lean toolchain" in error
            for error in dependency_lock_errors(toolchain, lake_rev_drift, manifest)
        ),
        "a Lakefile revision drift must be rejected",
    )

    manifest_data = json.loads(manifest)
    input_drift = copy.deepcopy(manifest_data)
    input_drift["packages"][0]["inputRev"] = "v4.29.0"
    require(
        any(
            "input revision drifted from lakefile" in error
            for error in dependency_lock_errors(
                toolchain, lakefile, encode_manifest(input_drift)
            )
        ),
        "a manifest input revision drift must be rejected",
    )

    inherited_mathlib = copy.deepcopy(manifest_data)
    inherited_mathlib["packages"][0]["inherited"] = True
    require(
        any(
            "direct dependency" in error
            for error in dependency_lock_errors(
                toolchain, lakefile, encode_manifest(inherited_mathlib)
            )
        ),
        "an inherited Mathlib dependency must be rejected",
    )

    shortened_revision = copy.deepcopy(manifest_data)
    shortened_revision["packages"][-1]["rev"] = "7802da01"
    require(
        any(
            "full commit revision" in error
            for error in dependency_lock_errors(
                toolchain, lakefile, encode_manifest(shortened_revision)
            )
        ),
        "a shortened package revision must be rejected",
    )

    duplicate_package = copy.deepcopy(manifest_data)
    duplicate_package["packages"].append(copy.deepcopy(manifest_data["packages"][0]))
    require(
        any(
            "names are not unique" in error
            for error in dependency_lock_errors(
                toolchain, lakefile, encode_manifest(duplicate_package)
            )
        ),
        "duplicate package names must be rejected",
    )

    project_name_drift = copy.deepcopy(manifest_data)
    project_name_drift["name"] = "different-project"
    require(
        any(
            "project name drifted" in error
            for error in dependency_lock_errors(
                toolchain, lakefile, encode_manifest(project_name_drift)
            )
        ),
        "a project-name drift must be rejected",
    )

    moving_requirement = requirements.replace("cffconvert==2.0.0", "cffconvert", 1)
    require(
        any(
            "exact name==version pin" in error
            for error in release_validator_lock_errors(moving_requirement, workflow)
        ),
        "an unpinned release requirement must be rejected",
    )

    unhashed_requirement = re.sub(
        r"(?m)^cffconvert==2\.0\.0(?:\s+--hash=sha256:[0-9a-f]{64})+$",
        "cffconvert==2.0.0",
        requirements,
        count=1,
    )
    require(
        any(
            "exact name==version pin" in error
            for error in release_validator_lock_errors(unhashed_requirement, workflow)
        ),
        "an unhashed release requirement must be rejected",
    )

    extra_requirement = requirements + "\npytest==9.0.0\n"
    extra_errors = release_validator_lock_errors(extra_requirement, workflow)
    require(
        any(
            "exactly the pinned" in error
            or "exact name==version pin" in error
            for error in extra_errors
        ),
        "an undeclared release requirement must be rejected",
    )

    moving_install = workflow.replace(
        RELEASE_INSTALL_COMMAND, "pip install cffconvert reuse", 1
    )
    moving_errors = release_validator_lock_errors(requirements, moving_install)
    require(
        any("pinned command" in error for error in moving_errors),
        "a moving release install command must be rejected",
    )
    require(
        any("moving package names" in error for error in moving_errors),
        "a bare metadata-validator install must be rejected",
    )

    with tempfile.TemporaryDirectory(prefix="dependency-lock-boundary-") as raw:
        fixture_root = Path(raw) / "checkout"
        fixture_root.mkdir()
        outside = Path(raw) / "private.toml"
        outside.write_text("name = 'private'", encoding="utf-8")
        (fixture_root / "lakefile.toml").symlink_to(outside)
        try:
            safe_dependency_file(fixture_root, "lakefile.toml")
        except UnsafeDependencyInput:
            pass
        else:
            raise AssertionError("symlinked dependency input was accepted")

    print(
        "test_dependency_lock_contract: Lean, direct Mathlib input, and "
        f"{len(manifest_data['packages'])} exact package revisions plus "
        f"{len(RELEASE_VALIDATOR_REQUIREMENTS)} release-validator pins agree; "
        "11 negative fixtures rejected"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
