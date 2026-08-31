#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Keep the software/manuscript licence split semantically explicit."""

from __future__ import annotations

import copy
import os
import stat
import tempfile
import tomllib
from pathlib import Path
from typing import Any
from unittest.mock import patch


ROOT = Path(__file__).resolve().parent.parent
APACHE = "Apache-2.0"
MANUSCRIPT_LICENSE = "CC-BY-4.0"
SPDX_LICENSE_HEADER = "SPDX-License-" "Identifier: "
MANUSCRIPT_BINARIES = {
    ".github/banner.png",
    "claim-faithful-publication-systems-paper.pdf",
    "cold-clone-to-proof-receipt.pdf",
    "erdos-68-factorial-denominator-irrationality.pdf",
    "erdos-243-reciprocal-tail-rigidity.pdf",
    "erdos-251-prime-gap-dyadic-series.pdf",
    "erdos-269-three-prime-running-lcm.pdf",
    "erdos-1041-lemniscate-newton-flow.pdf",
    "erdos-1049-rational-base-lambert.pdf",
    "erdos-249-binary-totient-series.pdf",
    "erdos-257-mersenne-support-subseries.pdf",
    "erdos249-257-main-paper.pdf",
    "erdos249-totient-reasoning-surface.pdf",
    "erdos257-mersenne-reasoning-surface.pdf",
}
MANUSCRIPT_SOURCES = {
    "paper/claim-faithful-publication-systems-paper.tex",
    "paper/cold-clone-to-proof-receipt.tex",
    "paper/erdos-68-factorial-denominator-irrationality.tex",
    "paper/erdos-243-reciprocal-tail-rigidity.tex",
    "paper/erdos-251-prime-gap-dyadic-series.tex",
    "paper/erdos-269-three-prime-running-lcm.tex",
    "paper/erdos-1041-lemniscate-newton-flow.tex",
    "paper/erdos-1049-rational-base-lambert.tex",
    "paper/erdos-249-binary-totient-series.tex",
    "paper/erdos-257-mersenne-support-subseries.tex",
    "paper/erdos249-257-main-paper.tex",
    "paper/module-aliases.tex",
}


def require(condition: bool, message: str) -> None:
    """Keep licensing contract failures active when run with ``python -O``."""
    if not condition:
        raise AssertionError(message)


def describe(errors: list[str]) -> str:
    """Render an error list so a failure names the violation, not just its kind."""
    if not errors:
        return "no errors reported"
    return "; ".join(errors)


def require_no_errors(errors: list[str], label: str) -> None:
    """Fail with every observed violation, never a bare 'is invalid'."""
    require(not errors, f"{label}: {describe(errors)}")


def require_reports(errors: list[str], fragment: str, label: str) -> None:
    """Fail a negative fixture with the errors it actually produced."""
    require(
        any(fragment in error for error in errors),
        f"{label}; expected an error naming {fragment!r}, got: {describe(errors)}",
    )


class UnsafeLicenseInput(ValueError):
    """A release-licensing input escaped the checkout or is not a file."""


def safe_license_file(root: Path, relative: str) -> Path:
    """Read only regular, non-symlink files beneath the asserted checkout."""
    path = Path(relative)
    if path.is_absolute() or ".." in path.parts:
        raise UnsafeLicenseInput(f"non-relative licensing input: {relative}")

    candidate = root / path
    root_resolved = root.resolve()
    current = root
    for component in path.parts:
        current /= component
        if current.is_symlink():
            raise UnsafeLicenseInput(f"symlinked licensing input: {relative}")

    resolved = candidate.resolve()
    if resolved != root_resolved and root_resolved not in resolved.parents:
        raise UnsafeLicenseInput(f"licensing input escaped checkout: {relative}")
    if not candidate.is_file():
        raise UnsafeLicenseInput(f"licensing input is not a regular file: {relative}")
    return candidate


def safe_license_text(root: Path, relative: str) -> str:
    """Read a licensing input through a no-follow regular-file descriptor."""
    candidate = safe_license_file(root, relative)
    flags = os.O_RDONLY | getattr(os, "O_NONBLOCK", 0) | getattr(os, "O_NOFOLLOW", 0)
    if hasattr(os, "O_CLOEXEC"):
        flags |= os.O_CLOEXEC
    try:
        descriptor = os.open(candidate, flags)
    except OSError as exc:
        raise UnsafeLicenseInput(
            f"licensing input could not be opened safely: {relative}"
        ) from exc
    try:
        if not stat.S_ISREG(os.fstat(descriptor).st_mode):
            raise UnsafeLicenseInput(
                f"licensing input is not a regular file: {relative}"
            )
        chunks: list[bytes] = []
        while True:
            chunk = os.read(descriptor, 1024 * 1024)
            if not chunk:
                break
            chunks.append(chunk)
    except OSError as exc:
        raise UnsafeLicenseInput(
            f"licensing input could not be read safely: {relative}"
        ) from exc
    finally:
        os.close(descriptor)
    try:
        return b"".join(chunks).decode("utf-8")
    except UnicodeDecodeError as exc:
        raise UnsafeLicenseInput(f"licensing input is not UTF-8: {relative}") from exc


def encode_reuse(config: dict[str, Any]) -> str:
    lines = [f"version = {config['version']}", ""]
    for annotation in config["annotations"]:
        lines.append("[[annotations]]")
        paths = annotation["path"]
        if isinstance(paths, str):
            lines.append(f'path = "{paths}"')
        else:
            quoted = ", ".join(f'"{path}"' for path in paths)
            lines.append(f"path = [{quoted}]")
        if "precedence" in annotation:
            lines.append(f'precedence = "{annotation["precedence"]}"')
        lines.append(
            f'SPDX-FileCopyrightText = "{annotation["SPDX-FileCopyrightText"]}"'
        )
        lines.append(
            f'SPDX-License-Identifier = "{annotation["SPDX-License-Identifier"]}"'
        )
        lines.append("")
    return "\n".join(lines)


def annotation_paths(annotation: dict[str, Any]) -> set[str]:
    paths = annotation.get("path")
    if isinstance(paths, str):
        return {paths}
    if isinstance(paths, list) and all(isinstance(path, str) for path in paths):
        return set(paths)
    return set()


def license_map_errors(
    reuse_text: str,
    readme: str,
    manuscript_sources: dict[str, str],
    license_files: set[str],
) -> list[str]:
    """Return semantic release-licensing failures."""
    errors: list[str] = []
    try:
        config = tomllib.loads(reuse_text)
    except tomllib.TOMLDecodeError:
        return ["REUSE.toml is not valid TOML"]

    annotations = config.get("annotations", [])
    blanket = [
        row
        for row in annotations
        if annotation_paths(row) == {"**"}
        and row.get("SPDX-License-Identifier") == APACHE
    ]
    if len(blanket) != 1:
        errors.append("REUSE.toml must contain one Apache-2.0 blanket annotation")

    manuscript_overrides = [
        row
        for row in annotations
        if row.get("precedence") == "override"
        and row.get("SPDX-License-Identifier") == MANUSCRIPT_LICENSE
    ]
    if len(manuscript_overrides) != 1:
        errors.append("REUSE.toml must contain one CC-BY-4.0 override")
    else:
        observed = annotation_paths(manuscript_overrides[0])
        if observed != MANUSCRIPT_BINARIES:
            errors.append(
                "REUSE.toml manuscript binary override must match the exact "
                "rendered-artifact set"
            )

    for path, source in manuscript_sources.items():
        if f"{SPDX_LICENSE_HEADER}{MANUSCRIPT_LICENSE}" not in source:
            errors.append(f"manuscript source {path} lost its CC-BY-4.0 header")
        if f"{SPDX_LICENSE_HEADER}{APACHE}" in source:
            errors.append(f"manuscript source {path} carries an Apache-2.0 header")

    for license_id in (APACHE, MANUSCRIPT_LICENSE):
        if f"LICENSES/{license_id}.txt" not in license_files:
            errors.append(f"licence text is missing for {license_id}")

    readme_boundary = (
        "Code, scripts, and documentation use Apache-2.0; manuscripts use "
        "CC-BY-4.0;"
    )
    if readme_boundary not in readme:
        errors.append("README lost the exact software/manuscript licence boundary")
    return errors


def main() -> int:
    reuse = safe_license_text(ROOT, "REUSE.toml")
    readme = safe_license_text(ROOT, "README.md")
    sources = {
        path: safe_license_text(ROOT, path)
        for path in MANUSCRIPT_SOURCES
    }
    safe_license_dir = ROOT / "LICENSES"
    if safe_license_dir.is_symlink() or not safe_license_dir.is_dir():
        raise UnsafeLicenseInput("LICENSES is not a regular checkout directory")
    license_files = {
        safe_license_file(ROOT, path.relative_to(ROOT).as_posix())
        .relative_to(ROOT)
        .as_posix()
        for path in safe_license_dir.glob("*.txt")
    }
    require_no_errors(
        license_map_errors(reuse, readme, sources, license_files),
        "live license map contract is invalid",
    )

    config = tomllib.loads(reuse)
    missing_override = copy.deepcopy(config)
    missing_override["annotations"] = missing_override["annotations"][:1]
    require_reports(
        license_map_errors(
            encode_reuse(missing_override), readme, sources, license_files
        ),
        "CC-BY-4.0 override",
        "missing manuscript license override was accepted",
    )

    incomplete_override = copy.deepcopy(config)
    incomplete_override["annotations"][1]["path"] = sorted(
        MANUSCRIPT_BINARIES - {"erdos249-257-main-paper.pdf"}
    )
    require_reports(
        license_map_errors(
            encode_reuse(incomplete_override), readme, sources, license_files
        ),
        "exact rendered-artifact set",
        "incomplete manuscript artifact override was accepted",
    )

    wrong_blanket = copy.deepcopy(config)
    wrong_blanket["annotations"][0]["SPDX-License-Identifier"] = MANUSCRIPT_LICENSE
    require_reports(
        license_map_errors(
            encode_reuse(wrong_blanket), readme, sources, license_files
        ),
        "Apache-2.0 blanket",
        "wrong blanket license was accepted",
    )

    lost_source_header = dict(sources)
    path = "paper/erdos249-257-main-paper.tex"
    lost_source_header[path] = lost_source_header[path].replace(
        f"{SPDX_LICENSE_HEADER}{MANUSCRIPT_LICENSE}",
        f"{SPDX_LICENSE_HEADER}{APACHE}",
        1,
    )
    require_reports(
        license_map_errors(reuse, readme, lost_source_header, license_files),
        path,
        "wrong manuscript source header was accepted",
    )

    missing_license_text = license_files - {f"LICENSES/{MANUSCRIPT_LICENSE}.txt"}
    require_reports(
        license_map_errors(reuse, readme, sources, missing_license_text),
        f"missing for {MANUSCRIPT_LICENSE}",
        "missing manuscript license text was accepted",
    )

    weakened_readme = readme.replace(
        "Code, scripts, and documentation use Apache-2.0; manuscripts use "
        "CC-BY-4.0;",
        "Code and manuscripts follow the repository default;",
        1,
    )
    require_reports(
        license_map_errors(reuse, weakened_readme, sources, license_files),
        "licence boundary",
        "weakened README license boundary was accepted",
    )

    with tempfile.TemporaryDirectory(prefix="license-map-boundary-") as raw:
        fixture_root = Path(raw) / "checkout"
        fixture_root.mkdir()
        outside = Path(raw) / "private.txt"
        outside.write_text("private licensing evidence", encoding="utf-8")
        (fixture_root / "REUSE.toml").symlink_to(outside)
        try:
            safe_license_file(fixture_root, "REUSE.toml")
        except UnsafeLicenseInput:
            pass
        else:
            raise AssertionError("symlinked licensing input was accepted")

    private_tmp = Path("/private/tmp")
    temporary_root = str(private_tmp) if private_tmp.is_dir() else None
    with tempfile.TemporaryDirectory(
        prefix="license-map-race-", dir=temporary_root
    ) as raw:
        fixture_root = Path(raw)
        raced = fixture_root / "raced.txt"
        raced.write_text("placeholder\n", encoding="utf-8")
        original_open = os.open

        def replace_with_fifo(path: Path, flags: int, mode: int = 0o777) -> int:
            if Path(path) == raced:
                raced.unlink()
                os.mkfifo(raced)
            return original_open(path, flags, mode)

        with patch.object(os, "open", side_effect=replace_with_fifo):
            try:
                safe_license_text(fixture_root, "raced.txt")
            except UnsafeLicenseInput as error:
                require("regular file" in str(error), str(error))
            else:
                raise AssertionError(
                    "licensing reader opened a final path replaced by a FIFO"
                )

    print(
        "test_license_map_contract: Apache software and CC-BY manuscript "
        "sources/rendered artifacts remain separated; "
        "7 negative fixtures rejected"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
