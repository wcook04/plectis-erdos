#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Selection fidelity: every published selection must name a real declaration.

Two audit waves found that a green comprehension gate coexisted with a poor
mathematical presentation.  Two of the four failure shapes are selection
failures rather than prose failures:

* a claim row can carry a declaration locator that no longer names the
  declaration on that line, so the reader is routed to the wrong theorem;
* a comparator package can select an endpoint name that is not declared in
  that package, or can be registered while its directory holds no challenge
  and no solution at all, so an empty directory passes as a package.

Neither shape is visible to a gate that only counts rows.  This script makes
both observable.  The mutation style follows
`test_cold_clone_comprehension.py`: validate the live tree, then prove the
validator rejects the adversarial fixtures that encode each failure.

Stdlib only, no Lean, no network, no git mutation.  Run from anywhere:

    python3 scripts/test_selection_fidelity.py
"""

from __future__ import annotations

import json
import sys
import tempfile
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

import verify_claims  # noqa: E402
from lean_declaration_index import (  # noqa: E402
    declaration_keyword_line,
    resolve_within,
)

ROOT = Path(__file__).resolve().parent.parent
CLAIMS_PATH = ROOT / "docs" / "claims.json"
CATALOG_PATH = ROOT / "verification" / "palomar-entry-catalog.json"
PACKAGE_PREFIX = "ExternalVerification"
REQUIRED_PACKAGE_FILES = ("Challenge.lean", "Solution.lean")
ACCEPTED_LOCATOR_STATUS = frozenset({"exact", "in_window"})


def require(condition: bool, message: str) -> None:
    """Keep assertions active when Python is run with -O."""
    if not condition:
        raise AssertionError(message)


# --- claim-row locators ------------------------------------------------------


def validate_claim_declarations(claims: dict) -> list[str]:
    """Every declaration on a claim row must sit where the row says it sits.

    `verify_claims.resolve_declaration` re-derives the true position, so a row
    whose status is neither `exact` nor `in_window` is a locator that has
    drifted away from the mathematics it advertises.
    """
    errors: list[str] = []
    for claim in claims.get("claims", []):
        claim_id = claim.get("id", "<unnamed>")
        for declaration in claim.get("declarations", []) or []:
            module = declaration.get("module", "")
            name = declaration.get("name", "")
            recorded = declaration.get("line")
            resolution = verify_claims.resolve_declaration(declaration)
            status = resolution["status"]
            if status not in ACCEPTED_LOCATOR_STATUS:
                errors.append(
                    f"claim {claim_id}: locator {module}:{recorded} does not "
                    f"name {name} ({status}; source says "
                    f"{resolution['resolved_line']})"
                )
                continue
            resolved = resolution["resolved_line"]
            if declaration_keyword_line(ROOT / module, name, resolved) is None:
                errors.append(
                    f"claim {claim_id}: {module}:{resolved} mentions {name} "
                    "but no declaration keyword introduces it there"
                )
    return errors


# --- comparator package selections -------------------------------------------


def package_directory(root: Path, config_path: Path, config: dict) -> Path:
    """Locate the package directory a comparator config describes."""
    challenge = config.get("challenge_module", "")
    package = challenge.split(".")[0] if challenge else config_path.parent.name
    sibling = config_path.parent
    if (sibling / "Challenge.lean").is_file() or sibling.name == package:
        return sibling
    return root / package


def validate_package_directory(root: Path, package: Path) -> list[str]:
    """A registered package must be a real, non-empty package directory."""
    relative = _relative(root, package)
    if not package.is_dir():
        return [f"package directory does not exist: {relative}"]
    contents = sorted(child.name for child in package.iterdir())
    if not contents:
        return [f"package directory is empty: {relative}"]
    errors = [
        f"package directory {relative} has no {required}"
        for required in REQUIRED_PACKAGE_FILES
        if required not in contents
    ]
    return errors


def validate_selected_theorems(
    root: Path, package: Path, config: dict, *, label: str
) -> list[str]:
    """Every selected endpoint must be declared in this package or its imports."""
    seeds = [package / name for name in REQUIRED_PACKAGE_FILES]
    errors: list[str] = []
    names = config.get("theorem_names") or []
    if not names:
        errors.append(f"{label}: selects no theorem names")
    for name in names:
        if resolve_within(root, seeds, name) is None:
            errors.append(
                f"{label}: selected endpoint {name} is not declared in "
                f"{_relative(root, package)}/Challenge.lean, Solution.lean, or "
                "any module they import inside this tree"
            )
    return errors


def validate_package_config(
    root: Path, config_path: Path, config: dict
) -> list[str]:
    """Validate one comparator selection end to end."""
    package = package_directory(root, config_path, config)
    label = f"config {_relative(root, config_path)}"
    errors = validate_package_directory(root, package)
    if errors:
        return errors
    if not (package / "comparator.json").is_file() and not config_path.is_file():
        errors.append(f"{label}: no comparator configuration on disk")
    return errors + validate_selected_theorems(root, package, config, label=label)


def _relative(root: Path, path: Path) -> str:
    try:
        return path.relative_to(root).as_posix()
    except ValueError:
        return path.as_posix()


def collect_configs(root: Path) -> list[tuple[Path, dict]]:
    """Every comparator selection this tree publishes.

    Two authorities carry selections in this release candidate: the package's
    own `comparator.json`, and the entries the Palomar catalog generates under
    `verification/palomar-entries/`.  Reading only one of them was how empty
    or unresolved packages stayed invisible.
    """
    configs: list[tuple[Path, dict]] = []
    seen: set[Path] = set()
    for config_path in sorted(root.rglob("comparator.json")):
        try:
            config = json.loads(config_path.read_text())
        except (OSError, json.JSONDecodeError):
            continue
        if "theorem_names" not in config:
            continue
        configs.append((config_path, config))
        seen.add(config_path)
    catalog_path = root / "verification" / "palomar-entry-catalog.json"
    if catalog_path.is_file():
        catalog = json.loads(catalog_path.read_text())
        for entry in catalog.get("entries", []):
            config_path = root / entry.get("config_path", "")
            if config_path in seen:
                continue
            seen.add(config_path)
            configs.append((config_path, entry))
    return configs


def validate_tree(root: Path) -> tuple[list[str], int, int]:
    """Validate every comparator selection and every unregistered package."""
    errors: list[str] = []
    configs = collect_configs(root)
    covered: set[Path] = set()
    for config_path, config in configs:
        package = package_directory(root, config_path, config)
        covered.add(package.resolve())
        errors.extend(validate_package_config(root, config_path, config))
    packages = 0
    for child in sorted(root.iterdir()):
        if not child.is_dir() or not child.name.startswith(PACKAGE_PREFIX):
            continue
        packages += 1
        if child.resolve() in covered:
            continue
        errors.extend(validate_package_directory(root, child))
    return errors, len(configs), packages


# --- adversarial fixtures ----------------------------------------------------

_CHALLENGE = """import Mathlib

namespace Erdos249257.ExternalVerificationFixture

theorem strong_endpoint (n : Nat) : n = n := by
  sorry

end Erdos249257.ExternalVerificationFixture
"""

_SOLUTION = """import Mathlib

namespace Erdos249257.ExternalVerificationFixture

theorem strong_endpoint (n : Nat) : n = n := by
  rfl

end Erdos249257.ExternalVerificationFixture
"""

_UNIMPORTED_WEAKER = """namespace Erdos249257.Elsewhere

theorem weaker_endpoint (n : Nat) : n = n ∨ True := by
  right
  trivial

end Erdos249257.Elsewhere
"""


def build_fixture_tree(root: Path) -> Path:
    """A minimal well-formed package plus an unimported weaker declaration."""
    package = root / "ExternalVerificationFixture"
    package.mkdir(parents=True)
    (package / "Challenge.lean").write_text(_CHALLENGE)
    (package / "Solution.lean").write_text(_SOLUTION)
    elsewhere = root / "Elsewhere"
    elsewhere.mkdir(parents=True)
    (elsewhere / "Weaker.lean").write_text(_UNIMPORTED_WEAKER)
    config = {
        "challenge_module": "ExternalVerificationFixture.Challenge",
        "solution_module": "ExternalVerificationFixture.Solution",
        "theorem_names": [
            "Erdos249257.ExternalVerificationFixture.strong_endpoint"
        ],
    }
    (package / "comparator.json").write_text(json.dumps(config, indent=2))
    return package


def check_fixtures() -> int:
    """Prove the validator rejects the two failure shapes the audits found."""
    checks = 0
    with tempfile.TemporaryDirectory() as raw:
        root = Path(raw)
        package = build_fixture_tree(root)
        config_path = package / "comparator.json"
        config = json.loads(config_path.read_text())

        baseline = validate_package_config(root, config_path, config)
        require(
            not baseline,
            f"selection-fidelity fixture baseline must pass: {baseline}",
        )
        checks += 1

        # Endpoint swap: the weaker declaration is real and lives in this
        # tree, but the package neither declares nor imports it.  A checker
        # that only asks "does this name exist somewhere" accepts the swap.
        swapped = dict(config)
        swapped["theorem_names"] = [
            "Erdos249257.Elsewhere.weaker_endpoint"
        ]
        errors = validate_package_config(root, config_path, swapped)
        require(
            any("selected endpoint" in error for error in errors),
            "weaker-endpoint swap escaped selection fidelity",
        )
        checks += 1

        # The same swap must still be rejected when the weaker declaration is
        # named with the package's own namespace, which is how a mis-selected
        # endpoint actually reaches a catalog entry.
        disguised = dict(config)
        disguised["theorem_names"] = [
            "Erdos249257.ExternalVerificationFixture.weaker_endpoint"
        ]
        errors = validate_package_config(root, config_path, disguised)
        require(
            any("selected endpoint" in error for error in errors),
            "disguised weaker-endpoint swap escaped selection fidelity",
        )
        checks += 1

        empty = root / "ExternalVerificationEmpty"
        empty.mkdir()
        errors = validate_package_directory(root, empty)
        require(
            any("is empty" in error for error in errors),
            "empty package directory escaped selection fidelity",
        )
        checks += 1

        stub = root / "ExternalVerificationStub"
        stub.mkdir()
        (stub / "README.md").write_text("package pending\n")
        errors = validate_package_directory(root, stub)
        require(
            any("has no Challenge.lean" in error for error in errors)
            and any("has no Solution.lean" in error for error in errors),
            "challenge-free stub package escaped selection fidelity",
        )
        checks += 1

        registered_empty = dict(config)
        registered_empty["challenge_module"] = (
            "ExternalVerificationEmpty.Challenge"
        )
        errors = validate_package_config(
            root, root / "verification" / "absent.json", registered_empty
        )
        require(
            any("is empty" in error for error in errors),
            "registered empty package escaped selection fidelity",
        )
        checks += 1

    return checks


def check_claim_locator_mutations(claims: dict) -> int:
    """A claim locator moved off its declaration must be reported as drift."""
    checks = 0
    live = next(
        (claim, declaration)
        for claim in claims.get("claims", [])
        for declaration in (claim.get("declarations") or [])
    )
    claim, declaration = live

    moved = dict(declaration)
    moved["line"] = (declaration.get("line") or 1) + 500
    errors = validate_claim_declarations(
        {"claims": [{"id": "fixture_moved_locator", "declarations": [moved]}]}
    )
    require(bool(errors), "moved claim locator escaped selection fidelity")
    checks += 1

    renamed = dict(declaration)
    renamed["name"] = declaration.get("name", "") + "_not_a_declaration"
    errors = validate_claim_declarations(
        {"claims": [{"id": "fixture_renamed_locator", "declarations": [renamed]}]}
    )
    require(bool(errors), "renamed claim locator escaped selection fidelity")
    checks += 1

    absent = dict(declaration)
    absent["module"] = "ErdosProblems/NoSuchModule.lean"
    errors = validate_claim_declarations(
        {"claims": [{"id": "fixture_absent_module", "declarations": [absent]}]}
    )
    require(bool(errors), "absent claim module escaped selection fidelity")
    checks += 1
    require(claim.get("id") is not None, "fixture claim must carry an id")
    return checks


def main() -> int:
    claims = json.loads(CLAIMS_PATH.read_text())
    claim_errors = validate_claim_declarations(claims)
    tree_errors, config_count, package_count = validate_tree(ROOT)
    fixture_checks = check_fixtures() + check_claim_locator_mutations(claims)

    errors = claim_errors + tree_errors
    declaration_count = sum(
        len(claim.get("declarations") or []) for claim in claims.get("claims", [])
    )
    if errors:
        print(f"test_selection_fidelity: {len(errors)} selection failure(s)")
        for error in errors:
            print(f"  FAIL {error}")
        return 1
    print(
        "test_selection_fidelity: "
        f"{declaration_count} claim declarations resolve; "
        f"{config_count} comparator selections over {package_count} packages "
        "resolve to declared endpoints; "
        f"{fixture_checks} adversarial fixtures were rejected"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
