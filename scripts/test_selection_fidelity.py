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

There is a third shape, and it is the one a locator check cannot settle: the
name resolves, the line is right, and the theorem underneath it now says
something else.  A hypothesis appears, a definition the statement depends on
is redefined, or the quantified domain narrows, and every name-shaped check
stays green while the reader is routed to a different theorem than the one the
claim describes.  Nothing here parses Lean.  The repository already carries
the statement evidence in two places, and this script binds to both:

* `docs/declaration_atlas.json` carries one row per declaration with `module`,
  `name`, `kind`, `line`, and the full `signature` text, under a
  `source_fingerprint` taken over the Lean sources themselves;
* `docs/semantic/reviews.json` receipts are digest-bound through
  `scripts/semantic_review.py`, whose material carries that fingerprint, and
  whose revision-move route refuses any receipt whose cited declaration has a
  different kind or signature on the two sides of the move.

So a statement change under an unchanged name moves the atlas signature and
the source fingerprint, and the existing digest path reports it.  The fixtures
below drive that path directly, with no git and no Lean.

Stdlib only, no Lean, no network, no git mutation.  Run from anywhere:

    python3 scripts/test_selection_fidelity.py
"""

from __future__ import annotations

import json
import sys
import tempfile
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

import semantic_review  # noqa: E402
import verify_claims  # noqa: E402
from lean_declaration_index import (  # noqa: E402
    declaration_keyword_line,
    resolve_within,
)

ROOT = Path(__file__).resolve().parent.parent
CLAIMS_PATH = ROOT / "docs" / "claims.json"
ATLAS_PATH = ROOT / "docs" / "declaration_atlas.json"
CATALOG_PATH = ROOT / "verification" / "palomar-entry-catalog.json"
PACKAGE_PREFIX = "ExternalVerification"
REQUIRED_PACKAGE_FILES = ("Challenge.lean", "Solution.lean")
ACCEPTED_LOCATOR_STATUS = frozenset({"exact", "in_window"})

# The atlas fields this script depends on, named so a schema change fails here
# rather than quietly turning the statement check into a no-op.
ATLAS_ROW_FIELDS = ("module", "name", "kind", "line", "signature")


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


# --- claim-row statements ----------------------------------------------------


def atlas_statement_index(atlas: dict) -> dict[tuple[str, str], dict]:
    """Index the declaration atlas by the coordinate a claim row names."""
    index: dict[tuple[str, str], dict] = {}
    for row in atlas.get("declarations", []):
        index[(str(row.get("module")), str(row.get("name")))] = row
    return index


def validate_atlas_statement_evidence(atlas: dict) -> list[str]:
    """The atlas must still be the statement evidence this script assumes."""
    errors: list[str] = []
    if not str(atlas.get("source_fingerprint", "")).startswith("sha256:"):
        errors.append(
            "declaration atlas carries no sha256 source fingerprint, so no "
            "receipt can be bound to the statements it records"
        )
    rows = atlas.get("declarations", [])
    if not rows:
        errors.append("declaration atlas records no declarations")
    return errors


def validate_claim_statements(
    claims: dict, index: dict[tuple[str, str], dict]
) -> list[str]:
    """Every cited declaration must carry a statement, not just a name.

    A locator check answers "is this name here".  This answers "does the
    repository hold the text of what it says", which is the thing a receipt
    can be bound to.  A claim citing a declaration with no atlas row, or with
    an empty signature, is a claim whose statement nothing pins.
    """
    errors: list[str] = []
    for claim in claims.get("claims", []):
        claim_id = claim.get("id", "<unnamed>")
        for declaration in claim.get("declarations", []) or []:
            module = str(declaration.get("module", ""))
            name = str(declaration.get("name", ""))
            row = index.get((module, name))
            if row is None:
                errors.append(
                    f"claim {claim_id}: {module}:{name} has no declaration "
                    "atlas row, so its statement is not recorded anywhere a "
                    "receipt can bind to"
                )
                continue
            missing = [field for field in ATLAS_ROW_FIELDS if field not in row]
            if missing:
                errors.append(
                    f"claim {claim_id}: atlas row for {module}:{name} lacks "
                    f"{', '.join(missing)}"
                )
                continue
            if not str(row.get("signature", "")).strip():
                errors.append(
                    f"claim {claim_id}: atlas row for {module}:{name} carries "
                    "an empty signature"
                )
                continue
            if name not in str(row["signature"]):
                errors.append(
                    f"claim {claim_id}: atlas signature for {module}:{name} "
                    "does not name the declaration it is recorded against"
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


# --- statement change under an unchanged name --------------------------------

_FIXTURE_MODULE = "ErdosProblems/Fixture/StatementDrift.lean"
_FIXTURE_DECLARATION = "tail_ratio_is_summable"
_FIXTURE_EVIDENCE_ID = f"{_FIXTURE_MODULE}:41:{_FIXTURE_DECLARATION}"
_FIXTURE_SIGNATURE = (
    f"theorem {_FIXTURE_DECLARATION} (A : Set Nat) : Summable (tailRatio A)"
)
# The same declaration after a hypothesis is added.  The name, the module, and
# the line are all unchanged; only the statement moved.
_FIXTURE_SIGNATURE_WITH_HYPOTHESIS = (
    f"theorem {_FIXTURE_DECLARATION} (A : Set Nat) (hA : A.Infinite) : "
    "Summable (tailRatio A)"
)
_FIXTURE_OLD_FINGERPRINT = "sha256:" + "a" * 64
_FIXTURE_NEW_FINGERPRINT = "sha256:" + "b" * 64
_FIXTURE_NEW_REVISION = "0" * 40


def _fixture_node(statement: str) -> dict:
    """One statement node citing one declaration, shaped like the live corpus."""
    return {
        "id": "Zfx::tail_ratio_summability",
        "canonical_statement": statement,
        "logical_class": "unconditional_progress",
        "problem": "257",
        "evidence": [
            {
                "id": _FIXTURE_EVIDENCE_ID,
                "kind": "theorem",
                "resolved": True,
                "module": _FIXTURE_MODULE,
                "declaration": _FIXTURE_DECLARATION,
            }
        ],
        "open_antecedents": [],
        "scope_caveat": "",
        "prior_art_state": "unassessed",
    }


def _fixture_registry(node: dict, *, fingerprint: str, revision: str) -> dict:
    """A receipt whose digest is issued by the live semantic-review code."""
    return {
        "schema": semantic_review.REGISTRY_SCHEMA,
        "reviews": [
            {
                "subject_kind": "statement_node",
                "subject_id": node["id"],
                "reviewer": "selection-fidelity fixture",
                "reviewer_type": "model",
                "reviewed_revision": revision,
                "reviewed_at": "2026-09-06",
                "review_scope": "fixture receipt for the statement-drift path",
                "claim_ceiling": "fixture only; no mathematical authority",
                "evidence_digest": semantic_review.subject_digest(
                    "statement_node",
                    node,
                    evidence_fingerprint=fingerprint,
                    reviewed_revision=revision,
                ),
            }
        ],
    }


def check_statement_drift_under_an_unchanged_name(claims: dict) -> int:
    """A statement change under the same name must reach the existing digest.

    Three routes, all of them already in `scripts/semantic_review.py`:

    1. the receipt digest covers the atlas source fingerprint, and that
       fingerprint is taken over the Lean sources, so restating a theorem
       makes every receipt over it stale;
    2. the revision-move route compares the kind and full signature of every
       cited declaration on both sides and refuses when they differ, which is
       the exact "same name, different theorem" case;
    3. restating the reviewed wording itself, with the sources unmoved, is
       stale for the same reason.

    Nothing here parses Lean and nothing runs git; the atlas signatures are
    passed in, which is the seam `rereview_moved_revision` already exposes.
    """
    checks = 0
    revision = str(
        claims.get("release", {}).get("formal_source", {}).get("ref", "")
    )
    require(
        len(revision) >= 7,
        "docs/claims.json must pin a formal-source revision for receipts to name",
    )
    require(
        revision != _FIXTURE_NEW_REVISION,
        "the fixture's moved revision must differ from the pinned revision",
    )
    checks += 1

    node = _fixture_node("The tail-ratio family is summable on every infinite support.")
    registry = _fixture_registry(
        node, fingerprint=_FIXTURE_OLD_FINGERPRINT, revision=revision
    )

    # Control: with the sources unmoved, the live validator accepts the receipt.
    errors = semantic_review.apply_review_registry(
        json.loads(json.dumps(registry)),
        {node["id"]: json.loads(json.dumps(node))},
        [],
        evidence_fingerprint=_FIXTURE_OLD_FINGERPRINT,
        reviewed_revision=revision,
    )
    require(not errors, f"the fixture receipt must validate unmoved: {errors}")
    checks += 1

    # Route 1: the Lean sources moved, so the fingerprint moved.  The name and
    # the wording are untouched and the receipt is still reported stale.
    errors = semantic_review.apply_review_registry(
        json.loads(json.dumps(registry)),
        {node["id"]: json.loads(json.dumps(node))},
        [],
        evidence_fingerprint=_FIXTURE_NEW_FINGERPRINT,
        reviewed_revision=revision,
    )
    require(
        any("digest is stale" in error for error in errors),
        "a moved source fingerprint escaped the semantic-review digest",
    )
    checks += 1

    old_corpus = {
        "evidence_fingerprint": _FIXTURE_OLD_FINGERPRINT,
        "statement_nodes": [json.loads(json.dumps(node))],
        "relations": [],
    }
    new_corpus = {
        "evidence_fingerprint": _FIXTURE_NEW_FINGERPRINT,
        "statement_nodes": [json.loads(json.dumps(node))],
        "relations": [],
    }
    unchanged = {
        (_FIXTURE_MODULE, _FIXTURE_DECLARATION): ("theorem", _FIXTURE_SIGNATURE)
    }
    restated = {
        (_FIXTURE_MODULE, _FIXTURE_DECLARATION): (
            "theorem",
            _FIXTURE_SIGNATURE_WITH_HYPOTHESIS,
        )
    }

    # Control for route 2: identical signatures on both sides re-issue cleanly.
    reissues, refusals = semantic_review.rereview_moved_revision(
        json.loads(json.dumps(registry)),
        old_corpus,
        new_corpus,
        new_revision=_FIXTURE_NEW_REVISION,
        today="2026-09-06",
        old_signatures=unchanged,
        new_signatures=unchanged,
    )
    require(
        len(reissues) == 1 and not refusals,
        f"an unchanged statement must re-issue across a revision move: {refusals}",
    )
    checks += 1

    # Route 2 proper: the added hypothesis is the disconfirming case.  The
    # declaration name, module, and line are all unchanged.
    reissues, refusals = semantic_review.rereview_moved_revision(
        json.loads(json.dumps(registry)),
        old_corpus,
        new_corpus,
        new_revision=_FIXTURE_NEW_REVISION,
        today="2026-09-06",
        old_signatures=unchanged,
        new_signatures=restated,
    )
    require(
        not reissues
        and any(
            "cited declaration statement differs" in refusal
            and f"{_FIXTURE_MODULE}:{_FIXTURE_DECLARATION}" in refusal
            for refusal in refusals
        ),
        "an added hypothesis under an unchanged declaration name escaped the "
        f"revision-move statement comparison: {refusals}",
    )
    checks += 1

    # A declaration the new atlas no longer records at all is the same class of
    # failure and must be refused rather than re-issued.
    reissues, refusals = semantic_review.rereview_moved_revision(
        json.loads(json.dumps(registry)),
        old_corpus,
        new_corpus,
        new_revision=_FIXTURE_NEW_REVISION,
        today="2026-09-06",
        old_signatures=unchanged,
        new_signatures={},
    )
    require(
        not reissues and refusals,
        "a cited declaration absent from the moved atlas escaped the comparison",
    )
    checks += 1
    return checks


def check_self_consistent_wrongness(claims_path: Path) -> int:
    """A claim restated away from its declaration must fail the digest path.

    The failure this encodes is a tree that is wrong and internally tidy: the
    reader-facing statement is edited, nothing is regenerated, and every
    name-shaped and count-shaped check still passes because the declaration is
    exactly where the row says it is.  The receipt is the only surface that
    notices, because its digest covers the wording it reviewed.

    The mutation happens in a temporary copy.  The live tree is read only.
    """
    checks = 0
    with tempfile.TemporaryDirectory() as raw:
        scratch = Path(raw)
        copied_claims = scratch / "claims.json"
        copied_claims.write_text(claims_path.read_text())
        claims = json.loads(copied_claims.read_text())
        revision = str(
            claims.get("release", {}).get("formal_source", {}).get("ref", "")
        )

        node = _fixture_node(
            "For every infinite support with summable reciprocal mass the "
            "tail-ratio family is summable."
        )
        registry = _fixture_registry(
            node, fingerprint=_FIXTURE_OLD_FINGERPRINT, revision=revision
        )
        (scratch / "semantic_corpus.json").write_text(
            json.dumps(
                {
                    "evidence_fingerprint": _FIXTURE_OLD_FINGERPRINT,
                    "statement_nodes": [node],
                    "relations": [],
                }
            )
        )
        (scratch / "reviews.json").write_text(json.dumps(registry))

        # Alter the statement only.  The cited declaration, its module, its
        # line, and the pinned revision are all untouched, and nothing is
        # regenerated: this is the self-consistent wrong tree.
        corpus = json.loads((scratch / "semantic_corpus.json").read_text())
        corpus["statement_nodes"][0]["canonical_statement"] = (
            "For every infinite support the tail-ratio family is summable."
        )
        (scratch / "semantic_corpus.json").write_text(json.dumps(corpus))

        altered = json.loads((scratch / "semantic_corpus.json").read_text())
        errors = semantic_review.apply_review_registry(
            json.loads((scratch / "reviews.json").read_text()),
            {row["id"]: row for row in altered["statement_nodes"]},
            [],
            evidence_fingerprint=str(altered["evidence_fingerprint"]),
            reviewed_revision=revision,
        )
        require(
            any(
                "digest is stale" in error and node["id"] in error
                for error in errors
            ),
            "a claim restated away from its reviewed wording escaped the "
            f"receipt digest: {errors}",
        )
        checks += 1

        # The same tree, unaltered, must pass; otherwise the check above proves
        # nothing about the alteration.
        errors = semantic_review.apply_review_registry(
            json.loads((scratch / "reviews.json").read_text()),
            {node["id"]: json.loads(json.dumps(node))},
            [],
            evidence_fingerprint=_FIXTURE_OLD_FINGERPRINT,
            reviewed_revision=revision,
        )
        require(not errors, f"the unaltered control must pass: {errors}")
        checks += 1
    return checks


def main() -> int:
    claims = json.loads(CLAIMS_PATH.read_text())
    atlas = json.loads(ATLAS_PATH.read_text())
    index = atlas_statement_index(atlas)
    claim_errors = validate_claim_declarations(claims)
    statement_errors = validate_atlas_statement_evidence(
        atlas
    ) + validate_claim_statements(claims, index)
    tree_errors, config_count, package_count = validate_tree(ROOT)
    fixture_checks = (
        check_fixtures()
        + check_claim_locator_mutations(claims)
        + check_statement_drift_under_an_unchanged_name(claims)
        + check_self_consistent_wrongness(CLAIMS_PATH)
    )

    errors = claim_errors + statement_errors + tree_errors
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
        f"{declaration_count} claim declarations resolve and carry a recorded "
        f"statement in {len(index)} atlas rows; "
        f"{config_count} comparator selections over {package_count} packages "
        "resolve to declared endpoints; "
        f"{fixture_checks} adversarial fixtures were rejected"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
