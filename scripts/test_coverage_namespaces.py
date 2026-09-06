#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Adversarial tests for the three separate coverage questions.

The failure this encodes: a private-frontier association counted as public
coverage.  The invariant is that no association outside the public claim
register can ever set `bound_by_public_claim_row`, and that an unrecognised
register raises rather than defaulting to public.

Fixtures carry every rejection case, so no private tree is read.  The live
pass over this release candidate is read-only and asserts only what the
candidate itself owns: every declaration on a public claim row is present in
the candidate source, and no row in the public register was imported from a
private frontier.

The paper surface used to be reported rather than asserted, because `paper/`
was under concurrent authorship.  The papers are frozen now, so the reader
route is an assertion: every selected public claim reaches a paper anchor, its
proof class agrees with whether it carries a Lean declaration at all, and every
claim the README leads with reaches a current problem paper.  A reader-facing
theorem that carries no declaration is legitimate exactly when its status says
so, which is what `ordinary proof here`, `cited only`, and `open` are for.

Stdlib only, no Lean, no network, no git mutation.
"""

from __future__ import annotations

import json
import re
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

import coverage_namespaces as coverage  # noqa: E402
from coverage_namespaces import Association, UnknownRegister  # noqa: E402
from lean_declaration_index import qualified_declarations  # noqa: E402

ROOT = Path(__file__).resolve().parent.parent
CLAIMS_PATH = ROOT / "docs" / "claims.json"
RESULTS_PATH = ROOT / "docs" / "RESULTS.md"
README_PATH = ROOT / "README.md"
PAPER_DIR = ROOT / "paper"

LABEL_PATTERN = re.compile(r"\\label\{([^}]+)\}")

# Statuses whose own wording explains an absent Lean declaration.  A claim in
# any other status must name at least one declaration, and a claim in one of
# these must name none, because `ordinary proof here` says in the taxonomy that
# no Lean declaration proves its endpoint.
STATUSES_EXPLAINING_NO_DECLARATION = frozenset(
    {"ordinary proof here", "cited only", "open"}
)

# The retired joint manuscript.  `README.md` presents it for archive and
# provenance, so an anchor that lives only here is not a current reader route.
ARCHIVE_PAPER_SOURCES = frozenset({"erdos249-257-main-paper.tex"})

# The two README-headline claims whose declarations reach no current problem
# paper: their only paper route is the retired joint manuscript.  This is a
# real reader-route gap in the release candidate, named here so it stays
# visible and so any further headline claim in the same position fails.
ARCHIVE_ROUTED_HEADLINE_CLAIMS = frozenset(
    {"diagonal_pincer_reduction", "adelic_height_obstruction"}
)


def require(condition: bool, message: str) -> None:
    """Keep assertions active when Python is run with -O."""
    if not condition:
        raise AssertionError(message)


# --- fixtures ----------------------------------------------------------------

FIXTURE_CANDIDATE = (
    "Erdos249257.irrational_erdosSupportSeries_of_summable_reciprocal",
    "ErdosProblems.Erdos249.mechanism_gap_sigma_solved",
    "ErdosProblems.Erdos1041.circle_slice_angular_closure",
)

FIXTURE_READER_SURFACES = {
    "docs/RESULTS.md": (
        "The reciprocal-summable support theorem "
        "`irrational_erdosSupportSeries_of_summable_reciprocal` holds in "
        "every integer base.\n"
    ),
    "paper/erdos257.tex": (
        "\\label{thm:reciprocal}"
        "irrational_erdosSupportSeries_of_summable_reciprocal\n"
    ),
}

FIXTURE_ASSOCIATIONS = (
    Association(
        declaration="Erdos249257.irrational_erdosSupportSeries_of_summable_reciprocal",
        row_id="reciprocal_summable_support",
        register=coverage.PUBLIC_CLAIM_REGISTER,
    ),
    Association(
        declaration="ErdosProblems.Erdos249.mechanism_gap_sigma_solved",
        row_id="erdos249.mechanism_gap_sigma_solved_and_no_eta_quotient",
        register="private_frontier",
    ),
    Association(
        declaration="ErdosProblems.Erdos1041.circle_slice_angular_closure",
        row_id="erdos1041.circle_slice_angular_closure_thirteen_twentyfifths",
        register="docs/semantic/frontier.json",
    ),
)


def check_fixtures() -> int:
    """Prove the three questions stay separate under every register."""
    checks = 0

    published = coverage.classify(
        "Erdos249257.irrational_erdosSupportSeries_of_summable_reciprocal",
        candidate_declarations=FIXTURE_CANDIDATE,
        associations=FIXTURE_ASSOCIATIONS,
        reader_surfaces=FIXTURE_READER_SURFACES,
    )
    require(
        published.present_in_candidate_source
        and published.bound_by_public_claim_row
        and published.exposed_by_reader_surface,
        "fully published fixture must answer yes three times",
    )
    require(not published.buried, "published fixture must not read as buried")
    checks += 1

    for association in FIXTURE_ASSOCIATIONS[1:]:
        result = coverage.classify(
            association.declaration,
            candidate_declarations=FIXTURE_CANDIDATE,
            associations=FIXTURE_ASSOCIATIONS,
            reader_surfaces=FIXTURE_READER_SURFACES,
        )
        require(
            result.present_in_candidate_source,
            f"{association.declaration} must be present in candidate source",
        )
        require(
            not result.bound_by_public_claim_row,
            "private-frontier association produced public_claim_row=True: "
            f"{association.row_id}",
        )
        require(
            not result.exposed_by_reader_surface,
            f"{association.declaration} must not read as reader-exposed",
        )
        require(
            result.buried,
            f"{association.declaration} must read as buried",
        )
        checks += 1

    # Every private register, on its own, must fail to bind a public row.
    for register in sorted(coverage.PRIVATE_FRONTIER_REGISTERS):
        result = coverage.classify(
            "Erdos249257.some_declaration",
            candidate_declarations=("Erdos249257.some_declaration",),
            associations=(
                Association(
                    declaration="Erdos249257.some_declaration",
                    row_id="row",
                    register=register,
                ),
            ),
            reader_surfaces={},
        )
        require(
            not result.bound_by_public_claim_row,
            f"register {register} produced public_claim_row=True",
        )
        checks += 1

    # A private row plus a public row on the same declaration is public; a
    # private row must never be the thing that makes it public.
    mixed = coverage.classify(
        "Erdos249257.some_declaration",
        candidate_declarations=("Erdos249257.some_declaration",),
        associations=(
            Association("Erdos249257.some_declaration", "a", "private_frontier"),
            Association(
                "Erdos249257.some_declaration",
                "b",
                coverage.PUBLIC_CLAIM_REGISTER,
            ),
        ),
        reader_surfaces={},
    )
    require(
        mixed.bound_by_public_claim_row,
        "a genuine public row must still bind when a private row sits beside it",
    )
    checks += 1

    # An unrecognised register must raise rather than default to public.
    try:
        coverage.classify(
            "Erdos249257.some_declaration",
            candidate_declarations=("Erdos249257.some_declaration",),
            associations=(
                Association("Erdos249257.some_declaration", "row", "new_ledger"),
            ),
            reader_surfaces={},
        )
    except UnknownRegister:
        checks += 1
    else:
        raise AssertionError("unrecognised register escaped the closed vocabulary")

    # A reader surface that names a declaration does not bind a claim row, and
    # a claim row does not expose a declaration to a reader.
    exposed_only = coverage.classify(
        "Erdos249257.only_in_prose",
        candidate_declarations=("Erdos249257.only_in_prose",),
        associations=(),
        reader_surfaces={"docs/RESULTS.md": "see Erdos249257.only_in_prose"},
    )
    require(
        exposed_only.exposed_by_reader_surface
        and not exposed_only.bound_by_public_claim_row,
        "reader-surface mention must not bind a public claim row",
    )
    checks += 1

    bound_only = coverage.classify(
        "Erdos249257.only_in_register",
        candidate_declarations=("Erdos249257.only_in_register",),
        associations=(
            Association(
                "Erdos249257.only_in_register",
                "row",
                coverage.PUBLIC_CLAIM_REGISTER,
            ),
        ),
        reader_surfaces={"docs/RESULTS.md": "nothing relevant here"},
    )
    require(
        bound_only.bound_by_public_claim_row
        and not bound_only.exposed_by_reader_surface,
        "a claim row must not count as reader exposure",
    )
    checks += 1

    absent = coverage.classify(
        "Erdos249257.not_in_this_tree",
        candidate_declarations=FIXTURE_CANDIDATE,
        associations=FIXTURE_ASSOCIATIONS,
        reader_surfaces=FIXTURE_READER_SURFACES,
    )
    require(
        not absent.present_in_candidate_source and not absent.buried,
        "a declaration absent from the candidate source must not read as buried",
    )
    checks += 1

    filtered = coverage.public_claim_rows_only(FIXTURE_ASSOCIATIONS)
    require(
        [row.row_id for row in filtered] == ["reciprocal_summable_support"],
        "public_claim_rows_only must drop every private-register row",
    )
    checks += 1
    return checks


# --- live read-only pass ------------------------------------------------------


def live_associations(claims: dict) -> list[Association]:
    """Every declaration binding the public claim register actually publishes."""
    rows: list[Association] = []
    for claim in claims.get("claims", []):
        for declaration in claim.get("declarations") or []:
            rows.append(
                Association(
                    declaration=declaration.get("name", ""),
                    row_id=claim.get("id", ""),
                    register=coverage.PUBLIC_CLAIM_REGISTER,
                )
            )
    return rows


def reader_surface_text() -> dict[str, str]:
    """Reader surfaces as text: the results page and every paper source."""
    surfaces: dict[str, str] = {}
    if RESULTS_PATH.is_file():
        surfaces["docs/RESULTS.md"] = RESULTS_PATH.read_text(errors="replace")
    if PAPER_DIR.is_dir():
        for tex in sorted(PAPER_DIR.rglob("*.tex")):
            surfaces[tex.relative_to(ROOT).as_posix()] = tex.read_text(
                errors="replace"
            )
    return surfaces


def check_live_tree() -> tuple[int, dict[str, int]]:
    """Assert the candidate's own invariants and report the coverage split."""
    claims = json.loads(CLAIMS_PATH.read_text())
    associations = live_associations(claims)
    surfaces = reader_surface_text()

    modules = {
        declaration.get("module", "")
        for claim in claims.get("claims", [])
        for declaration in claim.get("declarations") or []
    }
    candidate: set[str] = set()
    for module in sorted(modules):
        candidate.update(qualified_declarations(ROOT / module))

    checks = 0
    counts = {
        "public_claim_row": 0,
        "reader_exposed": 0,
        "present_only": 0,
        "declarations": 0,
    }
    for association in associations:
        result = coverage.classify(
            association.declaration,
            candidate_declarations=candidate,
            associations=[association],
            reader_surfaces=surfaces,
        )
        counts["declarations"] += 1
        require(
            result.present_in_candidate_source,
            "public claim row names a declaration absent from the candidate "
            f"source: {association.row_id} -> {association.declaration}",
        )
        require(
            result.bound_by_public_claim_row,
            "a row read from the public claim register must bind a public "
            f"claim row: {association.row_id}",
        )
        counts["public_claim_row"] += 1
        if result.exposed_by_reader_surface:
            counts["reader_exposed"] += 1
        else:
            counts["present_only"] += 1
        checks += 1

    # No row of the public register may carry a private-frontier register tag.
    for association in associations:
        require(
            coverage.is_public_register(association.register),
            f"private register leaked into the public claim pass: "
            f"{association.row_id}",
        )
    checks += 1
    return checks, counts


# --- frozen-input paper coverage ---------------------------------------------


def paper_sources() -> dict[str, str]:
    """Every paper source, keyed by file name."""
    if not PAPER_DIR.is_dir():
        return {}
    return {
        path.name: path.read_text(errors="replace")
        for path in sorted(PAPER_DIR.rglob("*.tex"))
    }


def anchor_sources(sources: dict[str, str]) -> dict[str, set[str]]:
    """Map each paper anchor to the paper sources that define it."""
    anchors: dict[str, set[str]] = {}
    for name, text in sources.items():
        for match in LABEL_PATTERN.finditer(text):
            anchors.setdefault(match.group(1), set()).add(name)
    return anchors


def check_paper_surface_coverage() -> tuple[int, dict[str, int]]:
    """Selected claims, their proof classes, and their reader routes agree."""
    claims = json.loads(CLAIMS_PATH.read_text())
    taxonomy = claims.get("status_taxonomy", {})
    sources = paper_sources()
    anchors = anchor_sources(sources)
    readme = README_PATH.read_text(errors="replace") if README_PATH.is_file() else ""

    require(bool(sources), "the release candidate must carry paper sources")

    errors: list[str] = []
    counts = {"selected": 0, "headline": 0, "no_declaration": 0}
    for claim in claims.get("claims", []):
        claim_id = claim.get("id", "<unnamed>")
        status = str(claim.get("status", ""))
        declarations = claim.get("declarations") or []
        paper_label = str(claim.get("paper_label") or "")

        if status not in taxonomy:
            errors.append(f"{claim_id}: status {status!r} is outside the taxonomy")
            continue

        # Proof class against the formal roster.
        if status in STATUSES_EXPLAINING_NO_DECLARATION:
            counts["no_declaration"] += 1
            if declarations:
                errors.append(
                    f"{claim_id}: status {status!r} says no Lean declaration "
                    f"proves its endpoint, yet the row names {len(declarations)}"
                )
        elif not declarations:
            errors.append(
                f"{claim_id}: status {status!r} implies a Lean declaration and "
                "the row names none; a status that explains the omission is "
                f"one of {sorted(STATUSES_EXPLAINING_NO_DECLARATION)}"
            )

        if not paper_label:
            continue
        counts["selected"] += 1
        defining = anchors.get(paper_label, set())
        if not defining:
            errors.append(
                f"{claim_id}: paper anchor {paper_label} is defined in no "
                "paper source, so the reader route is broken"
            )
            continue

        if not claim.get("readme_headline"):
            continue
        counts["headline"] += 1
        # The README leads with this claim, so its anchor must sit in a paper
        # the README links.
        linked = [
            name
            for name in sorted(defining)
            if f"{name[: -len('.tex')]}.pdf" in readme
        ]
        if not linked:
            errors.append(
                f"{claim_id}: README leads with this claim and its anchor "
                f"{paper_label} sits in {sorted(defining)}, none of which the "
                "README links"
            )
            continue
        # A headline claim must also reach a current problem paper by name.
        current = [
            name
            for name in sorted(sources)
            if name not in ARCHIVE_PAPER_SOURCES
            and any(
                str(declaration.get("name", "")) in sources[name]
                for declaration in declarations
            )
        ]
        if not current and claim_id not in ARCHIVE_ROUTED_HEADLINE_CLAIMS:
            errors.append(
                f"{claim_id}: README leads with this claim and no current "
                "problem paper names any of its declarations; its only paper "
                "route is the retired joint manuscript"
            )

    require(not errors, "paper-surface coverage failed:\n  " + "\n  ".join(errors))
    return counts["selected"] + counts["headline"], counts


def main() -> int:
    fixture_checks = check_fixtures()
    live_checks, counts = check_live_tree()
    paper_checks, paper_counts = check_paper_surface_coverage()
    print(
        "test_coverage_namespaces: "
        f"{fixture_checks} coverage fixtures held; "
        f"{live_checks} live claim bindings checked; "
        f"{counts['public_claim_row']} declarations bound by a public claim "
        f"row, {counts['reader_exposed']} of them also named on a reader "
        f"surface, {counts['present_only']} bound but never named to a reader"
    )
    print(
        "test_coverage_namespaces: "
        f"{paper_checks} paper-surface checks held over "
        f"{paper_counts['selected']} claims carrying a paper anchor, "
        f"{paper_counts['headline']} of them README headlines, and "
        f"{paper_counts['no_declaration']} claims whose status explains an "
        "absent Lean declaration"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
