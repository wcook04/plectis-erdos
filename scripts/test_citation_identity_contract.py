#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Keep current citation metadata distinct from historical release identity."""

from __future__ import annotations

import json
import re
from pathlib import Path


ROOT = Path(__file__).resolve().parent.parent
MAIN_PAPER = "paper/archive/erdos249-257-main-paper.tex"
CURRENT_SOFTWARE_TITLE = "Plectis: research on eight Erdős problems"
OPEN_BOUNDARY = (
    "It does not solve Erdős #249 or the universal #257 problem."
)


def require(condition: bool, message: str) -> None:
    """Keep citation identity failures active when run with ``python -O``."""
    if not condition:
        raise AssertionError(message)


def top_level_values(cff: str, key: str) -> list[str]:
    pattern = re.compile(
        rf"^{re.escape(key)}:\s*(?:\"([^\"]*)\"|'([^']*)'|([^\n#]+?))\s*$",
        re.MULTILINE,
    )
    return [
        next(group for group in match.groups() if group is not None).strip()
        for match in pattern.finditer(cff)
    ]


def require_scalar(
    errors: list[str],
    cff: str,
    key: str,
    expected: str,
) -> None:
    values = top_level_values(cff, key)
    if values != [expected]:
        errors.append(
            f"CITATION.cff top-level {key} must occur once as {expected!r}"
        )


def citation_identity_errors(
    cff: str,
    release: dict[str, object],
) -> list[str]:
    """Return current-repository citation identity failures."""
    errors: list[str] = []
    repository = str(release["repository"])
    require_scalar(errors, cff, "cff-version", "1.2.0")
    require_scalar(errors, cff, "type", "software")
    require_scalar(
        errors,
        cff,
        "title",
        # The current software name is status-neutral. Historical tags retain
        # their own CFF bytes; main does not borrow their version or date.
        CURRENT_SOFTWARE_TITLE,
    )
    require_scalar(errors, cff, "repository-code", repository)
    require_scalar(errors, cff, "url", repository)
    # Main changes between releases. A current abstract must not inherit an
    # older tag's edition identity. Use the tagged file for historical work.
    for key in ("version", "date-released"):
        if re.search(rf"^{key}:", cff, re.MULTILINE):
            errors.append(f"CITATION.cff current metadata must omit top-level {key}")
    if re.search(r"^identifiers:", cff, re.MULTILINE):
        errors.append("CITATION.cff current metadata must not claim a release identifier")

    abstracts = top_level_values(cff, "abstract")
    if len(abstracts) != 1 or OPEN_BOUNDARY not in abstracts[0]:
        errors.append("CITATION.cff abstract lost the exact open-problem boundary")

    messages = top_level_values(cff, "message")
    if len(messages) != 1 or MAIN_PAPER not in messages[0]:
        errors.append("CITATION.cff lost the mathematical exposition citation route")
    return errors


def citation_attribution_errors(cff: str, registry: dict[str, object]) -> list[str]:
    """Require the exact registry and paper-edition reference projection.

    All sources require a citation, reviewed alias or explicit exclusion. Full
    CFF schema validation remains the separate cffconvert CI step; native
    bibliography-coordinate coverage is enforced by the attribution builder.
    """
    import citation_projection as projection
    errors = []
    corpus = json.loads((ROOT / "docs/papers/corpus.json").read_text())
    # Exact rendering checks every included source and every repository paper,
    # including deletion, unknown additions and wrong identity anchors.
    index = {"sources": registry["sources"], "paper_inventory": {
        "bibliography_entries": [], "unmatched_citation_keys": [], "unresolved_includes": []}}
    try:
        errors.extend(projection.errors(cff, index, corpus))
    except (ValueError, KeyError) as exc:
        errors.append(str(exc))
    messages = top_level_values(cff, "message")
    for route in ("docs/PRIOR_ART.md", "docs/research-commons/SOURCE_ATTRIBUTIONS.md"):
        if len(messages) != 1 or route not in messages[0]:
            errors.append(f"CFF message lost attribution route {route}")
    return errors


def main() -> int:
    claims = json.loads((ROOT / "docs" / "claims.json").read_text(encoding="utf-8"))
    release = claims["release"]
    cff = (ROOT / "CITATION.cff").read_text(encoding="utf-8")
    require((ROOT / MAIN_PAPER).is_file(), f"missing citation target: {MAIN_PAPER}")
    require(
        not citation_identity_errors(cff, release),
        "canonical CITATION.cff identity contract failed",
    )

    registry = json.loads((ROOT / "docs/research-commons/source-attributions.json").read_text())
    require(not citation_attribution_errors(cff, registry), "CFF/source-credit agreement failed")
    require(bool(citation_attribution_errors(cff.split("\nreferences:\n", 1)[0], registry)),
            "deleting all references escaped validation")
    blocks = re.split(r"(?m)^  - type: ", cff.split("\nreferences:\n", 1)[1])
    without_one = cff.split("\nreferences:\n", 1)[0] + "\nreferences:\n" + "".join("  - type: " + block for block in blocks[2:])
    require(bool(citation_attribution_errors(without_one, registry)), "deleting one reference escaped validation")
    # A valid YAML/CFF record can still misattribute a source or drift to another version.
    for old, replacement in (
        ('given-names: "Han"', 'given-names: "Wrong"'),
        ('title: "Sparse Polynomial-Weighted Expansions"', 'title: "Old title"'),
        ('url: "https://arxiv.org/abs/2606.24972v4"', 'url: "https://arxiv.org/abs/2606.24972v99"'),
        ('#source-source-f4ad17717c8fd4', '#source-unknown-source'),
        ('docs/PRIOR_ART.md and ', ''),
    ):
        require(old in cff, f"fixture target missing: {old}")
        require(bool(citation_attribution_errors(cff.replace(old, replacement, 1), registry)),
                f"attribution drift fixture was not rejected: {old}")

    for title in ("Plectis: research on eight open Erdős problems", "Unrelated software"):
        wrong_title = cff.replace(CURRENT_SOFTWARE_TITLE, title, 1)
        require(
            any("top-level title" in error
                for error in citation_identity_errors(wrong_title, release)),
            f"wrong current software title fixture was not rejected: {title}",
        )
    duplicate_title = cff.replace(
        f'title: "{CURRENT_SOFTWARE_TITLE}"',
        f'title: "{CURRENT_SOFTWARE_TITLE}"\ntitle: "{CURRENT_SOFTWARE_TITLE}"',
        1,
    )
    require(
        any("top-level title" in error
            for error in citation_identity_errors(duplicate_title, release)),
        "duplicated current software title fixture was not rejected",
    )

    wrong_repository = cff.replace(
        str(release["repository"]),
        "https://github.com/example/wrong-repository",
        1,
    )
    require(
        any(
            "repository-code" in error
            for error in citation_identity_errors(wrong_repository, release)
        ),
        "wrong repository fixture was not rejected",
    )

    for field, error_fragment in (
        (f'version: "{release["version"]}"', "top-level version"),
        (f'date-released: "{release["date"]}"', "top-level date-released"),
        ('identifiers:\n  - type: url\n    value: "' + str(release["repository"])
         + '/releases/tag/' + str(release["tag"]) + '"', "release identifier"),
    ):
        historical_identity = cff + "\n" + field + "\n"
        require(
            any(error_fragment in error
                for error in citation_identity_errors(historical_identity, release)),
            f"historical identity fixture was not rejected: {field}",
        )

    overstated_abstract = cff.replace(
        OPEN_BOUNDARY,
        "It solves Erdős #249 and the universal #257 problem.",
        1,
    )
    require(
        any(
            "open-problem boundary" in error
            for error in citation_identity_errors(overstated_abstract, release)
        ),
        "overstated abstract fixture was not rejected",
    )

    lost_paper_route = cff.replace(MAIN_PAPER, "paper/missing-paper.tex", 1)
    require(
        any(
            "exposition citation route" in error
            for error in citation_identity_errors(lost_paper_route, release)
        ),
        "lost paper route fixture was not rejected",
    )

    wrong_type = cff.replace("type: software", "type: dataset", 1)
    require(
        any(
            "top-level type" in error
            for error in citation_identity_errors(wrong_type, release)
        ),
        "wrong type fixture was not rejected",
    )

    print(
        "test_citation_identity_contract: citation metadata retains the exact "
        "repository, current-edition boundary, paper route, and open boundary; "
        "17 identity, attribution and deletion negative fixtures rejected"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
