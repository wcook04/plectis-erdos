#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Keep citation metadata bound to the registered public release identity."""

from __future__ import annotations

import json
import re
from pathlib import Path


ROOT = Path(__file__).resolve().parent.parent
MAIN_PAPER = "paper/archive/erdos249-257-main-paper.tex"
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
    """Return semantic citation/release identity failures."""
    errors: list[str] = []
    repository = str(release["repository"])
    tag = str(release["tag"])
    require_scalar(errors, cff, "cff-version", "1.2.0")
    require_scalar(errors, cff, "type", "software")
    require_scalar(
        errors,
        cff,
        "title",
        # CITATION.cff describes the tagged release, whose immutable historical
        # title is independent of the current README's corrected status wording.
        "Plectis: research on eight open Erdős problems",
    )
    require_scalar(errors, cff, "version", str(release["version"]))
    require_scalar(errors, cff, "date-released", str(release["date"]))
    require_scalar(errors, cff, "repository-code", repository)
    require_scalar(errors, cff, "url", repository)

    tag_url = f"{repository}/releases/tag/{tag}"
    if cff.count(f'value: "{tag_url}"') != 1:
        errors.append("CITATION.cff lost its unique exact tagged-release identifier")
    if cff.count(
        'description: "The tagged release this metadata describes"'
    ) != 1:
        errors.append("CITATION.cff lost the tagged-release identifier boundary")

    abstracts = top_level_values(cff, "abstract")
    if len(abstracts) != 1 or OPEN_BOUNDARY not in abstracts[0]:
        errors.append("CITATION.cff abstract lost the exact open-problem boundary")

    messages = top_level_values(cff, "message")
    if len(messages) != 1 or MAIN_PAPER not in messages[0]:
        errors.append("CITATION.cff lost the mathematical exposition citation route")
    return errors


def citation_attribution_errors(cff: str, registry: dict[str, object]) -> list[str]:
    """Check explicitly linked CFF references against the authored credit owner.

    This reads the repository's block-style CFF, not arbitrary YAML. Full CFF
    schema validation remains the separate cffconvert CI step. Unlinked older
    references remain selected bibliography entries, not verified comparisons.
    """
    sources = {row["id"]: row for row in registry["sources"]}
    errors: list[str] = []
    prefix = "https://github.com/wcook04/plectis-erdos/blob/main/docs/research-commons/SOURCE_ATTRIBUTIONS.md#source-"
    for block in re.split(r"(?m)^  - type: ", cff.split("\nreferences:\n", 1)[-1])[1:]:
        links = re.findall(re.escape(prefix) + r'([^"\s]+)', block)
        if not links:
            continue
        if len(links) != 1 or links[0] not in sources:
            errors.append("CFF reference has an unknown or duplicated source attribution")
            continue
        source = sources[links[0]]
        scalar = "\n".join(line[4:] for line in block.splitlines()[1:])
        if top_level_values(scalar, "title") != [source["title"]]:
            errors.append(f"{source['id']}: CFF title differs from source registry")
        # Deliberately preserve initials as recorded, rather than guessing names.
        authors = re.findall(
            r'      - family-names: "([^"\n]+)"\n        given-names: "([^"\n]+)"', block
        )
        if [f"{given} {family}" for family, given in authors] != source["authors"]:
            errors.append(f"{source['id']}: CFF authors differ from source registry")
        urls = top_level_values(scalar, "url")
        if len(urls) != 1 or urls[0] not in source["urls"]:
            errors.append(f"{source['id']}: CFF source version is absent from registry")
    for route in ("docs/PRIOR_ART.md", "docs/research-commons/SOURCE_ATTRIBUTIONS.md"):
        if route not in top_level_values(cff, "message")[0]:
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

    wrong_tag = cff.replace(str(release["tag"]), "v0.5.0", 1)
    require(
        any(
            "tagged-release identifier" in error
            for error in citation_identity_errors(wrong_tag, release)
        ),
        "wrong tag fixture was not rejected",
    )

    duplicated_version = cff.replace(
        f'version: "{release["version"]}"',
        f'version: "{release["version"]}"\nversion: "{release["version"]}"',
        1,
    )
    require(
        any(
            "top-level version" in error
            for error in citation_identity_errors(duplicated_version, release)
        ),
        "duplicated version fixture was not rejected",
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
        "repository, tag, paper route, and open boundary; "
        "11 identity and attribution negative fixtures rejected"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
