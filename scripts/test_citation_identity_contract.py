#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Keep citation metadata bound to the registered public release identity."""

from __future__ import annotations

import json
import re
from pathlib import Path


ROOT = Path(__file__).resolve().parent.parent
MAIN_PAPER = "paper/erdos249-257-main-paper.tex"
OPEN_BOUNDARY = (
    "It does not solve Erdős #249 or the universal #257 problem."
)


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
        "Erdős #249/#257 Lean formalisation (eight-problem corpus)",
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


def main() -> int:
    claims = json.loads((ROOT / "docs" / "claims.json").read_text(encoding="utf-8"))
    release = claims["release"]
    cff = (ROOT / "CITATION.cff").read_text(encoding="utf-8")
    assert (ROOT / MAIN_PAPER).is_file()
    assert not citation_identity_errors(cff, release)

    wrong_repository = cff.replace(
        str(release["repository"]),
        "https://github.com/example/wrong-repository",
        1,
    )
    assert any(
        "repository-code" in error
        for error in citation_identity_errors(wrong_repository, release)
    )

    wrong_tag = cff.replace(str(release["tag"]), "v0.5.0", 1)
    assert any(
        "tagged-release identifier" in error
        for error in citation_identity_errors(wrong_tag, release)
    )

    duplicated_version = cff.replace(
        f'version: "{release["version"]}"',
        f'version: "{release["version"]}"\nversion: "{release["version"]}"',
        1,
    )
    assert any(
        "top-level version" in error
        for error in citation_identity_errors(duplicated_version, release)
    )

    overstated_abstract = cff.replace(
        OPEN_BOUNDARY,
        "It solves Erdős #249 and the universal #257 problem.",
        1,
    )
    assert any(
        "open-problem boundary" in error
        for error in citation_identity_errors(overstated_abstract, release)
    )

    lost_paper_route = cff.replace(MAIN_PAPER, "paper/missing-paper.tex", 1)
    assert any(
        "exposition citation route" in error
        for error in citation_identity_errors(lost_paper_route, release)
    )

    wrong_type = cff.replace("type: software", "type: dataset", 1)
    assert any(
        "top-level type" in error
        for error in citation_identity_errors(wrong_type, release)
    )

    print(
        "test_citation_identity_contract: citation metadata retains the exact "
        "repository, tag, paper route, and open boundary; "
        "6 negative fixtures rejected"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
