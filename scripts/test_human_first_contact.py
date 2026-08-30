#!/usr/bin/env python3
"""Acceptance checks for the public human-first documentation surface."""

from __future__ import annotations

import re
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]


def require(condition: bool, message: str) -> None:
    if not condition:
        raise AssertionError(message)


def words(text: str) -> list[str]:
    return re.findall(r"[A-Za-z0-9][A-Za-z0-9'’+#./−≥≤]*", text)


def main() -> None:
    readme = (ROOT / "README.md").read_text(encoding="utf-8")
    results = (ROOT / "docs/RESULTS.md").read_text(encoding="utf-8")
    docs_index = (ROOT / "docs/README.md").read_text(encoding="utf-8")

    require(len(words(readme)) <= 1_400, "README exceeds the human front-door budget")
    require(readme.count("```") <= 2, "README contains more than one command block")
    require(
        "All eight problems remain open" in readme,
        "README does not state the global open boundary near the front",
    )
    require(
        "docs/PALOMAR_RESULT_SHOWCASE.json" in readme and "docs/claims.json" in readme,
        "README must defer ranking and claim status to their canonical owners",
    )
    require(
        "archive and provenance" in readme,
        "README does not label the combined manuscript as archive/provenance",
    )
    require(
        "AGENTS.override.md" in readme and "docs/AGENT_WORKBENCH.md" in readme,
        "README must route agents to the separate workbench",
    )
    require(
        "query_semantic.py" not in readme and "--publication-architecture" not in readme,
        "README exposes machine drilldowns that belong in agent documentation",
    )

    paper_slugs = (
        "erdos-68-factorial-denominator-irrationality",
        "erdos-243-reciprocal-tail-rigidity",
        "erdos-249-binary-totient-series",
        "erdos-251-prime-gap-dyadic-series",
        "erdos-257-mersenne-support-subseries",
        "erdos-269-three-prime-running-lcm",
        "erdos-1041-lemniscate-newton-flow",
        "erdos-1049-rational-base-lambert",
    )
    for slug in paper_slugs:
        require(f"{slug}.pdf" in readme, f"README omits the {slug} paper")
        require((ROOT / f"{slug}.pdf").is_file(), f"missing PDF for {slug}")
        require(
            (ROOT / f"docs/papers/full-text/{slug}.md").is_file(),
            f"missing Markdown paper for {slug}",
        )

    details_at = results.find("<details>")
    guide_at = results.find("### Problem-by-problem guide")
    require(guide_at >= 0 and details_at > guide_at, "RESULTS does not lead with the human guide")
    require("</details>" in results, "RESULTS technical inventory is not closed")
    require(
        "<!-- BEGIN semantic_public_census -->" in results
        and "<!-- END semantic_public_census -->" in results,
        "RESULTS lost the generated semantic census contract",
    )
    require(
        "PALOMAR_RESULT_SHOWCASE.json" in results and "claims.json" in results,
        "RESULTS does not defer ranking and status to canonical data",
    )

    for heading in (
        "## Read the mathematics",
        "## Verify a claim",
        "## Work on the repository",
        "## Archive and provenance",
    ):
        require(heading in docs_index, f"documentation guide omits {heading}")
    require(
        "technical navigation surfaces" in docs_index,
        "documentation guide does not classify generated orientation correctly",
    )

    print("human-first-contact: PASS")


if __name__ == "__main__":
    main()
