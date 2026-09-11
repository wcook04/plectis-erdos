#!/usr/bin/env python3
"""Acceptance checks for the public human-first documentation surface."""

from __future__ import annotations

import re
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
HUMAN_ENTRY = ROOT / "docs/READING_GUIDE.md"


def require(condition: bool, message: str) -> None:
    if not condition:
        raise AssertionError(message)


def words(text: str) -> list[str]:
    return re.findall(r"[A-Za-z0-9][A-Za-z0-9'’+#./−≥≤]*", text)


def prose_words(text: str) -> list[str]:
    """Count reader prose without charging the separately bounded code block."""

    return words(re.sub(r"```.*?```", "", text, flags=re.DOTALL))


def local_markdown_targets(path: Path) -> list[Path]:
    """Resolve clone-local Markdown links from the document that owns them."""

    targets: list[Path] = []
    for raw in re.findall(r"\[[^]]+\]\(([^)]+)\)", path.read_text(encoding="utf-8")):
        target = raw.split("#", 1)[0]
        if not target or "://" in target or target.startswith("mailto:"):
            continue
        targets.append((path.parent / target).resolve())
    return targets


def authored_prose_blocks(text: str) -> list[str]:
    """Return ordinary prose blocks, excluding metadata and navigation syntax."""
    blocks: list[str] = []
    for raw in re.split(r"\n\s*\n", text):
        lines = [
            line.strip()
            for line in raw.splitlines()
            if line.strip() and not line.lstrip().startswith("<!--")
        ]
        if not lines or lines[0].startswith("#"):
            continue
        if any(
            line.startswith(("- ", "* ", "+ ", "> ", "|"))
            or re.match(r"\d+[.)]\s", line)
            for line in lines
        ):
            continue
        blocks.append(" ".join(lines))
    return blocks


def main() -> None:
    readme = (ROOT / "README.md").read_text(encoding="utf-8")
    human_entry = HUMAN_ENTRY.read_text(encoding="utf-8")
    results = (ROOT / "docs/RESULTS.md").read_text(encoding="utf-8")
    docs_index = (ROOT / "docs/README.md").read_text(encoding="utf-8")

    reader_surfaces = (
        ROOT / "README.md",
        HUMAN_ENTRY,
        ROOT / "paper/README.md",
        ROOT / "docs/README.md",
        ROOT / "docs/RESULTS.md",
        ROOT / "docs/AGENT_WORKBENCH.md",
        *sorted((ROOT / "docs/papers/full-text").glob("*.md")),
    )
    for source in reader_surfaces:
        for target in local_markdown_targets(source):
            require(target.is_file() or target.is_dir(), f"{source.relative_to(ROOT)} has a dead local link: {target}")

    require(
        "../README.md#problem-papers" in results,
        "RESULTS does not route readers to the current README paper anchor",
    )

    # 2026-09-10: 1_400 -> 1_700 -> 2_000. The operator rewrote the front page in
    # his own voice (second pass the same day); the paper index carries
    # short/longer PDF links, one-line strongest results, and erdosproblems.com
    # URLs that this counter charges as words. The budget follows the authored
    # page, it does not reshape it. Funded with slack, not to the byte.
    require(
        len(prose_words(readme)) <= 2_000,
        "README prose exceeds the human front-door budget",
    )
    # 2026-09-10, operator-directed: the front page carries no command block at
    # all. Commands live in REPRODUCIBILITY and the agent workbench, which the
    # README must name; the routed-surface checks below keep them reachable.
    require("```" not in readme, "README carries a command block; commands belong in REPRODUCIBILITY and the agent workbench")
    require(
        "[REPRODUCIBILITY](docs/REPRODUCIBILITY.md)" in readme
        and "](docs/AGENT_WORKBENCH.md)" in readme,
        "README no longer routes readers to the documents that hold its commands",
    )
    require(
        "All eight problems remain open" in readme,
        "README does not state the global open boundary near the front",
    )
    require(
        "docs/claims.json" in readme,
        "README must route claim status to its canonical owner",
    )
    require(
        "Palomar" not in readme and "PALOMAR_RESULT_SHOWCASE.json" not in readme,
        "README must not advertise Palomar as part of this public edition",
    )
    require(
        "later models" not in readme,
        "README must not predict unreleased models",
    )
    require(
        "paper/archive/" not in readme,
        "README must lead with the current papers, not an archived manuscript",
    )
    require(
        "AGENTS.md" in readme and "docs/AGENT_WORKBENCH.md" in readme,
        "README must route agents to the separate workbench",
    )
    first_screen = readme.split("## Problem papers", 1)[0]
    require(
        "[A reader's way in](docs/READING_GUIDE.md)" in first_screen,
        "README does not lead human readers to the prose-first entry",
    )
    require(
        not re.search(r"(?m)^\|.+\|$", first_screen),
        "README first screen uses a routing table instead of prose",
    )
    require("```" not in first_screen and "git clone" not in first_screen,
        "README asks a cold reader to choose a checkout before showing the papers")
    require(
        "![Eight open problems:" in first_screen
        and "](.github/system-map.png)" in first_screen,
        "README opening lost the mathematical research-record banner",
    )
    for token in (
        "routes that stopped",
        "human judgement",
        "independent, AI-assisted prototype",
        "short paper",
        "evidence boundary",
    ):
        require(token in " ".join(first_screen.split()), f"README opening lost its project-purpose boundary: {token}")
    require(
        "query_semantic.py" not in readme and "--publication-architecture" not in readme,
        "README exposes machine drilldowns that belong in agent documentation",
    )

    human_words = words(human_entry)
    prose_blocks = authored_prose_blocks(human_entry)
    prose_word_count = sum(len(words(block)) for block in prose_blocks)
    require(
        450 <= len(human_words) <= 1_200,
        "HUMAN_ENTRY must be a substantial but bounded prose introduction",
    )
    require(
        len(prose_blocks) >= 10 and prose_word_count / len(human_words) >= 0.9,
        "HUMAN_ENTRY is not predominantly authored explanatory prose",
    )
    require(
        len(words(prose_blocks[0])) >= 35,
        "HUMAN_ENTRY does not explain the project before routing the reader",
    )
    require("All eight problems remain open" in human_entry, "human entry blurs the open boundary")
    require(
        "Comparator" in human_entry and "Palomar" in human_entry,
        "human entry does not explain the two public review surfaces",
    )
    require("AGENTS.md" not in human_entry, "human entry leaks the agent router")
    require("python3 " not in human_entry, "human entry exposes shell commands")
    require("scripts/" not in human_entry, "human entry exposes implementation paths")
    require("```" not in human_entry, "human entry contains a code block")
    require(
        not re.search(r"(?m)^\|.+\|$", human_entry),
        "human entry contains a machine-like routing table",
    )
    require(
        not re.search(r"(?<![A-Za-z])--[a-z][a-z0-9-]*", human_entry),
        "human entry exposes command-line flags",
    )
    require(
        not re.search(r"\b(?:route|claim|problem|statement|family)_id\b", human_entry),
        "human entry exposes machine-readable identifiers",
    )
    require(
        not re.search(
            r"(?i)(?:^|[\s(])(?:[\w.-]+/)+[\w.-]+|"
            r"\b[\w-]+\.(?:json|py|lean|toml|ya?ml)\b|::",
            re.sub(r"\]\([^)]*\)", "]", human_entry),
        ),
        "human entry exposes implementation coordinates instead of explaining them",
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
    for n in ("68", "243", "249", "251", "257", "269", "1041", "1049"):
        require(
            f"https://www.erdosproblems.com/{n}" in readme,
            f"README lost the Erdős Problems catalogue link for #{n}",
        )
    for label in ("[short paper]", "[longer paper]"):
        require(label in readme, f"README lost the {label} paper-index label")
    for slug in paper_slugs:
        require(f"{slug}.pdf" in readme, f"README omits the {slug} paper")
        stored = list((ROOT / "paper").rglob(f"{slug}.pdf"))
        require(len(stored) == 1 and stored[0].is_file(), f"missing PDF for {slug}")
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
        "## Read",
        "## Check",
        "## Contribute",
        "## Where things live",
    ):
        require(heading in docs_index, f"documentation guide omits {heading}")
    require(
        "Generated technical navigation" in docs_index,
        "documentation guide does not classify generated orientation correctly",
    )

    print("human-first-contact: PASS")


if __name__ == "__main__":
    main()
