#!/usr/bin/env python3
"""Acceptance checks for the public human-first documentation surface."""

from __future__ import annotations

import _test_bootstrap  # noqa: F401

import json
import re
import subprocess
import tempfile
from pathlib import Path

from validation_singleflight import command_environment, GIT_COMMAND_TIMEOUT_SECONDS


ROOT = Path(__file__).resolve().parents[2]
HUMAN_ENTRY = ROOT / "docs/README.md"


def require(condition: bool, message: str) -> None:
    if not condition:
        raise AssertionError(message)


def words(text: str) -> list[str]:
    return re.findall(r"[A-Za-z0-9][A-Za-z0-9'’+#./−≥≤]*", text)


def prose_words(text: str) -> list[str]:
    """Count reader prose without charging the separately bounded code block."""

    return words(re.sub(r"```.*?```", "", text, flags=re.DOTALL))


def markdown_link_prose(text: str) -> str:
    """Exclude code, including native Pandoc inline and fenced math.

    Preserve surrounding link syntax: a code span in a real link's label
    does not stop that link from being checked.
    """
    lines: list[str] = []
    fence = ""
    for line in text.splitlines(keepends=True):
        if fence:
            if re.fullmatch(
                rf" {{0,3}}{re.escape(fence[0])}{{{len(fence)},}}[ \t]*",
                line.rstrip("\r\n"),
            ):
                fence = ""
            lines.append("\n")
            continue
        opening = re.match(r" {0,3}(`{3,}|~{3,})(.*)", line)
        if opening and not (
            opening[1].startswith("`") and "`" in opening[2]
        ):
            fence = opening[1]
            lines.append("\n")
        else:
            lines.append(line)
    return re.sub(
        r"(?<!`)(`+)(?!`)(.*?)(?<!`)\1(?!`)",
        lambda match: " " * len(match[0]),
        "".join(lines),
        flags=re.DOTALL,
    )


def local_markdown_targets(path: Path) -> list[Path]:
    """Resolve clone-local Markdown links from the document that owns them."""

    targets: list[Path] = []
    prose = markdown_link_prose(path.read_text(encoding="utf-8"))
    for raw in re.findall(r"\[[^]]+\]\(([^)]+)\)", prose):
        target = raw.split("#", 1)[0].split("?", 1)[0]
        if not target or "://" in target or target.startswith("mailto:"):
            continue
        targets.append((path.parent / target).resolve())
    return targets


def missing_checkout_targets(
    source: Path, tracked: set[Path]
) -> list[Path]:
    """Ignored author-local evidence must not make a public link look healthy."""
    directories = {parent for path in tracked for parent in path.parents}
    return [
        target for target in local_markdown_targets(source)
        if target not in tracked and target not in directories
    ]


def local_python_command_targets(source: Path, root: Path = ROOT) -> list[Path]:
    """Check concrete runnable instructions, including inline and fenced code."""
    targets = []
    for line in source.read_text(encoding="utf-8").splitlines():
        # Accepted evidence records describe execution at a pinned checkout;
        # their recorded commands are not instructions for the current clone.
        if (line.startswith("- Evidence records:")
                and re.search(r"environment=Public checkout [0-9a-f]{40}\b", line)
                and re.search(r"https://github\.com/[^ )]+/blob/[0-9a-f]{40}/", line)):
            continue
        line = re.sub(r"https?://[^\s)]+", "", line)
        for match in re.finditer(
            r"(?<![\w/])python3[ \t]+(?:-O[ \t]+)?"
            r"(scripts/[A-Za-z0-9_./-]+\.py)(?![A-Za-z0-9_./-])", line
        ):
            targets.append((root / match[1]).resolve())
    return targets


def test_checkout_command_boundary() -> None:
    with tempfile.TemporaryDirectory() as directory:
        root = Path(directory).resolve()
        source = root / "guide.md"
        scripts = root / "scripts"
        scripts.mkdir()
        public = scripts / "valid.py"
        ignored = scripts / "untracked.py"
        public.write_text("pass\n")
        ignored.write_text("pass\n")
        source.write_text(
            "`python3 scripts/valid.py`\n```sh\npython3 -O scripts/missing.py\n```\n"
            "python3 scripts/untracked.py\npython3 scripts/<name>.py\n"
            "python3 scripts/{name}.py\npython3 scripts/$name.py\n"
            "https://example.org/python3 scripts/valid.py\n"
            "- Evidence records: command=`python3 scripts/retired.py`; "
            "environment=Public checkout " + "a" * 40 + "; "
            "artifacts=https://github.com/example/repo/blob/" + "b" * 40 + "/old.py\n"
        )
        targets = local_python_command_targets(source, root)
        require(targets == [public, scripts / "missing.py", ignored],
                "command scan lost runnable code or misread placeholders/pinned records")
        require([target for target in targets if target not in {public} or not target.is_file()]
                == [scripts / "missing.py", ignored],
                "missing and existing untracked executable instructions must both fail")


def test_checkout_link_boundary() -> None:
    with tempfile.TemporaryDirectory() as directory:
        root = Path(directory).resolve()
        source = root / "guide.md"
        public = root / "public.md"
        ignored = root / "private-evidence.pdf"
        public.write_text("Public evidence\n", encoding="utf-8")
        ignored.write_bytes(b"Local evidence is not shipped")
        source.write_text(
            "[public](public.md#section) [private](private-evidence.pdf) "
            "[absent](missing.md) [remote](https://example.org/paper.pdf)\n"
            r"For the bounds, write $`b_k^{(r)}=[z^k](z;q)_\infty^{-r}`$."
            "\n`[inline example](not-a-link.md)`\n"
            "``[example with ` inside](also-not-a-link.md)``\n"
            "``` math\n[z^k](z;q)_\\infty^{-r}\n```\n"
            "~~~~ text\n[tilde example](not-a-link.md)\n~~~~\n"
            "```` text\n```\n[nested fence](not-a-link.md)\n````\n"
            "[`public code label`](public.md)\n"
            "`unmatched opener [still a link](public.md)\n",
            encoding="utf-8",
        )
        require(
            local_markdown_targets(source)
            == [public, ignored, root / "missing.md", public, public],
            "math and code examples must not become links or hide real links",
        )
        require(
            missing_checkout_targets(source, {source, public})
            == [ignored, root / "missing.md"],
            "link validation must reject ignored and missing evidence alike",
        )


# Frozen evidence and generated manuscript text preserve their original links;
# current guides are checked recursively, including newly added nested guides.
HISTORICAL_DOC_DIRS = (
    "research-commons/rounds", "research-commons/benchmarks", "release",
    "systems-paper-evidence", "reading-edition/records",
)
GENERATED_PAPER_TEXT_DIRS = ("papers/full-text",)
GENERATED_PAPER_TEXT_FILES = {
    "reading-edition/plectis-reading-edition.md",
    "reading-edition/plectis-short-papers.md",
}
HISTORICAL_SNAPSHOT_FILES = {
    "reference/ARGUMENT_FRONTIER.md", "reference/WAVE_INDEX.md",
}


def live_documentation_surfaces(root: Path = ROOT) -> list[Path]:
    """Select current Markdown guides by existing historical/output homes."""
    result = []
    for path in sorted((root / "docs").rglob("*.md")):
        rel = path.relative_to(root / "docs").as_posix()
        if any(rel.startswith(prefix + "/") for prefix in
               (*HISTORICAL_DOC_DIRS, *GENERATED_PAPER_TEXT_DIRS)):
            continue
        if rel in GENERATED_PAPER_TEXT_FILES or rel in HISTORICAL_SNAPSHOT_FILES:
            continue
        if re.search(r"(?:^|_)\d{4}-\d{2}-\d{2}(?:_|\.md$)", path.name):
            continue
        result.append(path)
    return result


def test_recursive_documentation_links() -> None:
    with tempfile.TemporaryDirectory() as raw:
        root = Path(raw).resolve()
        nested = root / "docs" / "agents" / "nested"
        nested.mkdir(parents=True)
        guide = nested / "guide.md"
        target = root / "docs" / "RESULTS.md"
        target.write_text("Results\n")
        guide.write_text("[current](../../RESULTS.md?plain=1#result) "
                         "[historical](https://github.com/wcook04/plectis-erdos/blob/" +
                         "a" * 40 + "/docs/RETIRED.md)\n")
        require(guide in live_documentation_surfaces(root), "nested guide escaped recursive scan")
        require(local_markdown_targets(guide) == [target], "relative nested link or historical URL misresolved")
        require(not missing_checkout_targets(guide, {guide, target}), "valid nested relative link rejected")
        guide.write_text("[broken](../../ABSENT.md)\n")
        require(missing_checkout_targets(guide, {guide, target}) == [root / "docs" / "ABSENT.md"],
                "missing nested guide link escaped")
        for relative in ("papers/full-text/frozen.md", "research-commons/rounds/round1/return.md",
                         "reference/QUALIFICATION_2026-09-13.md"):
            frozen = root / "docs" / relative
            frozen.parent.mkdir(parents=True, exist_ok=True)
            frozen.write_text("[old](missing.md)\n")
            require(frozen not in live_documentation_surfaces(root), "historical document treated as current guide")


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
    test_checkout_link_boundary()
    test_checkout_command_boundary()
    test_recursive_documentation_links()
    readme = (ROOT / "README.md").read_text(encoding="utf-8")
    human_entry = HUMAN_ENTRY.read_text(encoding="utf-8")
    results = (ROOT / "docs/RESULTS.md").read_text(encoding="utf-8")
    docs_index = (ROOT / "docs/README.md").read_text(encoding="utf-8")
    claims = json.loads((ROOT / "docs/claims.json").read_text(encoding="utf-8"))
    status_boundary = claims["external_verification_packet"]["boundary"]
    compact_status_boundary = " ".join(status_boundary.split())
    for relative in (
        "README.md",
        "docs/RESULTS.md",
        "paper/README.md",
    ):
        surface = (ROOT / relative).read_text(encoding="utf-8")
        require(
            compact_status_boundary in " ".join(surface.split()),
            f"{relative} lost the authority-owned release status boundary",
        )

    reader_surfaces = (
        ROOT / "README.md", ROOT / "paper/README.md",
        ROOT / "research/examples/ExternalVerificationPortfolio/README.md",
        *live_documentation_surfaces(),
    )
    tracked = {
        (ROOT / relative).resolve()
        for relative in subprocess.check_output(
            ["git", "ls-files", "-z"], cwd=ROOT, text=True,
            env=command_environment(), timeout=GIT_COMMAND_TIMEOUT_SECONDS,
        ).split("\0") if relative
    }
    for source in reader_surfaces:
        missing = missing_checkout_targets(source, tracked)
        require(not missing,
                f"{source.relative_to(ROOT)} links outside the public checkout: {missing}")
        for target in local_markdown_targets(source):
            require(target.is_file() or target.is_dir(), f"{source.relative_to(ROOT)} has a dead local link: {target}")

    command_surfaces = {
        *reader_surfaces, ROOT / "AGENTS.md", ROOT / "CONTRIBUTING.md",
        *(ROOT / "skills").rglob("SKILL.md"),
    }
    for source in sorted(command_surfaces):
        missing_commands = [target for target in local_python_command_targets(source)
                            if target not in tracked or not target.is_file()]
        require(not missing_commands,
                f"{source.relative_to(ROOT)} has missing/untracked executable commands: {missing_commands}")

    # Folder moves must leave every specialist guide reachable from the reader
    # hub, with links resolved from its new location, including generated pages.
    for group in ("agents", "verification", "reference"):
        index = ROOT / "docs" / group / "README.md"
        require(index in local_markdown_targets(ROOT / "docs/README.md"),
                f"documentation hub does not reach the {group} index")
        indexed = set(local_markdown_targets(index))
        for guide in index.parent.glob("*.md"):
            require(guide == index or guide in indexed, f"unindexed specialist guide: {guide}")
    orientation = json.loads((ROOT / "docs/orientation.json").read_text())
    require(orientation["drilldowns"]["current_papers"] == "paper/README.md",
            "machine orientation does not expose the current paper catalogue")
    require(orientation["source_provenance"]["human_exposition_role"] == "historical_joint_manuscript",
            "the retained historical manuscript is not labelled as such")
    require("../../paper/README.md" in (ROOT / "docs/reference/ORIENTATION.md").read_text(),
            "rendered orientation does not lead to the current papers")

    require(
        "../paper/README.md#problem-papers" in results,
        "RESULTS does not route readers to the current canonical paper catalogue",
    )

    # 2026-09-10: 1_400 -> 1_700 -> 2_000. The operator rewrote the front page in
    # his own voice (second pass the same day); the paper index carries
    # short/longer PDF links, one-line strongest results, and erdosproblems.com
    # URLs that this counter charges as words. The budget follows the authored
    # page, it does not reshape it. The 2026-09-19 exact #1041 release boundary
    # adds one authority-owned paragraph, so the same bounded surface allows 2_100.
    require(
        len(prose_words(readme)) <= 2_100,
        "README prose exceeds the human front-door budget",
    )
    # 2026-09-10, operator-directed: the front page carries no command block at
    # all. Commands live in REPRODUCIBILITY and the agent workbench, which the
    # README must name; the routed-surface checks below keep them reachable.
    require("```" not in readme, "README carries a command block; commands belong in REPRODUCIBILITY and the agent workbench")
    require(
        "](docs/REPRODUCIBILITY.md)" in readme
        and "](docs/agents/AGENT_WORKBENCH.md)" in readme,
        "README no longer routes readers to the documents that hold its commands",
    )
    require(compact_status_boundary in " ".join(readme.split()),
            "README does not state the authority-owned status boundary near the front")
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
        "AGENTS.md" in readme and "docs/agents/AGENT_WORKBENCH.md" in readme,
        "README must route agents to the separate workbench",
    )
    first_screen = readme.split("## Problem papers", 1)[0]
    require(
        "(docs/README.md)" in first_screen,
        "README does not lead human readers to the prose-first entry",
    )
    require(
        not re.search(r"(?m)^\|.+\|$", first_screen),
        "README first screen uses a routing table instead of prose",
    )
    require("```" not in first_screen and "git clone" not in first_screen,
        "README asks a cold reader to choose a checkout before showing the papers")
    require(
        "![Eight Erdős problem programmes:" in first_screen
        and "](.github/system-map.png)" in first_screen,
        "README opening lost the mathematical research-record banner",
    )
    for token in (
        "routes that stopped",
        "human judgement",
        "independent, AI-assisted prototype",
        "short paper",
    ):
        require(token in " ".join(first_screen.split()), f"README opening lost its project-purpose boundary: {token}")
    require(
        "(docs/RESULTS.md)" in first_screen,
        "README opening must route readers to the results and their limits",
    )
    require(
        "query_semantic.py" not in readme and "--publication-architecture" not in readme,
        "README exposes machine drilldowns that belong in agent documentation",
    )

    human_words = words(human_entry)
    require(450 <= len(human_words) <= 1_500,
            "human documentation entry must remain bounded")
    introduction = human_entry.split("## Choose a way in", 1)[0]
    require(len(words(introduction)) >= 35,
            "human entry must explain the mathematics before routing")
    require("[Results and limits](RESULTS.md)" in human_entry,
            "human entry must route current status to its owning guide")
    require("Comparator" in human_entry and "Palomar" in human_entry,
            "human entry must explain the two public review surfaces")
    require("python3 " not in human_entry and "```" not in human_entry,
            "human entry must not require shell commands")
    for limit in ("does not establish", "A finite computation covers its tested range",
                  "it is not peer review"):
        require(limit in " ".join(human_entry.split()),
                f"human entry lost the evidence limit: {limit}")
    architecture = (ROOT / "docs/ARCHITECTURE.md").read_text(encoding="utf-8")
    require("[Results and limits](RESULTS.md)" in architecture,
            "architecture must link its current mathematical status owner")

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
    require("(paper/README.md#problem-papers)" in readme,
            "README lost the canonical complete paper catalogue")
    catalogue = (ROOT / "paper/README.md").read_text(encoding="utf-8")
    require("## Problem papers" in catalogue,
            "README paper-catalogue anchor no longer resolves")
    agent_guide = (ROOT / "docs/agents/AGENT_GUIDE.md").read_text(encoding="utf-8")
    require("../RESULTS.md" in agent_guide and "## Validation" in agent_guide,
            "agent guide must preserve status-owner and mutation-validation routes")
    for slug in paper_slugs:
        require(f"{slug}.pdf" in catalogue, f"the linked catalogue omits the {slug} paper")
        stored = [
            path for path in tracked
            if path.is_relative_to(ROOT / "paper") and path.name == f"{slug}.pdf"
        ]
        require(len(stored) == 1 and stored[0].is_file(), f"missing PDF for {slug}")
        require(
            (ROOT / f"docs/papers/full-text/{slug}.md").is_file(),
            f"missing Markdown paper for {slug}",
        )

    guide_at = results.find("### Problem-by-problem guide")
    require(guide_at >= 0, "RESULTS must lead with the current problem guide")
    require(len(words(results)) <= 6_000,
            "RESULTS must not grow back into a duplicate technical inventory")
    require("claims.json" in results,
            "RESULTS does not defer public status to canonical data")
    for n in ("68", "243", "249", "251", "257", "269", "1041", "1049"):
        require(f'id="result-{n}"' in results,
                f"RESULTS lost its current programme summary for #{n}")
    for heading in ("## Choose a way in", "## Work through an argument",
                    "## The eight problems", "## Read the evidence",
                    "## Contribute", "## Specialist guides and records"):
        require(heading in docs_index, f"documentation guide omits {heading}")
    for relative in ("RESULTS.md", "ARCHITECTURE.md", "METHODOLOGY.md",
                     "REPRODUCIBILITY.md", "PRIOR_ART.md", "PRIVACY.md",
                     "THIRD_PARTY_NOTICES.md"):
        require(f"({relative})" in docs_index,
                f"documentation entry lost its reader guide {relative}")

    start_here = (ROOT / ".github/START_HERE_ISSUE.md").read_text(encoding="utf-8")
    require(
        "releases/download/" not in start_here,
        "start-here issue must not send people to frozen release PDFs",
    )
    require(
        "wcook04.github.io/plectis/maths/problems/erdos_257.html" in start_here,
        "start-here issue lost the live #257 problem page",
    )
    require(
        "blob/main/paper/257/erdos-257-mersenne-support-subseries.pdf" in start_here,
        "start-here issue lost the live #257 short paper on main",
    )

    print("human-first-contact: PASS")


if __name__ == "__main__":
    main()
