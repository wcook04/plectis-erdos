#!/usr/bin/env python3
"""Check the public human-to-agent contribution and credit route."""

from __future__ import annotations

import re
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]


def require(condition: bool, message: str) -> None:
    if not condition:
        raise AssertionError(message)


def text(path: str) -> str:
    return (ROOT / path).read_text(encoding="utf-8")


def local_markdown_links(path: str) -> list[Path]:
    source = ROOT / path
    links: list[Path] = []
    for target in re.findall(r"\[[^]]+\]\(([^)]+)\)", source.read_text(encoding="utf-8")):
        target = target.split("#", 1)[0]
        if not target or "://" in target:
            continue
        links.append((source.parent / target).resolve())
    return links


def main() -> int:
    contributing = text("CONTRIBUTING.md")
    human, marker, mechanics = contributing.partition("## For agents and maintainers")
    require(bool(marker), "contributor guide does not separate human meaning from agent mechanics")
    require(len(re.findall(r"\b[\w’'-]+\b", human)) >= 500, "human contribution route is too thin")
    for forbidden in ("```", "|---", "python3 ", "scripts/", "--require-", "return.json"):
        require(forbidden not in human, f"human contribution route exposes implementation syntax: {forbidden}")
    for concept in ("pull request", "plain-language", "accepted receipt", "credit", "older clone"):
        require(concept in human.lower(), f"human contribution route omits {concept!r}")

    required_files = (
        "docs/research-commons/README.md",
        "docs/research-commons/CREDIT_POLICY.md",
        "docs/research-commons/RETURN_PACKAGE_TEMPLATE.md",
        "docs/research-commons/schema/research-return-receipt.schema.json",
        ".github/ISSUE_TEMPLATE/research_progress.yml",
        ".github/ISSUE_TEMPLATE/research_return.yml",
        ".github/PULL_REQUEST_TEMPLATE.md",
        "skills/README.md",
        "skills/erdos-research-return/SKILL.md",
        "scripts/continue_research.py",
        "scripts/validate_research_return.py",
        "scripts/accept_research_return.py",
        "scripts/build_research_contributions.py",
        "scripts/build_research_contribution_recognition.py",
    )
    for path in required_files:
        require((ROOT / path).is_file(), f"clone-local contribution route is missing {path}")

    for source in (
        "CONTRIBUTING.md",
        "HUMAN_ENTRY.md",
        "docs/research-commons/README.md",
        "docs/research-commons/CREDIT_POLICY.md",
        "skills/README.md",
    ):
        for target in local_markdown_links(source):
            require(target.is_file(), f"{source} has a dead clone-local link: {target}")

    simple_issue = text(".github/ISSUE_TEMPLATE/research_progress.yml")
    for field in ("id: question", "id: finding", "id: evidence", "id: boundary", "id: credit"):
        require(field in simple_issue, f"plain-language research form omits {field}")
    for forbidden in ("python3", "return.json", "route-memory.json", "render: json"):
        require(forbidden not in simple_issue, f"plain-language research form exposes {forbidden}")

    pull_request = text(".github/PULL_REQUEST_TEMPLATE.md")
    require("Credit and provenance" in pull_request, "pull request route omits contribution credit")
    require("What remains open or uncertain?" in pull_request, "pull request route omits result boundary")
    require("python3" not in pull_request and "```" not in pull_request, "pull request front door is command-first")

    skill = text("skills/erdos-research-return/SKILL.md")
    agent_entry = text("AGENTS.override.md")
    for marker in (
        "scripts/continue_research.py",
        "scripts/validate_research_return.py",
        "scripts/accept_research_return.py",
        "scripts/build_research_contributions.py",
    ):
        require(marker in skill, f"research-return skill omits local tool {marker}")
    require("skills/erdos-research-return/SKILL.md" in agent_entry, "compact agent entry omits return skill")

    public_surfaces = "\n".join(
        text(path)
        for path in (
            "CONTRIBUTING.md",
            "docs/research-commons/README.md",
            "docs/research-commons/CREDIT_POLICY.md",
            "skills/erdos-research-return/SKILL.md",
        )
    )
    for forbidden in ("ai_workflow", "/Users/", "raw_seed.md", "private ledger path"):
        require(forbidden not in public_surfaces, f"public contribution route depends on private state: {forbidden}")

    require("structured" in mechanics.lower(), "agent mechanics do not expose the structured return path")
    print("contribution entry: human prose, clone-local return, provenance, credit, and update route PASS")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
