#!/usr/bin/env python3
"""Check the public split between human mathematical prose and agent machinery."""

import json
from pathlib import Path

from check_release import has_release_status_boundary


ROOT = Path(__file__).resolve().parents[1]
def read(path: str) -> str:
    return (ROOT / path).read_text(encoding="utf-8")


def require(condition: bool, message: str) -> None:
    if not condition:
        raise SystemExit(message)


def release_status_boundary() -> str:
    claims = json.loads(read("docs/claims.json"))
    boundary = claims["external_verification_packet"].get("boundary")
    require(isinstance(boundary, str) and boundary.strip(),
            "docs/claims.json lacks the release status boundary")
    return boundary


def main() -> None:
    claims = json.loads(read("docs/claims.json"))
    boundary = release_status_boundary()
    require(has_release_status_boundary(boundary.replace(". ", ".\n"), claims),
            "release boundary check must tolerate line wrapping")
    for missing in ("", "All eight problems remain open.",
                    "The degree-seven example refutes Erdős #1041."):
        require(not has_release_status_boundary(missing, claims),
                "release boundary check accepted missing formulation or review limits")
    for path in ("README.md", "docs/SCOPE.md"):
        require(has_release_status_boundary(read(path), claims),
                f"{path} differs from the current claim-owner boundary")
    human = read("docs/READING_GUIDE.md")
    require("```" not in human, "HUMAN_ENTRY must not make readers begin with commands")
    require("\n|" not in human, "HUMAN_ENTRY must remain prose rather than a table")
    require(human.count("\n\n") >= 10, "HUMAN_ENTRY has lost its prose structure")
    # Boundaries are matched across line wrapping, so reflowing a paragraph
    # cannot hide or fake one.
    prose = " ".join(human.split())
    boundaries = (
        release_status_boundary(),
        "The other seven target problems are not resolved here",
        "Independent human review of correspondence with the historical curve-length formulation has not been recorded",
        "peer review",
    )
    for boundary in boundaries:
        require(boundary in prose, f"HUMAN_ENTRY lost claim boundary: {boundary}")

    # Current systems manuscripts are also public entry points. Their examples
    # may be historical, but their descriptions of the present corpus must not
    # restore the superseded blanket status split.
    for path in (ROOT / "paper/systems").glob("*.tex"):
        manuscript = " ".join(path.read_text(encoding="utf-8").split())
        for stale in (
            "all eight problems remain open",
            "All eight problems remain open",
            "all eight endpoint problems remain open",
            "are the two principal reviewed programmes",
        ):
            require(stale not in manuscript, f"{path.name} repeats obsolete corpus status: {stale}")

    readme = read("README.md")
    human_link = readme.find("docs/READING_GUIDE.md")
    first_table = readme.find("\n|")
    first_fence = readme.find("```")
    require(human_link >= 0, "README no longer links the human entry")
    require(first_table < 0 or human_link < first_table, "README presents a table before its human entry")
    require(first_fence < 0 or human_link < first_fence, "README presents commands before its human entry")

    contributing = read("CONTRIBUTING.md").split("## For agents and maintainers", 1)[0]
    require("```" not in contributing, "human contribution guidance contains a command block")
    require("python3 " not in contributing, "human contribution guidance exposes commands")

    skill_path = "skills/public-mathematical-writing/SKILL.md"
    skill = read(skill_path)
    require("ai_workflow" not in skill and "/Users/" not in skill, "public writing skill has a private dependency")
    require(skill_path in read("AGENTS.md"), "AGENTS.md does not route to the public writing skill")
    require(skill_path in read("docs/agents/AGENT_GUIDE.md"), "docs/agents/AGENT_GUIDE.md does not route to the public writing skill")
    require(
        "public-mathematical-writing/SKILL.md" in read("skills/README.md"),
        "skills/README.md does not list the public writing skill",
    )

    print("test_public_writing_contract: human prose and agent machinery remain separated")


if __name__ == "__main__":
    main()
