#!/usr/bin/env python3
"""Check the public split between human mathematical prose and agent machinery."""

from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]


def read(path: str) -> str:
    return (ROOT / path).read_text(encoding="utf-8")


def require(condition: bool, message: str) -> None:
    if not condition:
        raise SystemExit(message)


def main() -> None:
    human = read("HUMAN_ENTRY.md")
    require("```" not in human, "HUMAN_ENTRY must not make readers begin with commands")
    require("\n|" not in human, "HUMAN_ENTRY must remain prose rather than a table")
    require(human.count("\n\n") >= 10, "HUMAN_ENTRY has lost its prose structure")
    for boundary in ("All eight problems remain open", "universal question", "peer review"):
        require(boundary in human, f"HUMAN_ENTRY lost claim boundary: {boundary}")

    readme = read("README.md")
    human_link = readme.find("HUMAN_ENTRY.md")
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
    require(skill_path in read("AGENTS.override.md"), "AGENTS.override.md does not route to the public writing skill")
    require(skill_path in read("AGENTS.md"), "AGENTS.md does not route to the public writing skill")
    require(
        "public-mathematical-writing/SKILL.md" in read("skills/README.md"),
        "skills/README.md does not list the public writing skill",
    )

    print("test_public_writing_contract: human prose and agent machinery remain separated")


if __name__ == "__main__":
    main()
