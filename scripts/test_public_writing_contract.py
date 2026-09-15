#!/usr/bin/env python3
"""Check the public split between human mathematical prose and agent machinery."""

import json
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
NUMBER_WORDS = (
    "zero", "one", "two", "three", "four", "five", "six",
    "seven", "eight", "nine", "ten", "eleven", "twelve",
)


def read(path: str) -> str:
    return (ROOT / path).read_text(encoding="utf-8")


def require(condition: bool, message: str) -> None:
    if not condition:
        raise SystemExit(message)


def open_status_sentence() -> str:
    """Return the guide's status sentence, with its count read from the problem index.

    docs/problems.json records each problem's status. When a problem is
    answered, the sentence the guide must carry changes with it.
    """
    index = json.loads(read("docs/problems.json"))
    problems = index["problems"]
    total = len(problems)
    require(total == index["problem_count"], "docs/problems.json problem_count disagrees with its rows")
    still_open = sum(1 for problem in problems if problem["status"] == "open")
    require(
        0 < still_open <= total < len(NUMBER_WORDS),
        f"no status sentence is defined for {still_open} open problems of {total}",
    )
    if still_open == total:
        return f"All {NUMBER_WORDS[total]} problems remain open"
    verb = "remains" if still_open == 1 else "remain"
    return f"{NUMBER_WORDS[still_open].capitalize()} of the {NUMBER_WORDS[total]} problems {verb} open"


def main() -> None:
    human = read("docs/READING_GUIDE.md")
    require("```" not in human, "HUMAN_ENTRY must not make readers begin with commands")
    require("\n|" not in human, "HUMAN_ENTRY must remain prose rather than a table")
    require(human.count("\n\n") >= 10, "HUMAN_ENTRY has lost its prose structure")
    # Boundaries are matched across line wrapping, so reflowing a paragraph
    # cannot hide or fake one.
    prose = " ".join(human.split())
    boundaries = (
        open_status_sentence(),
        "Universal irrationality and the proposed target values remain open",
        "peer review",
    )
    for boundary in boundaries:
        require(boundary in prose, f"HUMAN_ENTRY lost claim boundary: {boundary}")

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
