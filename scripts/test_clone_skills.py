#!/usr/bin/env python3
"""Test clone-local skill discovery, installation, and first-action routes."""

from __future__ import annotations

import json
import subprocess
import tempfile
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
INSTALLER = ROOT / "scripts" / "install_agent_skills.py"
SKILLS = (
    "install-clone-skills",
    "explain-public-system",
    "run-coupled-research-goals",
    "mine-open-problem",
    "lean-concurrent-validation",
    "propagate-research-consequences",
    "add-open-problem",
    "submit-pull-request",
    "erdos-research-return",
    "public-mathematical-writing",
)


def run(*args: str, expected: int = 0) -> subprocess.CompletedProcess[str]:
    result = subprocess.run(
        ["python3", str(INSTALLER), *args],
        cwd=ROOT,
        text=True,
        capture_output=True,
        check=False,
    )
    if result.returncode != expected:
        raise AssertionError(
            f"command returned {result.returncode}, expected {expected}:\n"
            f"stdout:\n{result.stdout}\nstderr:\n{result.stderr}"
        )
    return result


def main() -> int:
    readme = (ROOT / "README.md").read_text(encoding="utf-8")
    skill_index = (ROOT / "skills" / "README.md").read_text(encoding="utf-8")
    entry = (ROOT / "AGENTS.override.md").read_text(encoding="utf-8")
    registry = json.loads((ROOT / "skills" / "registry.json").read_text(encoding="utf-8"))
    registered = {row["id"] for row in registry["skills"]}

    listed = run("--list").stdout
    for name in SKILLS:
        skill = ROOT / "skills" / name / "SKILL.md"
        assert skill.is_file(), skill
        source = skill.read_text(encoding="utf-8")
        assert f"name: {name}" in source, name
        assert name in listed, name
        description = next(
            line.removeprefix("description: ")
            for line in source.splitlines()
            if line.startswith("description: ")
        )
        assert description in listed, name
        assert name in skill_index, name
        assert name in registered, name
        assert "/Users/" not in source and "src/ai_workflow" not in source, name

    for name in (
        "explain-public-system",
        "run-coupled-research-goals",
        "mine-open-problem",
        "propagate-research-consequences",
        "add-open-problem",
        "submit-pull-request",
    ):
        assert "skills/README.md" in readme
        assert name in skill_index, name
    assert "agent_entry.py --skills" in entry
    assert "install-clone-skills/SKILL.md" in skill_index
    assert "install_agent_skills.py" in (ROOT / "skills/install-clone-skills/SKILL.md").read_text()

    with tempfile.TemporaryDirectory(prefix="plectis-skill-test-") as temp:
        target = Path(temp) / "skills"
        preview = run("--target-dir", str(target), "--skill", "explain-public-system")
        assert "preview only" in preview.stdout
        assert not target.exists(), "preview mutated the destination"

        run(
            "--target-dir",
            str(target),
            "--skill",
            "explain-public-system",
            "--apply",
        )
        installed = target / "explain-public-system" / "SKILL.md"
        assert installed.is_file()
        run(
            "--target-dir",
            str(target),
            "--skill",
            "explain-public-system",
            "--check",
        )

        installed.write_text(installed.read_text(encoding="utf-8") + "\nchanged\n")
        collision = run(
            "--target-dir",
            str(target),
            "--skill",
            "explain-public-system",
            "--apply",
            expected=1,
        )
        assert "already contains different material" in collision.stderr

        link_target = Path(temp) / "links"
        run(
            "--target-dir",
            str(link_target),
            "--skill",
            "mine-open-problem",
            "--mode",
            "symlink",
            "--apply",
        )
        link = link_target / "mine-open-problem"
        assert link.is_symlink()
        run(
            "--target-dir",
            str(link_target),
            "--skill",
            "mine-open-problem",
            "--mode",
            "symlink",
            "--check",
        )

    print("clone skills: discovery, preview, copy, symlink, collision, and routes PASS")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
