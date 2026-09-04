#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Regression checks for clone-local task and skill discovery."""

from __future__ import annotations

import json
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

from agent_entry import entry_packet
from agent_skill_catalog import ROOT, load_catalog


ROUTE_CASES = {
    "explain how this repo works to a newcomer": ("understand_repository", "explain-public-system"),
    "I am new here and want to understand the eight open problems": (
        "understand_repository",
        "explain-public-system",
    ),
    "I am new here and want to attack one open problem": (
        "bounded_research",
        "mine-open-problem",
    ),
    "report theorem status and what remains open": ("mathematical_status", "explain-public-system"),
    "attack one open problem with proof search": ("bounded_research", "mine-open-problem"),
    "find a proof in Lean": ("bounded_research", "mine-open-problem"),
    "prove this Lean theorem": ("bounded_research", "mine-open-problem"),
    "run a sustained research campaign and keep working": (
        "sustained_research",
        "run-coupled-research-goals",
    ),
    "run a Lean build for the changed Lean source": ("lean_validation", "lean-concurrent-validation"),
    "propagate the downstream consequences of this new result": (
        "propagate_delta",
        "propagate-research-consequences",
    ),
    "edit the paper's reader-facing mathematical writing": (
        "public_writing",
        "public-mathematical-writing",
    ),
    "add a ninth problem to the corpus": ("add_problem", "add-open-problem"),
    "package a research return from an older clone": (
        "return_research",
        "erdos-research-return",
    ),
    "I cloned this repository, made mathematical progress, and want to send it back so it can be reviewed, assimilated, propagated, and credited": (
        "return_research",
        "erdos-research-return",
    ),
    "prepare a PR and submit pull request": ("submit_change", "submit-pull-request"),
    "install skills into Codex": ("install_skills", "install-clone-skills"),
    "install the clone-local skills": ("install_skills", "install-clone-skills"),
    "improve cold clone agent entry and skill discovery": (
        "repository_architecture",
        "maintain-public-infrastructure",
    ),
    "speed up the public Lean repo clone and build commands": (
        "repository_architecture",
        "maintain-public-infrastructure",
    ),
    "debug slow clone and duplicate builds": (
        "repository_architecture",
        "maintain-public-infrastructure",
    ),
    "organize consolidate and refresh clone-local skills": (
        "repository_architecture",
        "maintain-public-infrastructure",
    ),
    "the skills need organising consolidating and updating because they drifted": (
        "repository_architecture",
        "maintain-public-infrastructure",
    ),
    "audit every clone-local skill against the repository as it exists now and repair drift": (
        "repository_architecture",
        "maintain-public-infrastructure",
    ),
    "make the public clone self explaining and propagate accepted work": (
        "repository_architecture",
        "maintain-public-infrastructure",
    ),
    "dogfood instruction drift without private infrastructure": (
        "repository_architecture",
        "maintain-public-infrastructure",
    ),
    "I cloned the repository and want to prove Erdős problem 249": (
        "bounded_research",
        "mine-open-problem",
    ),
    "I cloned the repo and want to submit my changes upstream": (
        "submit_change",
        "submit-pull-request",
    ),
    "I have a patch from a fork that needs review and credit": (
        "return_research",
        "erdos-research-return",
    ),
    "please check whether this Lean theorem still compiles": (
        "lean_validation",
        "lean-concurrent-validation",
    ),
    "run the tests for my changed .lean file": (
        "lean_validation",
        "lean-concurrent-validation",
    ),
    "help me understand which skill I should use": (
        "repository_architecture",
        "maintain-public-infrastructure",
    ),
    "what skills are available for mathematical research?": (
        "repository_architecture",
        "maintain-public-infrastructure",
    ),
    "update the skill routing and make the workflows discoverable": (
        "repository_architecture",
        "maintain-public-infrastructure",
    ),
    "write an explanation of the strongest theorem for a mathematician": (
        "public_writing",
        "public-mathematical-writing",
    ),
    "add another Erdős problem and register its paper": (
        "add_problem",
        "add-open-problem",
    ),
    "keep researching this frontier until there is a stable result": (
        "sustained_research",
        "run-coupled-research-goals",
    ),
    "I found a counterexample; update every affected paper and claim": (
        "propagate_delta",
        "propagate-research-consequences",
    ),
    "package the work from my old checkout for maintainers": (
        "return_research",
        "erdos-research-return",
    ),
    "install only the research-return workflow into Codex": (
        "install_skills",
        "install-clone-skills",
    ),
    "prepare these finished commits as a pull request but do not push": (
        "submit_change",
        "submit-pull-request",
    ),
    "debug why two agents launched the same Lean build": (
        "lean_validation",
        "lean-concurrent-validation",
    ),
}


def run_cli(root: Path, *args: str) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        [sys.executable, str(root / "scripts" / "agent_entry.py"), *args],
        cwd=root,
        text=True,
        capture_output=True,
        check=False,
    )


def main() -> int:
    catalog = load_catalog()
    skill_ids = {row["id"] for row in catalog["skills"]}
    disk_ids = {
        path.parent.name for path in (ROOT / "skills").glob("*/SKILL.md") if path.is_file()
    }
    assert skill_ids == disk_ids
    assert all(row["description"] for row in catalog["skills"])
    assert {row["family"] for row in catalog["skills"]} == {
        row["id"] for row in catalog["families"]
    }
    assert all(row["stage"] and row["status"] == "active" for row in catalog["skills"])
    assert all(
        set(row["composes_with"]) <= skill_ids for row in catalog["skills"]
    )
    assert all("/Users/" not in json.dumps(row) for row in catalog["lanes"])
    assert "ai_workflow" not in json.dumps(catalog)
    for lane in catalog["lanes"]:
        for reference in lane["read"]:
            assert (ROOT / reference.split("#", 1)[0]).exists(), (lane["id"], reference)
        for command in lane["commands"]:
            words = command.split()
            if len(words) >= 2 and words[0] == "python3" and words[1].startswith("scripts/"):
                assert (ROOT / words[1]).is_file(), (lane["id"], command)

    for task, (expected_lane, expected_skill) in ROUTE_CASES.items():
        packet = entry_packet(catalog, task)
        assert packet["primary_lane"]["id"] == expected_lane, (task, packet)
        assert expected_skill in {row["id"] for row in packet["skills"]}, (task, packet)
        assert packet["primary_lane"]["read"], task
        assert packet["primary_lane"]["boundary"], task

    operational = entry_packet(
        catalog, "speed up the public Lean repo clone and build commands"
    )
    assert "lean_validation" in {
        row["id"] for row in operational["alternatives"]
    }
    duplicate_builds = entry_packet(catalog, "debug slow clone and duplicate builds")
    assert "lean_validation" in {
        row["id"] for row in duplicate_builds["alternatives"]
    }

    fallback = entry_packet(catalog, "frobnicate the unspecified material")
    assert fallback["route_status"] == "fallback"
    assert fallback["primary_lane"]["id"] == catalog["fallback_lane"]

    listed = run_cli(ROOT, "--skills", "--json")
    assert listed.returncode == 0, listed.stderr
    assert {row["id"] for row in json.loads(listed.stdout)["skills"]} == skill_ids
    assert {row["id"] for row in json.loads(listed.stdout)["families"]} == {
        row["id"] for row in catalog["families"]
    }
    assert {row["id"] for row in json.loads(listed.stdout)["lanes"]} == {
        row["id"] for row in catalog["lanes"]
    }

    human_listed = run_cli(ROOT, "--skills")
    assert human_listed.returncode == 0, human_listed.stderr
    assert "Routes:" in human_listed.stdout
    assert "Inspect one:" in human_listed.stdout

    skill = run_cli(ROOT, "--skill", "mine-open-problem", "--json")
    assert skill.returncode == 0, skill.stderr
    skill_value = json.loads(skill.stdout)
    assert skill_value["lanes"]
    assert all(row["task_cues"] for row in skill_value["route_lanes"])

    misspelled = run_cli(ROOT, "--skill", "mine-open-problm")
    assert misspelled.returncode != 0
    assert "mine-open-problem" in misspelled.stderr
    assert "--skills" in misspelled.stderr

    catalog_check = subprocess.run(
        [sys.executable, str(ROOT / "scripts" / "agent_skill_catalog.py"), "--check"],
        cwd=ROOT,
        text=True,
        capture_output=True,
        check=False,
    )
    assert catalog_check.returncode == 0, catalog_check.stdout + catalog_check.stderr

    routed = run_cli(ROOT, "--entry", "run a lean build", "--json")
    assert routed.returncode == 0, routed.stderr
    assert json.loads(routed.stdout)["primary_lane"]["id"] == "lean_validation"

    # Re-run the public command in a miniature cold clone containing only its
    # declared tracked inputs. This catches accidental imports from the parent
    # checkout, sibling repositories, user configuration, or private tooling.
    with tempfile.TemporaryDirectory(prefix="plectis-agent-entry-") as temporary:
        clone = Path(temporary)
        (clone / "scripts").mkdir()
        (clone / "skills").mkdir()
        for rel in ("scripts/agent_entry.py", "scripts/agent_skill_catalog.py"):
            shutil.copy2(ROOT / rel, clone / rel)
        shutil.copy2(ROOT / "skills" / "registry.json", clone / "skills" / "registry.json")
        shutil.copy2(ROOT / "skills" / "README.md", clone / "skills" / "README.md")
        for row in catalog["skills"]:
            destination = clone / row["path"]
            destination.parent.mkdir(parents=True, exist_ok=True)
            shutil.copy2(ROOT / row["path"], destination)
        cold = run_cli(clone, "--entry", "improve cold clone navigation", "--json")
        assert cold.returncode == 0, cold.stderr
        assert json.loads(cold.stdout)["primary_lane"]["id"] == "repository_architecture"

        catalog_script = clone / "scripts" / "agent_skill_catalog.py"
        current = subprocess.run(
            [sys.executable, str(catalog_script), "--check"],
            cwd=clone,
            text=True,
            capture_output=True,
            check=False,
        )
        assert current.returncode == 0, current.stdout + current.stderr
        clone_readme = clone / "skills" / "README.md"
        clone_readme.write_text(
            clone_readme.read_text(encoding="utf-8") + "\nstale copy\n",
            encoding="utf-8",
        )
        stale = subprocess.run(
            [sys.executable, str(catalog_script), "--check"],
            cwd=clone,
            text=True,
            capture_output=True,
            check=False,
        )
        assert stale.returncode == 1
        assert "skills/README.md is stale" in stale.stderr

        shutil.copy2(ROOT / "skills" / "README.md", clone_readme)
        clone_registry = clone / "skills" / "registry.json"
        invalid_registry = json.loads(clone_registry.read_text(encoding="utf-8"))
        invalid_registry["skills"][0]["family"] = "missing-family"
        clone_registry.write_text(json.dumps(invalid_registry), encoding="utf-8")
        invalid = run_cli(clone, "--skills", "--json")
        assert invalid.returncode != 0
        assert "unknown family" in invalid.stderr

        shutil.copy2(ROOT / "skills" / "registry.json", clone_registry)
        invalid_registry = json.loads(clone_registry.read_text(encoding="utf-8"))
        invalid_registry["lanes"][0]["task_cues"] = ["explain", "EXPLAIN"]
        clone_registry.write_text(json.dumps(invalid_registry), encoding="utf-8")
        invalid = run_cli(clone, "--skills", "--json")
        assert invalid.returncode != 0
        assert "duplicate normalized task cues" in invalid.stderr

    print(
        "agent entry: pass "
        f"({len(skill_ids)} skills, {len(catalog['lanes'])} lanes, "
        f"{len(ROUTE_CASES)} task fixtures, miniature cold clone)"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
