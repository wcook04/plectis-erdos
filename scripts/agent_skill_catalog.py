#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Read and validate the clone-local agent skill registry."""

from __future__ import annotations

import json
import re
import sys
from argparse import ArgumentParser
from pathlib import Path
from typing import Any


ROOT = Path(__file__).resolve().parents[1]
REGISTRY_PATH = ROOT / "skills" / "registry.json"
README_PATH = ROOT / "skills" / "README.md"
TOKEN_RE = re.compile(r"[a-z0-9]+")
SUPPORTED_SCHEMA = "plectis-agent-skill-registry/2"
ACTIVE_STATUSES = {"active", "deprecated"}


class SkillCatalogError(ValueError):
    """The committed skill registry and its workflow files disagree."""


def _frontmatter(path: Path) -> dict[str, str]:
    text = path.read_text(encoding="utf-8")
    lines = text.splitlines()
    if not lines or lines[0].strip() != "---":
        raise SkillCatalogError(f"{path.relative_to(ROOT)} has no YAML frontmatter")
    result: dict[str, str] = {}
    for line in lines[1:]:
        if line.strip() == "---":
            break
        match = re.fullmatch(r"([A-Za-z0-9_-]+):\s*(.+)", line)
        if match:
            result[match.group(1)] = match.group(2).strip().strip('"\'')
    for key in ("name", "description"):
        if not result.get(key):
            raise SkillCatalogError(f"{path.relative_to(ROOT)} is missing {key}")
    return result


def load_catalog() -> dict[str, Any]:
    data = json.loads(REGISTRY_PATH.read_text(encoding="utf-8"))
    if data.get("schema") != SUPPORTED_SCHEMA:
        raise SkillCatalogError("skills/registry.json has an unsupported schema")

    family_ids: set[str] = set()
    families: list[dict[str, Any]] = []
    for family in data.get("families", []):
        family_id = family.get("id")
        if not isinstance(family_id, str) or family_id in family_ids:
            raise SkillCatalogError(f"invalid or duplicate family id: {family_id!r}")
        if not isinstance(family.get("title"), str) or not family["title"].strip():
            raise SkillCatalogError(f"family {family_id} needs a title")
        if not isinstance(family.get("description"), str) or not family["description"].strip():
            raise SkillCatalogError(f"family {family_id} needs a description")
        family_ids.add(family_id)
        families.append(family)
    if not families:
        raise SkillCatalogError("skills/registry.json has no skill families")

    rows: list[dict[str, Any]] = []
    registered_ids: set[str] = set()
    registered_paths: set[str] = set()
    for registered in data.get("skills", []):
        skill_id = registered.get("id")
        rel = registered.get("path")
        if not isinstance(skill_id, str) or not isinstance(rel, str):
            raise SkillCatalogError("every skill row needs string id and path fields")
        if skill_id in registered_ids:
            raise SkillCatalogError(f"duplicate skill id: {skill_id}")
        if rel in registered_paths:
            raise SkillCatalogError(f"duplicate skill path: {rel}")
        family_id = registered.get("family")
        if family_id not in family_ids:
            raise SkillCatalogError(f"skill {skill_id} has unknown family {family_id!r}")
        status = registered.get("status")
        if status not in ACTIVE_STATUSES:
            raise SkillCatalogError(f"skill {skill_id} has invalid status {status!r}")
        stage = registered.get("stage")
        if not isinstance(stage, str) or not stage.strip():
            raise SkillCatalogError(f"skill {skill_id} needs a stage")
        path = ROOT / rel
        expected = ROOT / "skills" / skill_id / "SKILL.md"
        if path.resolve() != expected.resolve() or not path.is_file():
            raise SkillCatalogError(f"{skill_id} must resolve to skills/{skill_id}/SKILL.md")
        metadata = _frontmatter(path)
        if metadata["name"] != skill_id:
            raise SkillCatalogError(
                f"registry id {skill_id} disagrees with {rel} name {metadata['name']}"
            )
        registered_ids.add(skill_id)
        registered_paths.add(rel)
        rows.append(
            {
                **registered,
                "id": skill_id,
                "path": rel,
                "description": metadata["description"],
            }
        )

    disk_ids = {
        path.parent.name for path in (ROOT / "skills").glob("*/SKILL.md") if path.is_file()
    }
    if disk_ids != registered_ids:
        missing = sorted(disk_ids - registered_ids)
        stale = sorted(registered_ids - disk_ids)
        raise SkillCatalogError(
            f"skill registry coverage mismatch; missing={missing}, stale={stale}"
        )

    for row in rows:
        related = row.get("composes_with", [])
        if not isinstance(related, list) or not all(isinstance(value, str) for value in related):
            raise SkillCatalogError(f"skill {row['id']} composes_with must be a string list")
        unknown = set(related) - registered_ids
        if unknown:
            raise SkillCatalogError(
                f"skill {row['id']} composes with unknown skills: {sorted(unknown)}"
            )
        if row["id"] in related:
            raise SkillCatalogError(f"skill {row['id']} cannot compose with itself")

    lane_ids: set[str] = set()
    lanes: list[dict[str, Any]] = []
    for lane in data.get("lanes", []):
        lane_id = lane.get("id")
        if not isinstance(lane_id, str) or lane_id in lane_ids:
            raise SkillCatalogError(f"invalid or duplicate lane id: {lane_id!r}")
        lane_ids.add(lane_id)
        if not isinstance(lane.get("title"), str) or not lane["title"].strip():
            raise SkillCatalogError(f"lane {lane_id} needs a title")
        lane_skills = lane.get("skills")
        if (
            not isinstance(lane_skills, list)
            or not lane_skills
            or not all(isinstance(value, str) for value in lane_skills)
        ):
            raise SkillCatalogError(f"lane {lane_id} skills must be a non-empty string list")
        unknown = set(lane_skills) - registered_ids
        if unknown:
            raise SkillCatalogError(f"lane {lane_id} references unknown skills: {sorted(unknown)}")
        task_cues = lane.get("task_cues")
        if (
            not isinstance(task_cues, list)
            or not task_cues
            or not all(isinstance(value, str) and value.strip() for value in task_cues)
        ):
            raise SkillCatalogError(f"lane {lane_id} task_cues must be a non-empty string list")
        normalized_cues = [normalize(value) for value in task_cues]
        if "" in normalized_cues or len(normalized_cues) != len(set(normalized_cues)):
            raise SkillCatalogError(f"lane {lane_id} has empty or duplicate normalized task cues")
        for field in ("read", "commands"):
            values = lane.get(field)
            if not isinstance(values, list) or not all(
                isinstance(value, str) and value.strip() for value in values
            ):
                raise SkillCatalogError(f"lane {lane_id} {field} must be a string list")
        if not lane["read"]:
            raise SkillCatalogError(f"lane {lane_id} needs at least one read target")
        if not isinstance(lane.get("boundary"), str) or not lane["boundary"].strip():
            raise SkillCatalogError(f"lane {lane_id} needs a boundary")
        priority = lane.get("priority", 0)
        if not isinstance(priority, int):
            raise SkillCatalogError(f"lane {lane_id} priority must be an integer")
        lanes.append(lane)

    if data.get("fallback_lane") not in lane_ids:
        raise SkillCatalogError("fallback_lane does not name a registered lane")
    unused = registered_ids - {skill_id for lane in lanes for skill_id in lane["skills"]}
    if unused:
        raise SkillCatalogError(f"skills are not reachable from a task lane: {sorted(unused)}")
    return {
        **data,
        "skills": rows,
        "families": families,
        "lanes": lanes,
    }


def normalize(text: str) -> str:
    return " ".join(TOKEN_RE.findall(text.casefold()))


def rank_lanes(catalog: dict[str, Any], task: str) -> list[dict[str, Any]]:
    normalized_task = normalize(task)
    task_tokens = set(normalized_task.split())
    ranked: list[dict[str, Any]] = []
    for order, lane in enumerate(catalog["lanes"]):
        matches: list[str] = []
        score = 0
        for cue in lane["task_cues"]:
            normalized_cue = normalize(cue)
            cue_tokens = normalized_cue.split()
            if not normalized_cue:
                continue
            if " " in normalized_cue and normalized_cue in normalized_task:
                matches.append(cue)
                score += 4 + len(cue_tokens)
            elif len(cue_tokens) == 1 and cue_tokens[0] in task_tokens:
                matches.append(cue)
                score += 2
        ranked.append({**lane, "score": score, "matched_cues": matches, "order": order})
    ranked.sort(key=lambda row: (-row["score"], -row.get("priority", 0), row["order"]))
    if ranked and ranked[0]["score"] > 0:
        return ranked
    fallback = next(row for row in ranked if row["id"] == catalog["fallback_lane"])
    fallback["fallback"] = True
    return [fallback, *[row for row in ranked if row is not fallback]]


def render_skill_index(catalog: dict[str, Any]) -> str:
    """Render the tracked human index from the registry and skill frontmatter."""
    by_family: dict[str, list[dict[str, Any]]] = {
        family["id"]: [] for family in catalog["families"]
    }
    for skill in catalog["skills"]:
        by_family[skill["family"]].append(skill)

    lines = [
        "# Clone-local agent skills",
        "",
        "These workflows travel with the public repository and use only tracked",
        "clone-local files. Route the task before opening a skill:",
        "",
        "```sh",
        'python3 scripts/agent_entry.py --entry "<task>"',
        "python3 scripts/agent_entry.py --skills",
        "python3 scripts/agent_entry.py --skill mine-open-problem",
        "```",
        "",
        "`registry.json` owns families, task lanes, lifecycle relationships, and",
        "complete coverage. Each `SKILL.md` owns its executable workflow and",
        "frontmatter description. This index is generated from both, so it cannot",
        "silently become a second catalog.",
        "",
    ]
    for family in catalog["families"]:
        lines.extend((f"## {family['title']}", "", family["description"], ""))
        for skill in by_family[family["id"]]:
            lines.append(f"- [{skill['id']}]({skill['id']}/SKILL.md) — {skill['description']}")
            route_titles = [
                lane["title"]
                for lane in catalog["lanes"]
                if skill["id"] in lane["skills"]
            ]
            lines.append(f"  Routed by: {', '.join(route_titles)}")
        lines.append("")

    maintenance = catalog.get("maintenance", {})
    lines.extend(
        (
            "## Maintain and dogfood",
            "",
            "Treat a route that exists but misclassifies a real task as drift. Update the",
            "registry or owning skill, regenerate this index, add the observed journey as a",
            "fixture, and run the clone-local checks before propagation.",
            "",
            "```sh",
            maintenance.get("write_command", "python3 scripts/agent_skill_catalog.py"),
            maintenance.get("check_command", "python3 scripts/agent_skill_catalog.py --check"),
            "python3 scripts/test_agent_entry.py",
            "python3 scripts/test_clone_skills.py",
            "python3 scripts/check_cold_clone_comprehension.py --quick",
            "```",
            "",
        )
    )
    return "\n".join(lines)


def check_index(catalog: dict[str, Any]) -> None:
    expected = render_skill_index(catalog)
    actual = README_PATH.read_text(encoding="utf-8")
    if actual != expected:
        raise SkillCatalogError(
            "skills/README.md is stale; run python3 scripts/agent_skill_catalog.py"
        )


def main(argv: list[str] | None = None) -> int:
    parser = ArgumentParser(description=__doc__)
    parser.add_argument(
        "--check",
        action="store_true",
        help="validate registry/workflow coverage and fail when the generated index is stale",
    )
    args = parser.parse_args(argv)
    try:
        catalog = load_catalog()
        if args.check:
            check_index(catalog)
            print(
                "agent skill catalog: current "
                f"({len(catalog['skills'])} skills, {len(catalog['families'])} families, "
                f"{len(catalog['lanes'])} lanes)"
            )
        else:
            README_PATH.write_text(render_skill_index(catalog), encoding="utf-8")
            print(f"wrote {README_PATH.relative_to(ROOT)}")
    except (OSError, json.JSONDecodeError, SkillCatalogError) as exc:
        print(f"agent skill catalog: {exc}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
