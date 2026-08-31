#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Route a cold-clone task to the smallest public Plectis Lean workflow."""

from __future__ import annotations

import argparse
import json
from typing import Any

from agent_skill_catalog import SkillCatalogError, load_catalog, rank_lanes


def skill_map(catalog: dict[str, Any]) -> dict[str, dict[str, Any]]:
    return {row["id"]: row for row in catalog["skills"]}


def entry_packet(catalog: dict[str, Any], task: str) -> dict[str, Any]:
    ranked = rank_lanes(catalog, task)
    primary = ranked[0]
    alternatives = [row for row in ranked[1:] if row["score"] > 0][:2]
    skills = skill_map(catalog)
    return {
        "schema": "plectis-agent-entry/1",
        "task": task,
        "route_status": "fallback" if primary.get("fallback") else "matched",
        "primary_lane": {
            key: primary[key]
            for key in (
                "id",
                "title",
                "score",
                "matched_cues",
                "read",
                "commands",
                "boundary",
            )
        },
        "skills": [skills[skill_id] for skill_id in primary["skills"]],
        "alternatives": [
            {
                "id": row["id"],
                "title": row["title"],
                "score": row["score"],
                "matched_cues": row["matched_cues"],
                "skills": row["skills"],
            }
            for row in alternatives
        ],
        "authority_posture": catalog["authority_posture"],
        "catalog_command": "python3 scripts/agent_entry.py --skills",
    }


def render_entry(packet: dict[str, Any]) -> str:
    lane = packet["primary_lane"]
    lines = [
        "Plectis Lean cold-clone route",
        f"Task: {packet['task']}",
        f"Lane: {lane['id']} — {lane['title']}",
    ]
    if packet["route_status"] == "fallback":
        lines.append("Match: no specific cue; using the safe repository-understanding fallback")
    else:
        lines.append(f"Match: {', '.join(lane['matched_cues'])}")
    lines.extend(("", "Open only:"))
    lines.extend(f"  - {path}" for path in lane["read"])
    lines.extend(("", "Use these skills:"))
    for skill in packet["skills"]:
        lines.append(f"  - {skill['id']}: {skill['description']}")
        lines.append(f"    {skill['path']}")
    if lane["commands"]:
        lines.extend(("", "Next commands:"))
        lines.extend(f"  - {command}" for command in lane["commands"])
    lines.extend(("", f"Boundary: {lane['boundary']}"))
    if packet["alternatives"]:
        lines.extend(("", "Other plausible lanes:"))
        for row in packet["alternatives"]:
            lines.append(f"  - {row['id']}: {row['title']}")
    lines.extend(("", f"All skills: {packet['catalog_command']}"))
    return "\n".join(lines)


def render_skills(catalog: dict[str, Any]) -> str:
    lines = ["Clone-local skills", ""]
    for skill in catalog["skills"]:
        lines.append(f"{skill['id']}")
        lines.append(f"  Use when: {skill['description']}")
        lines.append(f"  Open: {skill['path']}")
    lines.extend(("", 'Route a task: python3 scripts/agent_entry.py --entry "<task>"'))
    return "\n".join(lines)


def render_skill(catalog: dict[str, Any], skill_id: str) -> str:
    skills = skill_map(catalog)
    if skill_id not in skills:
        choices = ", ".join(sorted(skills))
        raise SkillCatalogError(f"unknown skill {skill_id!r}; choose one of: {choices}")
    skill = skills[skill_id]
    lanes = [lane for lane in catalog["lanes"] if skill_id in lane["skills"]]
    lines = [
        skill["id"],
        f"Use when: {skill['description']}",
        f"Open: {skill['path']}",
        "",
        "Used by lanes:",
    ]
    lines.extend(f"  - {lane['id']}: {lane['title']}" for lane in lanes)
    return "\n".join(lines)


def parser() -> argparse.ArgumentParser:
    result = argparse.ArgumentParser(description=__doc__)
    action = result.add_mutually_exclusive_group(required=True)
    action.add_argument("--entry", metavar="TASK", help="route a task to a bounded lane")
    action.add_argument("--skills", action="store_true", help="list every clone-local skill and its purpose")
    action.add_argument("--skill", metavar="ID", help="show one skill card")
    result.add_argument("--json", action="store_true", help="emit machine-readable JSON")
    return result


def main() -> int:
    args = parser().parse_args()
    try:
        catalog = load_catalog()
        if args.entry is not None:
            value: Any = entry_packet(catalog, args.entry)
            output = json.dumps(value, indent=2) if args.json else render_entry(value)
        elif args.skills:
            value = {"schema": catalog["schema"], "skills": catalog["skills"]}
            output = json.dumps(value, indent=2) if args.json else render_skills(catalog)
        else:
            skills = skill_map(catalog)
            if args.skill not in skills:
                raise SkillCatalogError(f"unknown skill {args.skill!r}")
            value = {
                **skills[args.skill],
                "lanes": [
                    lane["id"] for lane in catalog["lanes"] if args.skill in lane["skills"]
                ],
            }
            output = json.dumps(value, indent=2) if args.json else render_skill(catalog, args.skill)
    except (OSError, json.JSONDecodeError, SkillCatalogError) as exc:
        parser().error(str(exc))
    print(output)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
