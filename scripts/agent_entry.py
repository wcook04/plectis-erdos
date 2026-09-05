#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Route a cold-clone task to the smallest public Plectis Lean workflow."""

from __future__ import annotations

import argparse
import json
from difflib import get_close_matches
from typing import Any

from agent_skill_catalog import SkillCatalogError, load_catalog, rank_lanes


def skill_map(catalog: dict[str, Any]) -> dict[str, dict[str, Any]]:
    return {row["id"]: row for row in catalog["skills"]}


def lanes_for_skill(catalog: dict[str, Any], skill_id: str) -> list[dict[str, Any]]:
    return [lane for lane in catalog["lanes"] if skill_id in lane["skills"]]


def skill_card(catalog: dict[str, Any], skill_id: str) -> dict[str, Any]:
    skills = skill_map(catalog)
    if skill_id not in skills:
        suggestions = get_close_matches(skill_id, sorted(skills), n=3, cutoff=0.45)
        hint = f"; did you mean: {', '.join(suggestions)}" if suggestions else ""
        raise SkillCatalogError(
            f"unknown skill {skill_id!r}{hint}; list the catalog with --skills"
        )
    lane_cards = lanes_for_skill(catalog, skill_id)
    return {
        **skills[skill_id],
        "lanes": [lane["id"] for lane in lane_cards],
        "route_lanes": [
            {
                "id": lane["id"],
                "title": lane["title"],
                "task_cues": lane["task_cues"],
            }
            for lane in lane_cards
        ],
    }


def entry_packet(catalog: dict[str, Any], task: str) -> dict[str, Any]:
    ranked = rank_lanes(catalog, task)
    primary = ranked[0]
    alternatives = [row for row in ranked[1:] if row["score"] > 0][:2]
    skills = skill_map(catalog)
    return {
        "schema": "plectis-agent-entry/2",
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
                "read": row["read"][:1],
                "commands": row["commands"][:1],
                "boundary": row["boundary"],
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
            for path in row["read"]:
                lines.append(f"    Open: {path}")
            for command in row["commands"]:
                lines.append(f"    Next: {command}")
    lines.extend(("", f"All skills: {packet['catalog_command']}"))
    return "\n".join(lines)


def render_skills(catalog: dict[str, Any]) -> str:
    lines = ["Clone-local skills", ""]
    by_family = {family["id"]: [] for family in catalog["families"]}
    for skill in catalog["skills"]:
        by_family[skill["family"]].append(skill)
    for family in catalog["families"]:
        lines.append(f"{family['title']}")
        lines.append(f"  {family['description']}")
        for skill in by_family[family["id"]]:
            routes = ", ".join(
                lane["title"] for lane in lanes_for_skill(catalog, skill["id"])
            )
            lines.append(f"  {skill['id']} [{skill['stage']}]")
            lines.append(f"    Use when: {skill['description']}")
            lines.append(f"    Routes: {routes}")
            lines.append(f"    Open: {skill['path']}")
        lines.append("")
    lines.extend(
        (
            "",
            'Route a task: python3 scripts/agent_entry.py --entry "<task>"',
            "Inspect one: python3 scripts/agent_entry.py --skill <skill-id>",
        )
    )
    return "\n".join(lines)


def render_skill(catalog: dict[str, Any], skill_id: str) -> str:
    skill = skill_card(catalog, skill_id)
    lanes = lanes_for_skill(catalog, skill_id)
    lines = [
        skill["id"],
        f"Family: {skill['family']}",
        f"Stage: {skill['stage']}",
        f"Use when: {skill['description']}",
        f"Open: {skill['path']}",
        "",
        "Used by lanes:",
    ]
    for lane in lanes:
        lines.append(f"  - {lane['id']}: {lane['title']}")
        lines.append(f"    Recognized requests: {', '.join(lane['task_cues'])}")
    if skill["composes_with"]:
        lines.extend(("", "Common next workflows:"))
        lines.extend(f"  - {related}" for related in skill["composes_with"])
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
            value = {
                "schema": catalog["schema"],
                "families": catalog["families"],
                "skills": catalog["skills"],
                "lanes": catalog["lanes"],
                "maintenance": catalog["maintenance"],
            }
            output = json.dumps(value, indent=2) if args.json else render_skills(catalog)
        else:
            value = skill_card(catalog, args.skill)
            output = json.dumps(value, indent=2) if args.json else render_skill(catalog, args.skill)
    except (OSError, json.JSONDecodeError, SkillCatalogError) as exc:
        parser().error(str(exc))
    print(output)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
