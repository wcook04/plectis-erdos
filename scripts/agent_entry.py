#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Route a cold-clone task to the smallest public Plectis Lean workflow."""

from __future__ import annotations

import argparse
import json
import os
import subprocess
from difflib import get_close_matches
from pathlib import Path
from typing import Any

from agent_skill_catalog import ROOT, SkillCatalogError, load_catalog, rank_lanes


PUBLIC_REPOSITORY = "https://github.com/wcook04/plectis-erdos.git"


def checkout_card(root: Path = ROOT, *, check_upstream: bool = False) -> dict[str, Any]:
    """Identify this checkout without updating it or trusting a fork's origin.

    Remote comparison is opt-in and observes a ref at one instant. An offline
    card never calls a cached remote-tracking branch 'latest'.
    """
    env = {key: value for key, value in os.environ.items() if not key.startswith("GIT_")}
    env["GIT_TERMINAL_PROMPT"] = "0"
    env["GIT_OPTIONAL_LOCKS"] = "0"

    def git(*args: str, timeout: int = 3) -> str | None:
        try:
            result = subprocess.run(
                ["git", "-C", str(root), *args], capture_output=True,
                text=True, timeout=timeout, env=env, check=False,
            )
        except (OSError, subprocess.TimeoutExpired):
            return None
        return result.stdout.strip() if result.returncode == 0 else None

    top = git("rev-parse", "--show-toplevel")
    is_checkout = top is not None and Path(top).resolve() == root.resolve()
    head = git("rev-parse", "HEAD") if is_checkout else None
    status = git("status", "--porcelain", "--untracked-files=normal") if head else None
    card: dict[str, Any] = {
        "schema": "plectis-agent-checkout/1",
        "repository": PUBLIC_REPOSITORY,
        "commit": head,
        "branch": git("symbolic-ref", "--quiet", "--short", "HEAD") if head else None,
        "exact_tag": git("describe", "--tags", "--exact-match", "HEAD") if head else None,
        "worktree": "unknown" if status is None else "modified" if status else "clean",
        "upstream_status": "not_checked",
        "upstream_main_commit": None,
        "scope": "Routes and capabilities come from this checkout; tags are frozen editions.",
        "next_command": "python3 scripts/agent_entry.py --checkout --check-upstream",
    }
    if check_upstream:
        remote = git("ls-remote", "--exit-code", PUBLIC_REPOSITORY, "refs/heads/main", timeout=10)
        rows = [row.split() for row in (remote or "").splitlines()]
        revisions = [row[0] for row in rows if len(row) == 2 and row[1] == "refs/heads/main"]
        revision = revisions[0] if len(revisions) == 1 else None
        card["upstream_main_commit"] = revision
        card["upstream_status"] = (
            "unavailable" if revision is None else
            "no_local_commit" if head is None else
            "matches_main" if head == revision else "differs_from_main"
        )
    card["guidance"] = (
        "No checkout revision available. Use a Git clone to record reproducible provenance."
        if head is None else
        "Commit matches public main at check time; local modifications are reported separately."
        if card["upstream_status"] == "matches_main" else
        "This commit differs from public main; it may be older, ahead, or divergent. Preserve local work."
        if card["upstream_status"] == "differs_from_main" else
        "Public main could not be checked. Continue locally without claiming this is the latest revision."
        if card["upstream_status"] == "unavailable" else
        "Currentness is unverified. Check public main explicitly when the task requires latest work."
    )
    return card


def render_checkout(card: dict[str, Any]) -> str:
    return "\n".join((
        f"Checkout: {card['commit'] or 'unversioned'} ({card['branch'] or 'detached/archive'})",
        f"Tag: {card['exact_tag'] or 'none'}; worktree: {card['worktree']}",
        f"Public main: {card['upstream_status']} ({card['upstream_main_commit'] or 'unobserved'})",
        card["guidance"],
        f"Version check: {card['next_command']}",
    ))


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
                "task_intents": lane.get("task_intents", []),
            }
            for lane in lane_cards
        ],
    }


def entry_packet(catalog: dict[str, Any], task: str, *, purpose: str | None = None, scope: str | None = None) -> dict[str, Any]:
    ranked = rank_lanes(catalog, task)
    if purpose is not None:
        selected = [row for row in ranked if purpose in row.get("entry_purposes", [])]
        if len(selected) != 1:
            raise SkillCatalogError(f"unknown entry purpose {purpose!r}; inspect --skills")
        ranked = [selected[0], *[row for row in ranked if row is not selected[0]]]
    if scope is not None and not scope.strip():
        raise SkillCatalogError("scope must be nonempty")
    primary = ranked[0]
    alternatives = [row for row in ranked[1:] if row["score"] > 0][:2]
    skills = skill_map(catalog)
    return {
        "schema": "plectis-agent-entry/2",
        "task": task,
        "purpose": purpose,
        "scope": scope,
        "selection_reason": "explicit purpose" if purpose else "task language",
        "route_status": "explicit" if purpose else "fallback" if primary.get("fallback") else "matched",
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
    if packet.get("scope"):
        lines.append(f"Scope: {packet['scope']}")
    if packet.get("purpose"):
        lines.append(f"Purpose: {packet['purpose']} (explicit; scope does not override purpose)")
    if "checkout" in packet:
        lines.extend(("", render_checkout(packet["checkout"])))
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
        for intent in lane.get("task_intents", []):
            lines.append(
                f"    Action/object intent: {'/'.join(intent['actions'])} + "
                f"{'/'.join(intent['objects'])} (words need not be adjacent)"
            )
    if skill["composes_with"]:
        lines.extend(("", "Common next workflows:"))
        lines.extend(f"  - {related}" for related in skill["composes_with"])
    return "\n".join(lines)


def nonempty_selector(value: str) -> str:
    """Reject a supplied blank before loading the skill catalog."""
    if not value.strip():
        raise argparse.ArgumentTypeError("must not be empty or whitespace")
    return value


def parser() -> argparse.ArgumentParser:
    result = argparse.ArgumentParser(description=__doc__)
    action = result.add_mutually_exclusive_group(required=True)
    action.add_argument("--entry", type=nonempty_selector, metavar="TASK", help="route a task to a bounded lane")
    action.add_argument("--skills", action="store_true", help="list every clone-local skill and its purpose")
    action.add_argument("--skill", type=nonempty_selector, metavar="ID", help="show one skill card")

    action.add_argument("--checkout", action="store_true", help="show checkout provenance without routing a task")
    result.add_argument("--check-upstream", action="store_true", help="compare with public main over the network (no fetch or checkout changes)")
    result.add_argument("--purpose", help="explicit workflow purpose: research, method, infrastructure, write, return, reproduce")
    result.add_argument("--scope", help="paper, problem, declaration or experiment to keep in the handoff")
    result.add_argument("--json", action="store_true", help="emit machine-readable JSON")
    return result


def main() -> int:
    args = parser().parse_args()
    if args.check_upstream and not (args.checkout or args.entry is not None):
        parser().error("--check-upstream requires --checkout or --entry")
    if (args.purpose or args.scope) and args.entry is None:
        parser().error("--purpose and --scope require --entry")
    if args.checkout:
        card = checkout_card(check_upstream=args.check_upstream)
        print(json.dumps(card, indent=2) if args.json else render_checkout(card))
        return 0
    try:
        catalog = load_catalog()
        if args.entry is not None:
            value: Any = entry_packet(catalog, args.entry, purpose=args.purpose, scope=args.scope)
            value["checkout"] = checkout_card(check_upstream=args.check_upstream)
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
