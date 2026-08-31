#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Read and validate the clone-local agent skill registry."""

from __future__ import annotations

import json
import re
from pathlib import Path
from typing import Any


ROOT = Path(__file__).resolve().parents[1]
REGISTRY_PATH = ROOT / "skills" / "registry.json"
TOKEN_RE = re.compile(r"[a-z0-9]+")


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
    if data.get("schema") != "plectis-agent-skill-registry/1":
        raise SkillCatalogError("skills/registry.json has an unsupported schema")

    rows: list[dict[str, Any]] = []
    registered_ids: set[str] = set()
    for registered in data.get("skills", []):
        skill_id = registered.get("id")
        rel = registered.get("path")
        if not isinstance(skill_id, str) or not isinstance(rel, str):
            raise SkillCatalogError("every skill row needs string id and path fields")
        if skill_id in registered_ids:
            raise SkillCatalogError(f"duplicate skill id: {skill_id}")
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
        rows.append(
            {
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

    lane_ids: set[str] = set()
    lanes: list[dict[str, Any]] = []
    for lane in data.get("lanes", []):
        lane_id = lane.get("id")
        if not isinstance(lane_id, str) or lane_id in lane_ids:
            raise SkillCatalogError(f"invalid or duplicate lane id: {lane_id!r}")
        lane_ids.add(lane_id)
        unknown = set(lane.get("skills", [])) - registered_ids
        if unknown:
            raise SkillCatalogError(f"lane {lane_id} references unknown skills: {sorted(unknown)}")
        if not lane.get("task_cues"):
            raise SkillCatalogError(f"lane {lane_id} has no task cues")
        lanes.append(lane)

    if data.get("fallback_lane") not in lane_ids:
        raise SkillCatalogError("fallback_lane does not name a registered lane")
    return {
        **data,
        "skills": rows,
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
    ranked.sort(key=lambda row: (-row["score"], row["order"]))
    if ranked and ranked[0]["score"] > 0:
        return ranked
    fallback = next(row for row in ranked if row["id"] == catalog["fallback_lane"])
    fallback["fallback"] = True
    return [fallback, *[row for row in ranked if row is not fallback]]
