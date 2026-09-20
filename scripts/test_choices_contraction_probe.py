#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Replay and meaning checks for the choices-and-contraction investigation.

The probe is finite evidence.  These checks keep it that way: the saved
counts must replay exactly, the three outcomes must partition the candidates,
and no reader-facing surface may turn "not excluded through depth N" into a
membership or representation claim.
"""
from __future__ import annotations

import importlib.util
import json
import re
from fractions import Fraction
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
HOME = ROOT / "research" / "experiments" / "choices_contraction"

# Phrases that promote finite survival to membership.  They are matched
# against every reader-facing surface that reports the probe.
PROMOTION_RE = re.compile(
    r"\balive\b|survives? forever|has an infinite (?:representation|code)"
    r"|(?:is|are) (?:therefore )?(?:represented|members?)\b(?! of the (?:list|team))",
    re.IGNORECASE,
)
READER_SURFACES = (
    HOME / "README.md",
    ROOT / "docs" / "reading-edition" / "INTRODUCTION.md",
    ROOT / "docs" / "reading-edition" / "plectis-reading-edition.md",
)


def load_probe():
    spec = importlib.util.spec_from_file_location(
        "rational_membership_probe", HOME / "rational_membership_probe.py"
    )
    module = importlib.util.module_from_spec(spec)
    assert spec.loader is not None
    spec.loader.exec_module(module)
    return module


def main() -> int:
    probe = load_probe()

    # The three outcomes partition the candidates and replay the saved rows.
    saved = json.loads((HOME / "results" / "grid_q12_24_36.json").read_text(encoding="utf-8"))
    assert set(saved["outcome_vocabulary"]) == set(probe.OUTCOMES), saved["outcome_vocabulary"]
    saved_rows = {(r["host"], r["q_max"], r["depth"]): r for r in saved["rows"]}
    for host in ("all", "odd"):
        previous = None
        for depth in (10, 20, 40):
            row = probe.run(host, 12, depth, 260)
            assert sum(row["counts"].values()) == row["candidates"], row
            assert row == saved_rows[(host, 12, depth)], (host, depth, "saved result does not replay")
            # Deeper search can only move fractions out of "not excluded".
            if previous is not None:
                assert row["counts"]["not_excluded"] <= previous, (host, depth)
            previous = row["counts"]["not_excluded"]

    # Known anchors from the #257 short paper: 3/4 lies in the first gap and
    # 1/3 is the finite sum at index 2.
    indices, weight, tail_upper, _, _ = probe.host_weights(probe.HOSTS["all"], 260)
    assert probe.classify(Fraction(3, 4), indices, weight, tail_upper, 60) == ("excluded", 1)
    assert probe.classify(Fraction(1, 3), indices, weight, tail_upper, 60) == ("finite_representation", 2)
    # 1/2 is undecided in the paper; the probe must report exactly that.
    assert probe.classify(Fraction(1, 2), indices, weight, tail_upper, 160) == ("not_excluded", None)

    # The large-cutoff table in the README is the saved computation.
    sweep = json.loads(
        (HOME / "results" / "full_host_q60_120_200_depth60.json").read_text(encoding="utf-8")
    )
    readme = (HOME / "README.md").read_text(encoding="utf-8")
    for row in sweep["rows"]:
        for value in (row["candidates"], row["counts"]["excluded"], row["counts"]["not_excluded"]):
            assert f"{value:,}" in readme, (row["q_max"], value, "README table drifted from results")

    # Meaning guard.
    for surface in READER_SURFACES:
        if not surface.exists():
            continue
        text = surface.read_text(encoding="utf-8")
        hit = PROMOTION_RE.search(text)
        assert hit is None, (str(surface.relative_to(ROOT)), hit.group(0))
    assert "not excluded through depth" in readme
    assert "no membership claim" in readme

    print("choices-and-contraction probe: saved counts replay; outcomes partition; no promotion of finite survival")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
