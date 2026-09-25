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
import io
import json
import re
from contextlib import redirect_stdout
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
STOPPING_RULE_RE = re.compile(
    r"\*\*Depth past[^\n]*adds nothing"
    r"|Survival past the threshold index is forced by counting",
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

    # Independent analytic tail bounds certify these first rejections.  They
    # occur beyond the discarded measure-based stopping scale (about 13.9),
    # so the production probe must keep searching when the requested depth
    # crosses that scale.  The certificate also checks every earlier skip.
    certificate_spec = importlib.util.spec_from_file_location(
        "late_rejection", HOME.parent / "sparse_interpolation" / "late_rejection.py"
    )
    certificate_module = importlib.util.module_from_spec(certificate_spec)
    assert certificate_spec.loader is not None
    certificate_spec.loader.exec_module(certificate_module)
    for target in (Fraction(189, 388), Fraction(577, 388)):
        certificate = certificate_module.certify_late_rejection(target)
        assert certificate["first_rejection"] == 17
        assert tail_upper[17] <= Fraction(certificate["tail_upper_bound"])
        for depth in (13, 14, 16):
            assert probe.classify(target, indices, weight, tail_upper, depth) == (
                "not_excluded", None
            ), (target, depth)
        for depth in (17, 60):
            assert probe.classify(target, indices, weight, tail_upper, depth) == (
                "excluded", 17
            ), (target, depth)

    early = probe.single_target(Fraction(189, 388), "all", 16, 160)
    late = probe.single_target(Fraction(189, 388), "all", 17, 160)
    assert early["outcome"] == "not_excluded" and early["first_rejection"] is None
    assert late["outcome"] == "excluded" and late["first_rejection"] == 17
    assert late["selected_indices"] == [2, 3, 7, 9, 10, 14, 15, 16]
    assert late["tail_upper"] == "196609/25769803776"
    assert late["tail_bound_kind"] == "universal_analytic"
    assert late["tail_bound_from"] == 18
    assert Fraction(late["tail_upper"]) < Fraction(late["remainder"]) < Fraction(late["weight"])
    odd_gap = probe.single_target(Fraction(1, 2), "odd", 20, 160)
    assert odd_gap["outcome"] == "excluded" and odd_gap["first_rejection"] == 1
    assert odd_gap["tail_upper"] == "7/24" and odd_gap["tail_bound_from"] == 3
    assert probe.single_target(Fraction(1, 3), "all", 20, 160)["outcome"] == "finite_representation"
    assert probe.single_target(Fraction(1, 2), "all", 20, 160)["outcome"] == "not_excluded"
    for invalid in (Fraction(0), Fraction(-1, 2), Fraction(2)):
        try:
            probe.single_target(invalid, "all", 17, 160)
        except ValueError:
            pass
        else:
            raise AssertionError((invalid, "invalid target accepted"))
    output = io.StringIO()
    with redirect_stdout(output):
        assert probe.main(["--target", "189/388", "--depth", "16", "17",
                           "--horizon", "160", "--json"]) == 0
    cli_rows = json.loads(output.getvalue())["rows"]
    assert [row["outcome"] for row in cli_rows] == ["not_excluded", "excluded"]
    assert cli_rows[1] == late

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
        hit = STOPPING_RULE_RE.search(text)
        assert hit is None, (str(surface.relative_to(ROOT)), hit.group(0))
    assert "not excluded through depth" in readme
    assert "no membership claim" in readme

    print("choices-and-contraction probe: saved counts replay; outcomes partition; "
          "late rejections certified; no promotion of finite survival or deterministic cutoff")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
