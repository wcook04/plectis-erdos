#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Compare argument-continuation exports run as a two-factor, two-level design.

  compare_argument_exports.py ARMS.json [--out REPORT.json] [--show 25]

ARMS.json maps an arm code to its run: {"00": {"graph": G, "export": E, "caps": {...},
"run": ID}, "10": ..., "01": ..., "11": ...}. The code gives the factor levels in the
NIST standard order: the first digit is weakening (the used-consequence pass, consumer
side), the second literal generalisation (producer side); 00 is the baseline and 11 runs
both. "export" (the export JSONL, optionally gzipped) is optional; without it the
statements an arm searched are unknown. "caps" records the caps the arm was launched with
in seconds (weaken, generalise, search): the export's meta record does not carry the
weakening cap.

The report has four parts.

Effective configuration: each arm's caps and what each pass did, from the export summary
the graph carries (attempts and milliseconds per pass). A pass launched with cap 0 that
still attempted work is flagged: the weakening loop checks its clock after an attempt, so
a zero cap does not by itself mean zero attempts. Cap totals that differ between arms are
flagged: the arms then compare allocation policies, and a pass's effect is not isolated.

Discovery yield: statements an arm's graph has and the baseline's does not, by origin,
and how many of them the arm supplies. These change the denominator, so they are kept
apart from reach.

Reach on matched targets: the statements every arm's search processed (statement records
of each export), and among them the closed hypotheses of corpus theorems, the demands the
corpus makes. For each target the four outcomes (supplied or not) give the two main
effects and the interaction as contrasts: a factor's effect is the mean outcome at its
high level less the mean at its low level, and the interaction's high level is 00 and 11.
A target some arm did not search is left out and listed, never counted as a failure.

Whole-graph sets: joint_novel = S11 - (S00 | S10 | S01), statements only the arm running
both passes supplies. The contrast with the one-sided arms alone, S11 - (S10 | S01), is
kept under that name: it can contain statements the baseline supplies.

Targets read off these runs make any effect exploratory; a claim of effect needs a replay
on targets fixed before the runs, with the same budget in every arm.
"""
from __future__ import annotations

import argparse
import collections
import gzip
import json
from pathlib import Path

ARMS = ("00", "10", "01", "11")
NAMES = {"00": "baseline", "10": "consumer", "01": "producer", "11": "joint"}
PASS_FIELDS = {
    "weaken": ("weakening_tried", "weakened_theorems", "weakening_consequences", "weakening_ms",
               "battery_consequences_tried"),
    "generalise": ("generalisation_theorems", "generalisation_literals", "generalised", "generalise_ms"),
    "search": ("telescope_ms", "search_ms", "statements_discovered", "statements_searched", "truncated"),
}


def _open(path: str):
    return gzip.open(path, "rt", encoding="utf-8") if path.endswith(".gz") else open(path, encoding="utf-8")


def load_graph(path: str) -> dict:
    with _open(path) as f:
        g = json.load(f)
    statements = {s["key"]: s for s in g["statements"]}
    return {
        "statements": statements,
        "supplied": {k for k, s in statements.items() if s.get("status") == "supplied"},
        "demands": {h for t in g.get("theorems", []) for h in t.get("hypotheses", [])},
        "summary": (g.get("source") or {}).get("export_summary") or {},
        "config": (g.get("source") or {}).get("export_config") or {},
    }


def load_searched(path: str) -> set[str]:
    searched = set()
    with _open(path) as f:
        for line in f:
            if '"statement"' not in line:
                continue
            row = json.loads(line)
            if row.get("record") == "statement":
                searched.add(row["key"])
    return searched


def effects(outcomes: dict[str, dict[str, bool]]) -> dict:
    """Mean contrasts over targets; outcomes[target][arm] is whether the arm supplies it."""
    patterns = collections.Counter()
    w = g = wg = 0.0
    for y in outcomes.values():
        v = {a: 1 if y[a] else 0 for a in ARMS}
        patterns["".join(str(v[a]) for a in ARMS)] += 1
        w += (v["10"] + v["11"] - v["00"] - v["01"]) / 2
        g += (v["01"] + v["11"] - v["00"] - v["10"]) / 2
        wg += (v["00"] + v["11"] - v["10"] - v["01"]) / 2
    n = len(outcomes)
    return {"targets": n, "patterns_y00_y10_y01_y11": dict(sorted(patterns.items())),
            "weakening_effect": w / n if n else None, "generalisation_effect": g / n if n else None,
            "interaction": wg / n if n else None}


def configuration(arm: dict, graph: dict) -> dict:
    caps = arm.get("caps") or {}
    summary = graph["summary"]
    out = {"caps_seconds": caps, "cap_total_seconds": sum(caps.get(k, 0) for k in ("weaken", "generalise", "search")),
           "consequence_battery_allowance_seconds": caps.get("weaken", 0) / 2,
           "passes": {p: {f: summary.get(f) for f in fields} for p, fields in PASS_FIELDS.items()},
           "elapsed_ms": summary.get("elapsed_ms"), "flags": []}
    if caps.get("weaken") == 0 and (summary.get("weakening_tried") or 0) > 0:
        out["flags"].append(f"weakening launched off but tried {summary['weakening_tried']} candidate(s)")
    if caps.get("generalise") == 0 and (summary.get("generalisation_literals") or 0) > 0:
        out["flags"].append(f"generalisation launched off but tried {summary['generalisation_literals']} literal(s)")
    if not summary:
        out["flags"].append("the graph carries no export summary")
    return out


def compare(arms: dict, show: int = 25) -> dict:
    graphs = {a: load_graph(arms[a]["graph"]) for a in ARMS}
    searched = {a: (load_searched(arms[a]["export"]) if arms[a].get("export") else None) for a in ARMS}
    config = {a: configuration(arms[a], graphs[a]) for a in ARMS}
    totals = {a: config[a]["cap_total_seconds"] for a in ARMS}
    design_flags = []
    if len(set(totals.values())) > 1:
        design_flags.append("cap totals differ between arms (" + ", ".join(f"{NAMES[a]} {totals[a]}s" for a in ARMS)
                            + "): the arms compare allocation policies and no pass's effect is isolated")
    base = graphs["00"]["statements"]
    discovery = {}
    for a in ("10", "01", "11"):
        new = set(graphs[a]["statements"]) - set(base)
        by_origin = collections.Counter((graphs[a]["statements"][k].get("origins") or ["?"])[0] for k in new)
        discovery[NAMES[a]] = {"statements": len(new), "supplied": len(new & graphs[a]["supplied"]),
                               "by_origin": dict(by_origin.most_common())}
    S = {a: graphs[a]["supplied"] for a in ARMS}
    sets = {
        "joint_novel": S["11"] - (S["00"] | S["10"] | S["01"]),
        "joint_versus_one_sided_only": S["11"] - (S["10"] | S["01"]),
        "baseline_lost_in_joint": S["00"] - S["11"],
        "one_sided_lost_in_joint": (S["10"] | S["01"]) - S["11"],
    }
    report = {"arms": {NAMES[a]: {"code": a, "run": arms[a].get("run"), **config[a]} for a in ARMS},
              "design_flags": design_flags, "discovery_yield": discovery,
              "whole_graph_sets": {k: len(v) for k, v in sets.items()}, "matched": {}}
    if all(searched[a] is not None for a in ARMS):
        common = set.intersection(*(searched[a] for a in ARMS))
        union = set.union(*(searched[a] for a in ARMS))
        demands = common & graphs["00"]["demands"]
        for label, targets in (("searched_by_every_arm", common), ("corpus_demands_searched_by_every_arm", demands)):
            outcomes = {t: {a: t in S[a] for a in ARMS} for t in targets}
            block = effects(outcomes)
            block["joint_novel"] = sorted(t for t, y in outcomes.items() if y["11"] and not (y["00"] or y["10"] or y["01"]))
            report["matched"][label] = block
        unmatched = {t for t in union - common if any(t in S[a] for a in ARMS)}
        report["matched"]["supplied_but_not_searched_by_every_arm"] = len(unmatched)
    else:
        report["matched"]["note"] = "an export is missing, so the searched statements are unknown"
    report["whole_graph_joint_novel"] = [
        {"key": k, "type": graphs["11"]["statements"][k].get("type", "")[:300],
         "problems": graphs["11"]["statements"][k].get("problems"),
         "origins": graphs["11"]["statements"][k].get("origins")}
        for k in sorted(sets["joint_novel"], key=lambda k: len(graphs["11"]["statements"][k].get("type") or ""))[:show]]
    report["status"] = "exploratory: targets read off these runs"
    return report


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("arms")
    ap.add_argument("--out")
    ap.add_argument("--show", type=int, default=25)
    a = ap.parse_args()
    arms = json.loads(Path(a.arms).read_text(encoding="utf-8"))
    report = compare(arms, a.show)
    for name, c in report["arms"].items():
        p = c["passes"]
        print(f"{name:9} caps {c['caps_seconds']} total {c['cap_total_seconds']}s  weakening tried "
              f"{p['weaken']['weakening_tried']} ({p['weaken']['weakening_ms']} ms)  generalisation literals "
              f"{p['generalise']['generalisation_literals']} ({p['generalise']['generalise_ms']} ms)  searched "
              f"{p['search']['statements_searched']}  {'; '.join(c['flags'])}")
    for flag in report["design_flags"]:
        print("DESIGN:", flag)
    print("discovery yield:", json.dumps(report["discovery_yield"], ensure_ascii=False))
    print("whole-graph sets:", report["whole_graph_sets"])
    for label, block in report["matched"].items():
        print(f"matched {label}:", json.dumps(block if not isinstance(block, dict) else
                                             {k: v for k, v in block.items() if k != "joint_novel"}, ensure_ascii=False),
              f"joint_novel {len(block['joint_novel'])}" if isinstance(block, dict) and "joint_novel" in block else "")
    for row in report["whole_graph_joint_novel"]:
        print(f"  {row['key']} {row['problems']} {row['origins']}\n      {row['type']}")
    if a.out:
        Path(a.out).write_text(json.dumps(report, indent=1, ensure_ascii=False) + "\n", encoding="utf-8")


if __name__ == "__main__":
    main()
