#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Measure whether a reformulation's position predicts that it was productive.

This is the one measurement this corpus can make and the published formal
corpora cannot. They are broad: Formal Conjectures carries about 3.7 Lean
statements per Erdos problem, and the Equational Theories Project carries one
node per equational law. This corpus is deep -- roughly 1,850 authored theorems
about a single open problem -- so it is the only place where the reformulation
graph of one open problem is dense enough to ask whether the graph has
predictive structure at all.

The question. A reformulation is cheap to produce and, on its own, proves
nothing: restating an open problem leaves it open. The field is now generating
reformulations at machine scale, so it matters whether some reformulations are
better bets than others, and whether that is visible at the time they are made
rather than only in hindsight.

The measurement. For each authored declaration, count how many other
declarations reference it in their proof bodies -- its fan-in, which is the
observable trace of having been built upon. Aggregate to statement nodes, then
ask whether features available when the node was introduced (its logical class,
whether it restates the open problem, how many open antecedents it carries, its
degree in the reformulation graph) separate the productive nodes from the dead
ends.

Both answers are results. If position predicts productivity, the graph is a tool
for choosing which restatement to pursue. If it predicts nothing, then
reformulation is a random walk, which is a real and useful negative finding about
a method the field is currently scaling up.

What this does not measure. Fan-in is usage inside this development, not
mathematical importance, and a declaration can be load-bearing while being cited
once. Reference counting is textual: it sees a name appearing in a proof body,
not a proof-term dependency, so it over-counts mentions in comments that survive
the comment mask and under-counts implicit use through simp sets. It is a proxy,
and it is reported as one.
"""

from __future__ import annotations

import argparse
from collections import Counter, defaultdict
import json
from pathlib import Path
import re
import statistics
import sys

ROOT = Path(__file__).resolve().parents[1]
ATLAS = ROOT / "docs" / "declaration_atlas.json"
CORPUS = ROOT / "docs" / "semantic_corpus.json"
OUTPUT = ROOT / "docs" / "reformulation_productivity.json"

LIBRARY_ROOTS = ("Erdos249257", "ErdosProblems")
IDENT_RE = re.compile(r"[A-Za-z_][A-Za-z0-9_'.!?]*")

sys.path.insert(0, str(ROOT / "scripts"))
from build_benchmark_packet import code_mask  # noqa: E402


def declaration_spans(path: Path, known: set[str]) -> list[tuple[str, int, int]]:
    """Return (name, body_start, body_end) for each declaration in a file."""
    lines = path.read_text(encoding="utf-8", errors="replace").splitlines()
    mask = code_mask(lines)
    heads: list[tuple[str, int]] = []
    head_re = re.compile(
        r"^\s*(?:@\[[^\]]*\]\s*)?"
        r"(?:private\s+|protected\s+|noncomputable\s+|partial\s+|unsafe\s+|local\s+)*"
        r"(theorem|lemma|def|abbrev|instance)\s+([A-Za-z_][A-Za-z0-9_'.!?]*)"
    )
    bare_re = re.compile(
        r"^\s*(?:private\s+|protected\s+|noncomputable\s+|partial\s+|unsafe\s+|local\s+)*"
        r"(theorem|lemma|def|abbrev|instance)\s*$"
    )
    for index, line in enumerate(lines):
        if not mask[index]:
            continue
        match = head_re.match(line)
        if match:
            heads.append((match.group(2), index))
            continue
        if bare_re.match(line):
            for offset in range(1, 4):
                nxt = index + offset
                if nxt >= len(lines) or not mask[nxt] or not lines[nxt].strip():
                    continue
                name = IDENT_RE.match(lines[nxt].strip())
                if name:
                    heads.append((name.group(0), index))
                break

    spans: list[tuple[str, int, int]] = []
    for position, (name, start) in enumerate(heads):
        end = heads[position + 1][1] if position + 1 < len(heads) else len(lines)
        spans.append((name, start, end))
    return spans


def fan_in(known: set[str]) -> tuple[Counter, dict[str, set[str]]]:
    """Count, for each known declaration, how many other declarations cite it."""
    citers: dict[str, set[str]] = defaultdict(set)
    for library in LIBRARY_ROOTS:
        base = ROOT / library
        if not base.is_dir():
            continue
        for path in sorted(base.rglob("*.lean")):
            lines = path.read_text(encoding="utf-8", errors="replace").splitlines()
            mask = code_mask(lines)
            for name, start, end in declaration_spans(path, known):
                body = " ".join(
                    lines[i] for i in range(start, min(end, len(lines))) if mask[i]
                )
                for token in set(IDENT_RE.findall(body)):
                    if token in known and token != name:
                        citers[token].add(name)
    return Counter({k: len(v) for k, v in citers.items()}), citers


def build() -> dict:
    atlas = json.loads(ATLAS.read_text(encoding="utf-8"))
    corpus = json.loads(CORPUS.read_text(encoding="utf-8"))

    generated = {d["name"] for d in atlas["declarations"] if d.get("generated_certificate")}
    authored = {
        d["name"]
        for d in atlas["declarations"]
        if not d.get("generated_certificate") and d["kind"] in ("theorem", "lemma")
    }
    known = {d["name"] for d in atlas["declarations"]}

    counts, _ = fan_in(known)

    # Aggregate to statement nodes. A node's productivity is the total fan-in of
    # the declarations that realise it, excluding citations from generated
    # certificate modules, which are emitted in bulk and would swamp the signal.
    nodes = corpus["statement_nodes"]
    degree_out = Counter()
    degree_in = Counter()
    reform_degree = Counter()
    for edge in corpus["relations"]:
        if edge.get("suppressed_in_views"):
            continue
        degree_out[edge["from"]] += 1
        degree_in[edge["to"]] += 1
        if edge["relation"] in ("reformulates", "equivalent_to", "specialises", "generalises"):
            reform_degree[edge["from"]] += 1
            reform_degree[edge["to"]] += 1

    rows = []
    for node in nodes:
        decls = [
            ev["declaration"]
            for ev in node.get("evidence", ())
            if ev.get("declaration") and ev["declaration"] not in generated
        ]
        if not decls:
            continue
        productivity = sum(counts.get(d, 0) for d in decls)
        rows.append(
            {
                "node": node["id"],
                "problem": node["problem"],
                "logical_class": node["logical_class"],
                "is_restatement": bool(node.get("is_restatement_of_open_problem")),
                "open_antecedents": len(node.get("open_antecedents") or ()),
                "declarations": len(decls),
                "productivity": productivity,
                "productivity_per_declaration": round(productivity / len(decls), 2),
                "graph_out_degree": degree_out.get(node["id"], 0),
                "graph_in_degree": degree_in.get(node["id"], 0),
                "reformulation_degree": reform_degree.get(node["id"], 0),
                "prior_art_state": node.get("prior_art_state"),
            }
        )

    def summarise(subset: list[dict], label: str) -> dict:
        if not subset:
            return {"label": label, "n": 0}
        values = [r["productivity_per_declaration"] for r in subset]
        return {
            "label": label,
            "n": len(subset),
            "median_fan_in_per_declaration": round(statistics.median(values), 2),
            "mean_fan_in_per_declaration": round(statistics.fmean(values), 2),
            "share_never_cited": round(sum(1 for v in values if v == 0) / len(values), 3),
        }

    by_class = [
        summarise([r for r in rows if r["logical_class"] == cls], cls)
        for cls in sorted({r["logical_class"] for r in rows})
    ]
    restatement_split = [
        summarise([r for r in rows if r["is_restatement"]], "restates_the_open_problem"),
        summarise([r for r in rows if not r["is_restatement"]], "does_not_restate"),
    ]
    antecedent_split = [
        summarise([r for r in rows if r["open_antecedents"] == 0], "no_open_antecedent"),
        summarise([r for r in rows if r["open_antecedents"] > 0], "carries_open_antecedent"),
    ]
    # Does being well-connected in the reformulation graph go with being built on?
    connected = sorted(rows, key=lambda r: -r["reformulation_degree"])
    quartile = max(1, len(connected) // 4)
    degree_split = [
        summarise(connected[:quartile], "top_quartile_reformulation_degree"),
        summarise(connected[-quartile:], "bottom_quartile_reformulation_degree"),
    ]

    return {
        "schema": "erdos249257-reformulation-productivity/1",
        "artifact_role": "generated_measurement_over_the_atlas_and_semantic_corpus",
        "question": (
            "Does a reformulation's position in the graph predict that it was built "
            "upon? Only a corpus with many statements of ONE open problem can ask "
            "this; the broad formal corpora carry too few statements per problem."
        ),
        "proxy_and_its_limits": (
            "Productivity is fan-in: how many other authored declarations reference "
            "this one in their proof bodies. That is usage inside this development, "
            "not mathematical importance, and reference counting is textual rather "
            "than proof-term. Citations from generated certificate modules are "
            "excluded because they are emitted in bulk."
        ),
        "scale": {
            "authored_theorem_like": len(authored),
            "generated_excluded": len(generated),
            "statement_nodes_measured": len(rows),
            "problems": 2,
            "authored_theorems_per_problem": round(len(authored) / 2),
            "comparison": {
                "formal_conjectures_statements_per_erdos_problem": 3.7,
                "equational_theories_nodes_per_law": 1.0,
                "density_ratio_vs_formal_conjectures": round((len(authored) / 2) / 3.7),
            },
        },
        "by_logical_class": by_class,
        "by_restatement": restatement_split,
        "by_open_antecedent": antecedent_split,
        "by_reformulation_degree": degree_split,
        "nodes": sorted(rows, key=lambda r: -r["productivity"]),
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()

    data = build()
    rendered = json.dumps(data, ensure_ascii=False, indent=1) + "\n"

    if args.check:
        if not OUTPUT.exists() or OUTPUT.read_text(encoding="utf-8") != rendered:
            print("measure_reformulation_productivity: output is stale", file=sys.stderr)
            return 1
        print("measure_reformulation_productivity: current")
        return 0

    OUTPUT.write_text(rendered, encoding="utf-8")
    scale = data["scale"]
    print(
        f"measured {scale['statement_nodes_measured']} nodes over "
        f"{scale['authored_theorem_like']} authored theorems "
        f"({scale['authored_theorems_per_problem']} per problem, "
        f"{scale['comparison']['density_ratio_vs_formal_conjectures']}x the density of "
        "Formal Conjectures)\n"
    )
    for group, title in (
        ("by_restatement", "restatement of the open problem"),
        ("by_open_antecedent", "carries an unproved antecedent"),
        ("by_reformulation_degree", "reformulation-graph degree"),
    ):
        print(f"  {title}:")
        for row in data[group]:
            if row["n"]:
                print(
                    f"    {row['label']:<38} n={row['n']:<4} "
                    f"median={row['median_fan_in_per_declaration']:<7} "
                    f"mean={row['mean_fan_in_per_declaration']:<7} "
                    f"never_cited={row['share_never_cited']:.0%}"
                )
    print("\n  by logical class:")
    for row in sorted(data["by_logical_class"], key=lambda r: -(r.get("median_fan_in_per_declaration") or 0)):
        if row["n"]:
            print(
                f"    {row['label']:<34} n={row['n']:<4} "
                f"median={row['median_fan_in_per_declaration']:<7} "
                f"never_cited={row['share_never_cited']:.0%}"
            )
    return 0


if __name__ == "__main__":
    sys.exit(main())
