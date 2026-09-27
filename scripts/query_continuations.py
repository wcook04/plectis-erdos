#!/usr/bin/env python3
"""Query the kernel argument graph.

Reads ``docs/argument_continuations_graph.json.gz`` (built by
``scripts/build_argument_continuations.py`` from the kernel export) and answers
the questions a researcher asks before spending effort on a statement:

    summary                     graph totals, the export's own boundary and freshness
    problem N                   open targets, disguise classes, leverage for one problem
    find TEXT                   statements whose Lean rendering contains TEXT
    statement KEY               one statement: status, witness, refutation or
                                reductions, bundles, leverage, disguise class, consumers
    theorem NAME                one theorem: obligations (with status), conclusion,
                                unused hypotheses, papers
    why KEY                     the witness chain of a supplied statement, or the
                                refutation of a refuted one
    about CONSTANT              everything the graph holds about one corpus object
    next --problem N            a shortlist of open statements worth attacking next,
                                each with the structural reasons it was chosen
    near "WORDS"                the supplied and open statements sharing the most
                                corpus objects with a proposed statement
    barriers [--problem N]      kernel-checked barriers (countermodels, endpoint
                                equivalences, method ceilings) and what they constrain
    idle [--problem N]          theorems whose proofs never use some hypotheses
    weakenings [--problem N]    theorems whose proofs use a hypothesis only through
                                what they derive from it, with what that is
    papers [--problem N]        every paper result against the graph, with the
                                hypotheses its declarations need or use only in part
    criticality KEY|THEOREM     what loses its witness chain without it
    transfer                    reductions where a theorem attributed to one problem
                                supplies a statement attributed only to others
    check-bundle KEY... [--target KEY]
                                whether statements assumed together are jointly
                                impossible, and whether they restate a target
    cut TARGET --costs FILE     the cheapest set, within a pool of statements with
                                costs, that supplies the target without a conflict
    diff OLD NEW                how the frontier moved between two graph files
    packet --problem N          a bounded Markdown research packet for one problem

Every answer cites kernel theorems. "Open" means that no chain of corpus
theorems found by the export supplies or refutes the statement; the producer
relation is a lower bound, so an open statement may still follow from an
argument the export did not try. Nothing here is proof authority.
"""

from __future__ import annotations

import argparse
import gzip
import json
import os
import subprocess
import sys
from collections import defaultdict
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))

import argument_graph_frontier as frontier_module  # noqa: E402
import build_argument_continuations as builder  # noqa: E402

DEFAULT_GRAPH = ROOT / "docs" / "argument_continuations_graph.json.gz"
PACKET_BYTE_BUDGET = 150_000
# Keys from exports written before the key reordering lead with the zero-padded
# 32-bit structural hash; their informative digits start after these.
LEGACY_KEY_PREFIX = "00000000"


def load(path: Path) -> tuple[builder.Graph, dict[str, Any]]:
    if not path.is_file():
        raise SystemExit(
            f"{path} is missing. Build it with: python3 scripts/build_argument_continuations.py "
            "--export <argument-continuations artifact>")
    with gzip.open(path, "rt", encoding="utf-8") as handle:
        payload = json.load(handle)
    if payload.get("schema") != builder.GRAPH_SCHEMA:
        raise SystemExit(f"{path}: unexpected schema {payload.get('schema')!r}")
    graph = builder.Graph.from_payload(payload)
    graph.analyse()
    return graph, payload


def short(key: str) -> str:
    """Twelve informative hex digits of a key, for prose."""
    return key[8:20] if key.startswith(LEGACY_KEY_PREFIX) else key[:12]


def resolve_key(graph: builder.Graph, token: str) -> str:
    if token in graph.alias:  # the key of an unfolding merged into its named statement
        token = graph.canon(token)
    if token in graph.statements:
        return token
    matches = [k for k in graph.statements if k.startswith(token)]
    if not matches:
        matches = [k for k in graph.statements if k.startswith(LEGACY_KEY_PREFIX) and k[8:].startswith(token)]
    if len(matches) == 1:
        return matches[0]
    raise SystemExit(f"unknown statement key {token!r} ({len(matches)} prefix matches)")


def resolve_theorem(graph: builder.Graph, target: str) -> str | None:
    """The theorem a full or suffix name designates; ambiguity is an error."""
    if target in graph.theorems:
        return target
    candidates = sorted(n for n in graph.theorems if n.endswith("." + target))
    if len(candidates) > 1:
        raise SystemExit(f"ambiguous theorem name {target!r}: {len(candidates)} theorems end with it "
                         f"(for example {', '.join(candidates[:4])}); give the full name")
    return candidates[0] if candidates else None


def problems_of(payload: dict[str, Any]) -> dict[str, list[str]]:
    return {row["key"]: row.get("problems", []) for row in payload.get("statements", [])}


def own_problems_of(graph: builder.Graph, payload: dict[str, Any]) -> dict[str, list[str]]:
    """A statement's own attribution: the problems of the theorems that state
    it as a hypothesis or a conclusion, before any producer's problem is added."""
    rows = payload.get("statements", [])
    if rows and all("own_problems" in row for row in rows):
        return {row["key"]: row["own_problems"] for row in rows}
    out: dict[str, list[str]] = {}
    for key, node in graph.statements.items():
        problems = {graph.theorems.get(name, {}).get("card", {}).get("problem")
                    for name in node["consumers"] | node["conclusion_of"]}
        out[key] = sorted(p for p in problems if p)
    return out


def theorem_card(graph: builder.Graph, name: str) -> dict[str, Any]:
    theorem = graph.theorems.get(name, {})
    card = {"name": name}
    card.update(theorem.get("card", {}))
    return card


def refutation_view(graph: builder.Graph, key: str) -> dict[str, Any]:
    record = graph.refuted[key]
    if record["kind"] == "kernel":
        producer = record["producer"]
        return {"kind": "kernel", "reading": record["reading"],
                "refuted_by": producer if producer.startswith("tactic:") else theorem_card(graph, producer)}
    reaches = record["reaches"]
    if record["kind"] == "derived_conflict":
        return {"kind": "derived_conflict",
                "note": "supplying this statement would supply the statement below together with the residuals "
                        "of a recorded refutation of it",
                "reaches": {"key": reaches, "type": graph.statements.get(reaches, {}).get("type"),
                            "status": graph.status(reaches)},
                "refuted_by": record.get("refuted_by"), "via": record["producers"],
                "evidence_class": record.get("evidence_class")}
    return {"kind": "derived",
            "note": "supplying this statement would supply the refuted statement below",
            "reaches": {"key": reaches, "type": graph.statements.get(reaches, {}).get("type"),
                        "kind": graph.refuted.get(reaches, {}).get("kind")},
            "via": record["producers"]}


def statement_view(graph: builder.Graph, payload: dict[str, Any], key: str, *, depth: str = "full") -> dict[str, Any]:
    key = resolve_key(graph, key)
    node = graph.statements[key]
    status = graph.status(key)
    view: dict[str, Any] = {
        "key": key,
        "type": node.get("type"),
        "status": status,
        "problems": problems_of(payload).get(key, []),
        "consumed_by": [theorem_card(graph, n) for n in sorted(node["consumers"])[:20]],
        "consumer_count": len(node["consumers"]),
    }
    if status == "supplied":
        view["witness"] = graph.proof_tree(key, limit=4 if depth == "full" else 1)
        return view
    if status == "refuted":
        view["refutation"] = refutation_view(graph, key)
        view["note"] = "every theorem that assumes this statement is vacuous"
        return view
    reductions = graph.reduced_by_head.get(key, [])
    view["reductions"] = [
        {"producer": theorem_card(graph, producer), "reading": reading,
         "open_residuals": [{"key": r, "type": graph.statements.get(r, {}).get("type"), "status": graph.status(r)}
                            for r in left]}
        for (_, producer, reading, left) in reductions[:25]
    ]
    view["reduction_count"] = len(reductions)
    component = graph.component.get(key)
    if component is not None and len(graph.components[component]) >= 2:
        view["disguise_class"] = [
            {"key": m, "type": graph.statements[m].get("type")} for m in graph.components[component]]
    touching = ((payload.get("barriers") or {}).get("constrains") or {}).get(key, [])
    if touching:
        view["barriers_touching"] = touching[:12]
    gained = graph.leverage(key)
    view["leverage"] = {"count": len(gained),
                        "sample": [{"key": g, "type": graph.statements[g].get("type")} for g in sorted(gained)[:15]]}
    if depth == "full":
        bundles, truncated, checks = graph.bundle_report(key)
        view["bundles"] = [[{"key": b, "type": graph.statements[b].get("type")} for b in bundle]
                           for bundle in bundles]
        view["bundles_truncated"] = truncated
        if checks:
            view["bundle_checks"] = [builder.joint_check_row(check) for check in checks]
    return view


def git_lean_tree(root: Path) -> str | None:
    try:
        done = subprocess.run(["git", "-C", str(root), "rev-parse", "HEAD:lean"], capture_output=True,
                              text=True, timeout=30, env={**os.environ, "GIT_OPTIONAL_LOCKS": "0"})
    except (OSError, subprocess.SubprocessError):
        return None
    value = done.stdout.strip()
    return value if done.returncode == 0 and value else None


def freshness(payload: dict[str, Any], root: Path = ROOT) -> dict[str, Any]:
    """Whether the committed Lean sources differ from the ones the export ran on."""
    source = payload.get("source") or {}
    built = source.get("lean_tree")
    if built:
        current = git_lean_tree(root)
        state = "unknown" if current is None else ("current" if current == built else "stale")
        return {"state": state,
                "basis": "git tree of lean/ at the exported commit against HEAD:lean (uncommitted edits "
                         "are not compared)",
                "built_from": built, "current": current, "source_revision": source.get("source_revision")}
    fingerprint = source.get("lean_source_fingerprint")
    index = root / "docs" / "lean_dependency_index.json"
    current = json.loads(index.read_text(encoding="utf-8")).get("source_fingerprint") if index.is_file() else None
    if not fingerprint or not current:
        return {"state": "unknown", "basis": "no lean tree recorded", "built_from": fingerprint, "current": current}
    return {"state": "current" if fingerprint == current else "stale",
            "basis": "fallback: the dependency index fingerprint when the graph was built, which does not "
                     "identify the sources the export ran on",
            "built_from": fingerprint, "current": current}


def cmd_summary(graph: builder.Graph, payload: dict[str, Any], args: argparse.Namespace) -> Any:
    return {
        "freshness": freshness(payload),
        "source": payload.get("source"),
        "statements": len(graph.statements),
        "supplied": len(graph.supplied),
        "open": len(graph.open),
        "refuted": sum(1 for r in graph.refuted.values() if r["kind"] == "kernel"),
        "refuted_derived": sum(1 for r in graph.refuted.values() if r["kind"] == "derived"),
        "refuted_by_conflict": sum(1 for r in graph.refuted.values() if r["kind"] == "derived_conflict"),
        "supplied_and_refuted": len(graph.inconsistent),
        "kernel_checked_compositions_supplying": len(graph.composition_uses),
        "reductions": len(graph.reductions),
        "disguise_classes": len(graph.disguise_classes()),
        "largest_disguise_class": max((len(c) for c in graph.disguise_classes()), default=0),
        "existential_reductions": len(graph.existential),
        "budget_exhausted_attempts": len(graph.budget_exhausted),
        "idle_theorems": len(graph.idle),
        "idle_dropping_open": sum(1 for e in graph.idle if e.get("dropped_open_without_idle")),
    }


def open_for_problem(graph: builder.Graph, payload: dict[str, Any], problem: str) -> list[str]:
    owners = problems_of(payload)
    return [k for k in graph.open if problem in owners.get(k, [])]


def sinks_for(graph: builder.Graph, keys: list[str]) -> list[str]:
    sinks = []
    for key in keys:
        if not graph.reduced_by_head.get(key):
            continue
        component = graph.component.get(key)
        if not any(graph.component.get(s) != component for s in graph.implies.get(key, ())):
            sinks.append(key)
    sinks.sort(key=lambda k: (-len(graph.reduced_by_head.get(k, [])), graph.statements[k].get("type") or ""))
    return sinks


def cmd_problem(graph: builder.Graph, payload: dict[str, Any], args: argparse.Namespace) -> Any:
    keys = open_for_problem(graph, payload, args.number)
    owners = problems_of(payload)
    sinks = sinks_for(graph, keys)
    levered = sorted(keys, key=lambda k: (-len(graph.leverage(k)), k))
    classes = sorted({graph.component[k] for k in keys if graph.component.get(k) is not None
                      and len(graph.components[graph.component[k]]) >= 2},
                     key=lambda c: -len(graph.components[c]))
    return {
        "problem": args.number,
        "open_statements": len(keys),
        "refuted_statements": sum(1 for k in graph.refuted if args.number in owners.get(k, [])),
        "sinks": [statement_view(graph, payload, k, depth="brief") for k in sinks[: args.limit]],
        "disguise_classes": [
            [{"key": m, "type": graph.statements[m].get("type")} for m in graph.components[c]]
            for c in classes[: args.limit]],
        "highest_leverage": [
            {"key": k, "type": graph.statements[k].get("type"), "leverage": len(graph.leverage(k))}
            for k in levered[: args.limit]],
    }


def statement_text(node: dict[str, Any]) -> str:
    return " ".join([node.get("type") or "", *sorted(node.get("aliases", ())),
                     *sorted(node.get("constants", ()))]).lower()


STATUS_ORDER = {"open": 0, "refuted": 1, "supplied": 2}


def cmd_find(graph: builder.Graph, payload: dict[str, Any], args: argparse.Namespace) -> Any:
    words = [w for w in args.text.lower().split() if w]
    hits = [(k, n) for k, n in graph.statements.items()
            if all(w in statement_text(n) for w in words)]
    hits.sort(key=lambda kn: (STATUS_ORDER[graph.status(kn[0])], len(kn[1].get("type") or "")))
    return [{"key": k, "status": graph.status(k), "type": n.get("type")}
            for k, n in hits[: args.limit]]


def cmd_statement(graph: builder.Graph, payload: dict[str, Any], args: argparse.Namespace) -> Any:
    return statement_view(graph, payload, args.key)


def cmd_theorem(graph: builder.Graph, payload: dict[str, Any], args: argparse.Namespace) -> Any:
    name = resolve_theorem(graph, args.name)
    if name is None:
        raise SystemExit(f"unknown theorem {args.name!r}")
    theorem = graph.theorems[name]
    conclusion = theorem.get("conclusion_key")
    idle = next((e for e in graph.idle if e.get("theorem") == name), None)
    view = {
        **theorem_card(graph, name),
        "module": theorem.get("module"),
        "kernel_status": builder.kernel_status(graph, name),
        "hypotheses": [
            {"key": h, "type": graph.statements.get(h, {}).get("type"), "status": graph.status(h)}
            for h in theorem.get("hypotheses", [])],
        "schematic_hypotheses": theorem.get("schematic_hypotheses", []),
        "witness_obligations": theorem.get("witness_obligations", []),
        "conclusion": {"key": conclusion, "type": theorem.get("conclusion_type"),
                       "status": graph.status(conclusion) if conclusion else "schematic"},
    }
    if idle:
        view["idle"] = {"stronger_statement": idle.get("type"), "dropped": idle.get("dropped", []),
                        "kernel_status_after_idle": builder.kernel_status(graph, name, after_idle=True)}
    weakened = [row for row in weakening_rows(graph) if row["name"] == name]
    if weakened:
        view["weakenings"] = weakened
    return view


def cmd_why(graph: builder.Graph, payload: dict[str, Any], args: argparse.Namespace) -> Any:
    view = statement_view(graph, payload, args.key, depth="brief")
    if view["status"] == "refuted":
        return {"key": view["key"], "status": "refuted", "refutation": view["refutation"]}
    if view["status"] != "supplied":
        return {"key": view["key"], "status": "open", "note": "no witness chain in the export"}
    return graph.proof_tree(view["key"], limit=args.depth)


def cmd_barriers(graph: builder.Graph, payload: dict[str, Any], args: argparse.Namespace) -> Any:
    entries = (payload.get("barriers") or {}).get("entries", [])
    if args.problem:
        entries = [e for e in entries if e["problem"] == args.problem]
    entries = sorted(entries, key=lambda e: (-e["open_statements_touched"], e["id"]))
    return {"count": len(entries), "in_graph": sum(1 for e in entries if e["in_graph"]),
            "entries": entries[: args.limit]}


def idle_rows(graph: builder.Graph, problem: str | None = None) -> list[dict[str, Any]]:
    rows = []
    for entry in graph.idle:
        card = theorem_card(graph, entry.get("theorem"))
        if problem and card.get("problem") != problem:
            continue
        open_dropped = set(entry.get("dropped_open_without_idle", []))
        rows.append({**card, "stronger_statement": entry.get("type"),
                     "dropped": [{"type": d.get("type"), "key": d.get("key"),
                                  "open_without_idle": d.get("key") in open_dropped}
                                 for d in entry.get("dropped", [])],
                     "reduction": entry.get("reduction"), "reason_without_reduction": entry.get("reason")})
    rows.sort(key=lambda r: (not r.get("papers"), not any(d["open_without_idle"] for d in r["dropped"]),
                             r["name"]))
    return rows


def weakening_rows(graph: builder.Graph, problem: str | None = None) -> list[dict[str, Any]]:
    """Theorems whose proofs use a closed hypothesis only through what they
    derive from it, with the status of the hypothesis and of each consequence.
    The kernel accepted each weakened theorem and each implication."""
    rows = []
    for entry in graph.weakenings:
        card = theorem_card(graph, entry.get("theorem"))
        if problem and card.get("problem") != problem:
            continue
        hypothesis = entry.get("hypothesis")
        conclusion = entry.get("conclusion")
        uses = [{"key": c["key"], "type": c.get("type"), "status": graph.status(c["key"]),
                 "via": c.get("via", []), "sites": c.get("sites", [])} for c in entry.get("consequences", [])]
        rows.append({**card,
                     "hypothesis": {"key": hypothesis, "type": entry.get("hypothesis_type"),
                                    "status": graph.status(hypothesis) if hypothesis else None},
                     "uses_only": uses,
                     "weakened_theorem": entry.get("weakened"),
                     "weakened_statement": entry.get("type"),
                     "conclusion": {"key": conclusion, "status": graph.status(conclusion) if conclusion else None},
                     "reduction": entry.get("reduction"), "reason_without_reduction": entry.get("reason")})
    rows.sort(key=lambda r: (r["hypothesis"]["status"] != "open",
                             not all(u["status"] == "supplied" for u in r["uses_only"]),
                             not r.get("papers"), r["name"]))
    return rows


def status_after_weakening(graph: builder.Graph, name: str) -> str | None:
    """The theorem's status when each hypothesis it weakens counts as supplied
    once every consequence the proof uses of it is supplied: the kernel
    accepted the weakened theorem, so those consequences suffice."""
    theorem = graph.theorems.get(name)
    if theorem is None:
        return None
    covered = {e.get("hypothesis") for e in graph.weakenings if e.get("theorem") == name
               and all(c["key"] in graph.supplied for c in e.get("consequences", []))}
    closed = [h for h in theorem.get("hypotheses", []) if h not in covered]
    if any(k in graph.refuted for k in closed):
        return "conditional_on_refuted"
    if any(k not in graph.supplied for k in closed):
        return "conditional_on_open"
    if theorem.get("schematic_hypotheses") or theorem.get("witness_obligations"):
        return "conditional_on_schematic"
    return "conditional_on_supplied" if theorem.get("hypotheses") else "unconditional"


# The order in which a paper result's declarations decide its row: the most
# conditional status wins.
PAPER_STATUS_ORDER = ("conditional_on_refuted", "conditional_on_open", "conditional_on_schematic",
                      "conditional_on_supplied", "unconditional")


def cmd_papers(graph: builder.Graph, payload: dict[str, Any], args: argparse.Namespace) -> Any:
    """Every paper result the paper-to-Lean ledger joins to a theorem of the
    graph, with what the graph says about that theorem: unconditional;
    conditional only on statements the graph supplies (so a chain of corpus
    theorems closes it); conditional on an open, schematic or refuted
    hypothesis; and any hypothesis its proof never uses. The ledger status and
    the Comparator status travel with each row."""
    idle_by_theorem = {row["theorem"]: row for row in payload.get("idle", []) if row.get("kernel_checked", True)}
    rows: dict[str, dict[str, Any]] = {}
    for name, theorem in sorted(graph.theorems.items()):
        for paper in (theorem.get("card") or {}).get("papers", []):
            if args.problem and str(paper.get("problem")) != str(args.problem):
                continue
            if args.paper and args.paper not in (paper.get("paper") or ""):
                continue
            entry = rows.setdefault(paper["row"], {
                "row": paper["row"], "paper": paper.get("paper"), "side": paper.get("side"),
                "label": paper.get("label"), "lean_status": paper.get("lean_status"),
                "comparator": paper.get("comparator"), "declarations": []})
            status = builder.kernel_status(graph, name)
            after_idle = builder.kernel_status(graph, name, after_idle=True)
            declaration: dict[str, Any] = {"name": name, "status": status}
            if after_idle != status:
                declaration["status_after_idle"] = after_idle
            open_hypotheses = [h for h in theorem.get("hypotheses", []) if h not in graph.supplied]
            if open_hypotheses:
                declaration["open_or_refuted_hypotheses"] = [
                    {"key": h, "type": graph.statements.get(h, {}).get("type"), "status": graph.status(h)}
                    for h in open_hypotheses[:6]]
            if name in idle_by_theorem:
                declaration["idle_hypotheses"] = [d.get("type") for d in idle_by_theorem[name].get("dropped", [])]
            weakened = [e for e in graph.weakenings if e.get("theorem") == name]
            if weakened:
                declaration["uses_only"] = [
                    {"hypothesis": e.get("hypothesis_type"), "hypothesis_status": graph.status(e["hypothesis"])
                     if e.get("hypothesis") else None,
                     "consequences": [{"type": c.get("type"), "status": graph.status(c["key"]),
                                       "via": c.get("via", [])} for c in e.get("consequences", [])]}
                    for e in weakened]
                after = status_after_weakening(graph, name)
                if after != status and PAPER_STATUS_ORDER.index(after) > PAPER_STATUS_ORDER.index(
                        declaration.get("status_after_idle", status)):
                    declaration["status_after_weakening"] = after
            entry["declarations"].append(declaration)
    counts: dict[str, int] = defaultdict(int)
    for entry in rows.values():
        statuses = {d.get("status_after_weakening", d.get("status_after_idle", d["status"]))
                    for d in entry["declarations"]}
        entry["status"] = next((s for s in PAPER_STATUS_ORDER if s in statuses), "unconditional")
        counts[entry["status"]] += 1
    notable = [e for e in rows.values()
               if e["status"] in ("conditional_on_refuted", "conditional_on_supplied")
               or any("idle_hypotheses" in d or "status_after_idle" in d or "uses_only" in d
                      for d in e["declarations"])]
    notable.sort(key=lambda e: (PAPER_STATUS_ORDER.index(e["status"]), e["row"]))
    return {
        "rule": "a row takes the most conditional status among its declarations; conditional_on_supplied means "
                "every closed hypothesis has a witness chain in the graph; idle hypotheses and weakenings "
                "(uses_only: what the proof derives from a hypothesis) are kernel-checked, and a declaration's "
                "status after either is the one that counts",
        "paper_results_in_graph": len(rows),
        "by_status": dict(sorted(counts.items())),
        "notable": notable[: args.limit],
    }


def cmd_idle(graph: builder.Graph, payload: dict[str, Any], args: argparse.Namespace) -> Any:
    """Theorems whose proofs never use some proposition binders; the kernel
    accepted each stronger statement. Paper-cited ones first, then those that
    drop a statement open in the graph without the idle rows."""
    rows = idle_rows(graph, args.problem)
    return {"count": len(rows),
            "dropping_open": sum(1 for r in rows if any(d["open_without_idle"] for d in r["dropped"])),
            "rows": rows[: args.limit]}


def cmd_weakenings(graph: builder.Graph, payload: dict[str, Any], args: argparse.Namespace) -> Any:
    """Theorems whose proofs use a closed hypothesis only through what they
    derive from it: open hypotheses first, then those whose consequences the
    graph supplies (the conclusion then holds without the hypothesis)."""
    rows = weakening_rows(graph, args.problem)
    return {"count": len(rows),
            "of_open_hypotheses": sum(1 for r in rows if r["hypothesis"]["status"] == "open"),
            "consequences_all_supplied": sum(1 for r in rows if all(u["status"] == "supplied"
                                                                    for u in r["uses_only"])),
            "rows": rows[: args.limit]}


def cmd_next(graph: builder.Graph, payload: dict[str, Any], args: argparse.Namespace) -> Any:
    """A shortlist of open statements worth attacking next, each with its reasons.

    Structural only: it excludes what is supplied or refuted, the problem's own
    targets restated (members of a sink's disguise class) and statements that
    settle nothing, and prefers members of bundles with two or more open
    statements (no recorded reduction supplies the target from such a member
    alone), statements no barrier touches, and statements serving more than one
    problem. Whether a candidate is worth a mathematician's time stays a
    judgement."""
    keys = open_for_problem(graph, payload, args.problem)
    sinks = sinks_for(graph, keys)
    target_classes = {graph.component.get(s) for s in sinks}
    touched = ((payload.get("barriers") or {}).get("constrains") or {})
    owners = problems_of(payload)
    served_by_bundle: dict[str, set[str]] = defaultdict(set)
    for sink in sinks[: args.sinks]:
        for bundle in graph.bundles(sink)[0]:
            if len(bundle) >= 2:
                for member in bundle:
                    served_by_bundle[member].add(sink)
    rows = []
    for key in keys:
        if key in graph.refuted or graph.component.get(key) in target_classes:
            continue
        gained = graph.leverage(key)
        if not gained and key not in served_by_bundle:
            continue
        reasons = []
        if key in served_by_bundle:
            reasons.append(f"member of a two-or-more bundle for {len(served_by_bundle[key])} target(s)")
        if gained:
            reasons.append(f"settles {len(gained)} open statement(s)")
        if key in touched:
            reasons.append(f"touched by barrier(s) {', '.join(touched[key][:3])}: check them first")
        else:
            reasons.append("no recorded barrier touches it")
        problems = owners.get(key, [])
        if len(problems) > 1:
            reasons.append(f"serves problems {', '.join(problems)}")
        score = (key in served_by_bundle, key not in touched, len(problems), len(gained))
        rows.append((score, key, reasons))
    rows.sort(key=lambda row: row[0], reverse=True)
    return {
        "problem": args.problem,
        "rule": "exclude supplied, refuted, target-restating and consequence-free statements; prefer bundle members, "
                "unbarriered statements, cross-problem statements, then leverage",
        "shortlist": [{"key": key, "type": graph.statements[key].get("type"), "reasons": reasons}
                      for _, key, reasons in rows[: args.limit]],
    }


def cmd_check_bundle(graph: builder.Graph, payload: dict[str, Any], args: argparse.Namespace) -> Any:
    """Whether the given statements, assumed together, are jointly impossible
    over the recorded edges, and whether they supply and restate a target."""
    keys = [resolve_key(graph, k) for k in args.keys]
    target = resolve_key(graph, args.target) if args.target else None
    return graph.frontier().check(keys, target=target, max_work=args.max_work)


def cmd_cut(graph: builder.Graph, payload: dict[str, Any], args: argparse.Namespace) -> Any:
    """The cheapest set of statements from a pool with costs (a JSON object of
    statement keys to integers or rational strings, at most 32) that supplies
    the target without a recorded conflict; a statement is paid for once."""
    target = resolve_key(graph, args.target)
    raw = json.loads(args.costs.read_text(encoding="utf-8"))
    if not isinstance(raw, dict):
        raise SystemExit("--costs must hold a JSON object mapping statement keys to costs")
    costs = {resolve_key(graph, k): v for k, v in raw.items()}
    try:
        return graph.frontier().cheapest_cut(target, costs, max_states=args.max_states, max_work=args.max_work,
                                             exclude_equivalent=args.exclude_equivalent)
    except ValueError as error:
        raise SystemExit(str(error)) from error


def cmd_near(graph: builder.Graph, payload: dict[str, Any], args: argparse.Namespace) -> Any:
    """Statements that share the most corpus objects with a proposed statement:
    the kernel facts to read before formulating a new lemma."""
    words = [w for w in args.text.replace("(", " ").replace(")", " ").split() if w]
    constants: set[str] = set()
    universe = {c for n in graph.statements.values() for c in n.get("constants", ())}
    for word in words:
        constants |= {c for c in universe if c == word or c.endswith("." + word)}
    if not constants:
        return {"query": args.text, "note": "no corpus constant matches a word of the query"}
    scored = []
    for key, node in graph.statements.items():
        mine = set(node.get("constants", ()))
        shared = mine & constants
        if shared:
            scored.append((len(shared) / len(mine | constants), key, sorted(shared)))
    scored.sort(key=lambda row: (-row[0], row[1]))

    def rows(status: str) -> list[dict[str, Any]]:
        out = []
        for score, key, shared in scored:
            if graph.status(key) != status:
                continue
            out.append({"key": key, "overlap": round(score, 3), "shared": shared,
                        "type": graph.statements[key].get("type")})
            if len(out) >= args.limit:
                break
        return out
    return {"query_constants": sorted(constants), "supplied": rows("supplied"), "open": rows("open"),
            "refuted": rows("refuted")}


def cmd_about(graph: builder.Graph, payload: dict[str, Any], args: argparse.Namespace) -> Any:
    name = args.constant
    hits = [k for k, n in graph.statements.items()
            if any(c == name or c.endswith("." + name) for c in n.get("constants", ()))]
    supplied = sorted((k for k in hits if k in graph.supplied), key=lambda k: len(graph.statements[k].get("type") or ""))
    refuted = sorted((k for k in hits if k in graph.refuted), key=lambda k: len(graph.statements[k].get("type") or ""))
    open_ = sorted((k for k in hits if k in graph.open), key=lambda k: -len(graph.leverage(k)))
    return {
        "constant": name,
        "supplied_count": len(supplied),
        "open_count": len(open_),
        "refuted_count": len(refuted),
        "supplied": [{"key": k, "type": graph.statements[k].get("type"),
                      "witness": graph.reductions[graph.witness[k]][1] if graph.witness.get(k, -1) >= 0 else None}
                     for k in supplied[: args.limit]],
        "open": [{"key": k, "type": graph.statements[k].get("type"),
                  "reductions": len(graph.reduced_by_head.get(k, [])), "leverage": len(graph.leverage(k))}
                 for k in open_[: args.limit]],
        "refuted": [{"key": k, "type": graph.statements[k].get("type"), "kind": graph.refuted[k]["kind"]}
                    for k in refuted[: args.limit]],
    }


def cmd_criticality(graph: builder.Graph, payload: dict[str, Any], args: argparse.Namespace) -> Any:
    name = resolve_theorem(graph, args.target)
    if name is not None:
        lost = graph.criticality(producer=name)
        subject: dict[str, Any] = {"theorem": name}
    else:
        key = resolve_key(graph, args.target)
        lost = graph.criticality(statement=key)
        subject = {"statement": key, "type": graph.statements[key].get("type")}
    return {**subject, "loses_every_witness_chain": len(lost),
            "sample": [{"key": k, "type": graph.statements[k].get("type")} for k in sorted(lost)[: args.limit]]}


def cmd_transfer(graph: builder.Graph, payload: dict[str, Any], args: argparse.Namespace) -> Any:
    """Reductions whose producer is attributed to one problem while the
    statement it supplies is stated only by theorems of other problems (the
    statement's own attribution, before producers' problems are added)."""
    own = own_problems_of(graph, payload)
    rows = []
    for head, producer, reading, residuals in graph.reductions:
        producer_problem = graph.theorems.get(producer, {}).get("card", {}).get("problem")
        if not producer_problem or producer_problem in ("cross", "249_257"):
            continue
        head_problems = set(own.get(head, []))
        if not head_problems or "cross" in head_problems:
            continue
        if "249_257" in head_problems:
            head_problems |= {"249", "257"}
        if producer_problem in head_problems:
            continue
        rows.append({"producer": producer, "producer_problem": producer_problem,
                     "supplies": head, "type": graph.statements.get(head, {}).get("type"),
                     "statement_problems": sorted(own.get(head, [])), "reading": reading,
                     "status": graph.status(head),
                     "open_residuals": [r for r in residuals if r not in graph.supplied]})
    rows.sort(key=lambda r: (r["producer_problem"], r["producer"]))
    return {"cross_problem_reductions": len(rows), "rows": rows[: args.limit]}


def cmd_diff(graph: builder.Graph, payload: dict[str, Any], args: argparse.Namespace) -> Any:
    old_graph, _ = load(args.old)
    new_graph, _ = load(args.new)
    newly_supplied = sorted(new_graph.supplied - old_graph.supplied)
    lost = sorted(old_graph.supplied - new_graph.supplied)
    newly_refuted = sorted(set(new_graph.refuted) - set(old_graph.refuted))
    added = sorted(set(new_graph.statements) - set(old_graph.statements))
    old_classes = {frozenset(c) for c in old_graph.disguise_classes()}
    new_classes = [c for c in new_graph.disguise_classes() if frozenset(c) not in old_classes]

    def rows(graph_: builder.Graph, keys: list[str]) -> list[dict[str, Any]]:
        return [{"key": k, "type": graph_.statements[k].get("type")} for k in keys[: args.limit]]
    return {"newly_supplied": len(newly_supplied), "newly_supplied_sample": rows(new_graph, newly_supplied),
            "no_longer_supplied": len(lost), "no_longer_supplied_sample": rows(old_graph, lost),
            "newly_refuted": len(newly_refuted), "newly_refuted_sample": rows(new_graph, newly_refuted),
            "new_statements": len(added), "new_disguise_classes": len(new_classes)}


def packet_markdown(graph: builder.Graph, payload: dict[str, Any], problem: str, limit: int) -> str:
    keys = open_for_problem(graph, payload, problem)
    owners = problems_of(payload)
    sinks = sinks_for(graph, keys)
    source = payload.get("source", {})
    lines = [
        f"# Argument frontier for Erdős #{problem}",
        "",
        f"Generated from the kernel export `{source.get('export_digest', '?')}` "
        f"(Lean {source.get('lean_version', '?')}). Every row cites corpus theorems; "
        "`open` means no chain of corpus theorems found by the export supplies or refutes the statement "
        "(the producer relation is a lower bound). Lean is the proof authority, not this packet.",
        "",
        f"Open statements attributed to #{problem}: {len(keys)}. Open targets (sinks): {len(sinks)}.",
        "",
        "## 1. Open targets",
        "",
    ]

    def paper_note(name: str) -> str:
        card = theorem_card(graph, name)
        notes = []
        for row in card.get("papers", [])[:3]:
            notes.append(f"{row.get('side')} paper `{row.get('label')}` ({row.get('source')}, "
                         f"Comparator: {row.get('comparator') or 'n/a'})")
        if card.get("source"):
            notes.insert(0, f"`{card['source']}`")
        return "; ".join(notes)

    def depending_results(key: str) -> list[str]:
        """Paper results whose Lean declarations take this statement as a hypothesis."""
        out = []
        for name in sorted(graph.statements[key]["consumers"]):
            for row in theorem_card(graph, name).get("papers", [])[:2]:
                out.append(f"{row.get('side')} `{row.get('label')}` ({row.get('source')}; "
                           f"Comparator: {row.get('comparator') or 'n/a'})")
        return out[:6]

    def residual_text(r: str) -> str:
        status = graph.status(r)
        marker = " (refuted: this route is dead)" if status == "refuted" else ""
        return f"`{short(r)}` {graph.statements.get(r, {}).get('type')}{marker}"

    for key in sinks[:limit]:
        node = graph.statements[key]
        lines.append(f"### `{short(key)}` {node.get('type')}")
        results = depending_results(key)
        if results:
            lines.append("Paper results that assume it: " + "; ".join(results) + ".")
        if node.get("aliases"):
            lines.append("Also stated as: " + "; ".join(sorted(node["aliases"])[:3]) + ".")
        reductions = graph.reduced_by_head.get(key, [])
        lines.append(f"Reductions into it: {len(reductions)}.")
        for (_, producer, reading, left) in reductions[:8]:
            leaves = "; ".join(residual_text(r) for r in left) or "(none)"
            lines.append(f"- `{producer}` ({reading}) {paper_note(producer)} leaves: {leaves}")
        bundles, truncated = graph.bundles(key)
        if bundles:
            lines.append("Minimal bundles (supply every member of one bundle to close it):")
            for bundle in bundles[:10]:
                lines.append("- " + " AND ".join(f"`{short(b)}`" for b in bundle))
        if truncated:
            lines.append("- (bundle enumeration hit a limit; more bundles may exist)")
        component = graph.component.get(key)
        if component is not None and len(graph.components[component]) >= 2:
            lines.append(f"Disguise class: {len(graph.components[component])} statements equivalent through "
                         "recorded reductions (see section 2). Moving between them is not progress.")
        lines.append("")

    lines += ["## 2. Disguise classes: the same statement in other coordinates", ""]
    classes = sorted({graph.component[k] for k in keys if graph.component.get(k) is not None
                      and len(graph.components[graph.component[k]]) >= 2},
                     key=lambda c: -len(graph.components[c]))
    if not classes:
        lines.append("None found among this problem's open statements.")
    for c in classes[:limit]:
        members = graph.components[c]
        lines.append(f"### Class of {len(members)}")
        for m in members[:20]:
            lines.append(f"- `{short(m)}` {graph.statements[m].get('type')}")
        lines.append("")

    lines += ["## 3. Partial progress: members of bundles of size two or more", "",
              "Supplying one member of such a bundle leaves a smaller open bundle for the target. The graph "
              "records no reduction by which that member alone supplies the target, and it records nothing "
              "about whether the target implies the member.", ""]
    seen: set[str] = set()
    for key in sinks[:limit]:
        bundles, _ = graph.bundles(key)
        for bundle in bundles:
            if len(bundle) < 2:
                continue
            for member in bundle:
                if member in seen:
                    continue
                seen.add(member)
                lines.append(f"- `{short(member)}` {graph.statements[member].get('type')} "
                             f"(leverage {len(graph.leverage(member))}; serves `{short(key)}`)")
    if not seen:
        lines.append("None: every recorded route to these targets is a single open statement.")
    lines.append("")

    problem_barriers = [e for e in (payload.get("barriers") or {}).get("entries", []) if e["problem"] == problem]
    if problem_barriers:
        lines += ["## Barriers: argument classes already ruled out", "",
                  "Each is a Lean declaration (kernel-checked when `in graph`); what it rules out is an "
                  "authored reading, and a barrier may rule out a narrower class than a specialist would try.", ""]
        for e in sorted(problem_barriers, key=lambda e: -e["open_statements_touched"])[:limit * 2]:
            lane = "in graph" if e["in_graph"] else (e.get("build_lane") or "outside graph")
            lines.append(f"- **{e['kind']}** `{e.get('declaration') or e['id']}` ({lane}): {e.get('blocks')}")
        lines.append("")

    refuted = sorted(k for k in graph.refuted if problem in owners.get(k, []))
    if refuted:
        lines += ["## Refuted statements: routes that are closed", "",
                  "A corpus theorem or a kernel-checked battery proof establishes the negation (kernel), or "
                  "supplying the statement would supply a refuted one (derived). Every theorem that assumes one "
                  "of these is vacuous.", ""]
        for key in refuted[:limit * 2]:
            record = graph.refuted[key]
            if record["kind"] == "kernel":
                how = f"kernel: `{record['producer']}` ({record['reading']})"
            else:
                how = f"derived: reaches `{short(record['reaches'])}` via " + ", ".join(
                    f"`{p}`" for p in record["producers"][:3])
            lines.append(f"- `{short(key)}` {graph.statements[key].get('type')} ({how})")
        lines.append("")

    unused = [r for r in idle_rows(graph, problem) if any(d["open_without_idle"] for d in r["dropped"])]
    if unused:
        lines += ["## Hypotheses the proofs never use", "",
                  "Each theorem below assumes an open statement its proof never uses; the kernel accepted the "
                  "statement without it.", ""]
        for row in unused[:limit]:
            dropped = "; ".join(d["type"] or "?" for d in row["dropped"] if d["open_without_idle"])
            lines.append(f"- `{row['name']}` drops {dropped}: {row['stronger_statement']}")
        lines.append("")

    weakened = [r for r in weakening_rows(graph, problem) if r["hypothesis"]["status"] == "open"]
    if weakened:
        lines += ["## What the proofs use of their open inputs", "",
                  "Each theorem below assumes an open statement but its proof uses only the consequences listed "
                  "(through the lemmas named); the kernel accepted the theorem with the input replaced by them. "
                  "A consequence is a weaker target than the input it comes from.", ""]
        for row in weakened[:limit * 2]:
            uses = "; ".join(f"`{short(u['key'])}` {u['type']} ({u['status']}, via "
                             + ", ".join(f"`{v}`" for v in u["via"][:2]) + ")" for u in row["uses_only"])
            lines.append(f"- `{row['name']}` assumes {row['hypothesis']['type']} and uses only: {uses}")
        lines.append("")

    lines += ["## 4. Highest leverage open statements", ""]
    levered = sorted(keys, key=lambda k: (-len(graph.leverage(k)), k))
    for key in levered[:limit]:
        gained = graph.leverage(key)
        if not gained:
            break
        lines.append(f"- `{short(key)}` {graph.statements[key].get('type')}: supplies {len(gained)} open statements")
    lines.append("")
    text = "\n".join(lines)
    if len(text.encode("utf-8")) > PACKET_BYTE_BUDGET:
        text = text.encode("utf-8")[:PACKET_BYTE_BUDGET].decode("utf-8", "ignore") + "\n\n(truncated at the packet budget)\n"
    return text


def cmd_packet(graph: builder.Graph, payload: dict[str, Any], args: argparse.Namespace) -> Any:
    return packet_markdown(graph, payload, args.problem, args.limit)


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--graph", type=Path, default=DEFAULT_GRAPH)
    sub = parser.add_subparsers(dest="command", required=True)
    sub.add_parser("summary")
    p = sub.add_parser("problem"); p.add_argument("number"); p.add_argument("--limit", type=int, default=15)
    p = sub.add_parser("find"); p.add_argument("text"); p.add_argument("--limit", type=int, default=30)
    p = sub.add_parser("statement"); p.add_argument("key")
    p = sub.add_parser("theorem"); p.add_argument("name")
    p = sub.add_parser("why"); p.add_argument("key"); p.add_argument("--depth", type=int, default=6)
    p = sub.add_parser("about"); p.add_argument("constant"); p.add_argument("--limit", type=int, default=30)
    p = sub.add_parser("near"); p.add_argument("text"); p.add_argument("--limit", type=int, default=12)
    p = sub.add_parser("next"); p.add_argument("--problem", required=True)
    p.add_argument("--limit", type=int, default=15); p.add_argument("--sinks", type=int, default=12)
    p = sub.add_parser("barriers"); p.add_argument("--problem"); p.add_argument("--limit", type=int, default=40)
    p = sub.add_parser("idle"); p.add_argument("--problem"); p.add_argument("--limit", type=int, default=40)
    p = sub.add_parser("weakenings"); p.add_argument("--problem"); p.add_argument("--limit", type=int, default=40)
    p = sub.add_parser("papers"); p.add_argument("--problem"); p.add_argument("--paper")
    p.add_argument("--limit", type=int, default=40)
    p = sub.add_parser("criticality"); p.add_argument("target"); p.add_argument("--limit", type=int, default=30)
    p = sub.add_parser("transfer"); p.add_argument("--limit", type=int, default=60)
    p = sub.add_parser("diff"); p.add_argument("old", type=Path); p.add_argument("new", type=Path)
    p.add_argument("--limit", type=int, default=30)
    p = sub.add_parser("packet"); p.add_argument("--problem", required=True); p.add_argument("--limit", type=int, default=12)
    p = sub.add_parser("check-bundle"); p.add_argument("keys", nargs="+"); p.add_argument("--target")
    p.add_argument("--max-work", type=int, default=frontier_module.CHECK_WORK_LIMIT,
                   help="propagation steps before the answer reads unknown_budget")
    p = sub.add_parser("cut"); p.add_argument("target")
    p.add_argument("--costs", type=Path, required=True,
                   help="JSON object: statement key (or unique prefix) -> integer or rational-string cost")
    p.add_argument("--max-states", type=int, default=10_000)
    p.add_argument("--max-work", type=int, default=5_000_000)
    p.add_argument("--exclude-equivalent", action="store_true",
                   help="skip sets the target implies member by member (restatements of the target)")
    args = parser.parse_args(argv)
    graph, payload = load(args.graph)
    handler = {"summary": cmd_summary, "problem": cmd_problem, "find": cmd_find, "statement": cmd_statement,
               "theorem": cmd_theorem, "why": cmd_why, "about": cmd_about, "near": cmd_near, "next": cmd_next,
               "barriers": cmd_barriers, "idle": cmd_idle, "weakenings": cmd_weakenings, "papers": cmd_papers,
               "criticality": cmd_criticality, "check-bundle": cmd_check_bundle, "cut": cmd_cut,
               "transfer": cmd_transfer, "diff": cmd_diff, "packet": cmd_packet}[args.command]
    result = handler(graph, payload, args)
    if isinstance(result, str):
        sys.stdout.write(result)
    else:
        print(json.dumps(result, indent=1, ensure_ascii=False))
    return 0


if __name__ == "__main__":
    sys.exit(main())
