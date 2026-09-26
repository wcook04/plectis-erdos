#!/usr/bin/env python3
"""Query the kernel argument graph.

Reads ``docs/argument_continuations_graph.json.gz`` (built by
``scripts/build_argument_continuations.py`` from the kernel export) and answers
the questions a researcher asks before spending effort on a statement:

    summary                     graph totals and the export's own boundary
    problem N                   open targets, disguise classes, leverage for one problem
    find TEXT                   statements whose Lean rendering contains TEXT
    statement KEY               one statement: status, kernel witness or reductions,
                                bundles, leverage, disguise class, consumers, papers
    theorem NAME                one theorem: hypotheses (with status), conclusion, papers
    why KEY                     the kernel witness chain of a supplied statement
    about CONSTANT              everything the graph holds about one corpus object
    criticality KEY|THEOREM     what loses its kernel witness chain without it
    transfer                    reductions where a theorem attributed to one problem
                                supplies a statement attributed only to others
    diff OLD NEW                how the frontier moved between two graph files
    packet --problem N          a bounded Markdown research packet for one problem

Every answer cites kernel theorems. "Open" means no chain of corpus theorems
found by the export supplies the statement; the producer relation is a lower
bound, so an open statement may still follow from an argument the export did
not try. Nothing here is proof authority.
"""

from __future__ import annotations

import argparse
import gzip
import json
import sys
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))

import build_argument_continuations as builder  # noqa: E402

DEFAULT_GRAPH = ROOT / "docs" / "argument_continuations_graph.json.gz"
PACKET_BYTE_BUDGET = 150_000


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


def problems_of(payload: dict[str, Any]) -> dict[str, list[str]]:
    return {row["key"]: row.get("problems", []) for row in payload.get("statements", [])}


def theorem_card(graph: builder.Graph, name: str) -> dict[str, Any]:
    theorem = graph.theorems.get(name, {})
    card = {"name": name}
    card.update(theorem.get("card", {}))
    return card


def statement_view(graph: builder.Graph, payload: dict[str, Any], key: str, *, depth: str = "full") -> dict[str, Any]:
    if key not in graph.statements:
        matches = [k for k in graph.statements if k.startswith(key)]
        if len(matches) == 1:
            key = matches[0]
        else:
            raise SystemExit(f"unknown statement key {key!r} ({len(matches)} prefix matches)")
    node = graph.statements[key]
    view: dict[str, Any] = {
        "key": key,
        "type": node.get("type"),
        "status": "supplied" if key in graph.supplied else "open",
        "problems": problems_of(payload).get(key, []),
        "consumed_by": [theorem_card(graph, n) for n in sorted(node["consumers"])[:20]],
        "consumer_count": len(node["consumers"]),
    }
    if key in graph.supplied:
        view["witness"] = graph.proof_tree(key, limit=4 if depth == "full" else 1)
        return view
    reductions = graph.reduced_by_head.get(key, [])
    view["reductions"] = [
        {"producer": theorem_card(graph, producer), "reading": reading,
         "open_residuals": [{"key": r, "type": graph.statements.get(r, {}).get("type")} for r in left]}
        for (_, producer, reading, left) in reductions[:25]
    ]
    view["reduction_count"] = len(reductions)
    component = graph.component.get(key)
    if component is not None and len(graph.components[component]) >= 2:
        view["disguise_class"] = [
            {"key": m, "type": graph.statements[m].get("type")} for m in graph.components[component]]
    gained = graph.leverage(key)
    view["leverage"] = {"count": len(gained),
                        "sample": [{"key": g, "type": graph.statements[g].get("type")} for g in sorted(gained)[:15]]}
    if depth == "full":
        bundles, truncated = graph.bundles(key)
        view["bundles"] = [[{"key": b, "type": graph.statements[b].get("type")} for b in bundle]
                           for bundle in bundles]
        view["bundles_truncated"] = truncated
    return view


def cmd_summary(graph: builder.Graph, payload: dict[str, Any], args: argparse.Namespace) -> Any:
    return {
        "source": payload.get("source"),
        "statements": len(graph.statements),
        "supplied": len(graph.supplied),
        "open": len(graph.open),
        "reductions": len(graph.reductions),
        "disguise_classes": len(graph.disguise_classes()),
        "largest_disguise_class": max((len(c) for c in graph.disguise_classes()), default=0),
        "existential_reductions": len(graph.existential),
        "budget_exhausted_attempts": len(graph.budget_exhausted),
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
    sinks = sinks_for(graph, keys)
    levered = sorted(keys, key=lambda k: (-len(graph.leverage(k)), k))
    classes = sorted({graph.component[k] for k in keys if graph.component.get(k) is not None
                      and len(graph.components[graph.component[k]]) >= 2},
                     key=lambda c: -len(graph.components[c]))
    return {
        "problem": args.number,
        "open_statements": len(keys),
        "sinks": [statement_view(graph, payload, k, depth="brief") for k in sinks[: args.limit]],
        "disguise_classes": [
            [{"key": m, "type": graph.statements[m].get("type")} for m in graph.components[c]]
            for c in classes[: args.limit]],
        "highest_leverage": [
            {"key": k, "type": graph.statements[k].get("type"), "leverage": len(graph.leverage(k))}
            for k in levered[: args.limit]],
    }


def cmd_find(graph: builder.Graph, payload: dict[str, Any], args: argparse.Namespace) -> Any:
    needle = args.text.lower()
    hits = [(k, n) for k, n in graph.statements.items() if needle in (n.get("type") or "").lower()]
    hits.sort(key=lambda kn: (kn[0] in graph.supplied, len(kn[1].get("type") or "")))
    return [{"key": k, "status": "supplied" if k in graph.supplied else "open", "type": n.get("type")}
            for k, n in hits[: args.limit]]


def cmd_statement(graph: builder.Graph, payload: dict[str, Any], args: argparse.Namespace) -> Any:
    return statement_view(graph, payload, args.key)


def cmd_theorem(graph: builder.Graph, payload: dict[str, Any], args: argparse.Namespace) -> Any:
    theorem = graph.theorems.get(args.name)
    if theorem is None:
        candidates = [n for n in graph.theorems if n.endswith("." + args.name) or n == args.name]
        if len(candidates) != 1:
            raise SystemExit(f"unknown theorem {args.name!r} ({len(candidates)} suffix matches)")
        theorem = graph.theorems[candidates[0]]
    return {
        **theorem_card(graph, theorem["name"]),
        "module": theorem.get("module"),
        "hypotheses": [
            {"key": h, "type": graph.statements.get(h, {}).get("type"),
             "status": "supplied" if h in graph.supplied else "open"}
            for h in theorem.get("hypotheses", [])],
        "schematic_hypotheses": theorem.get("schematic_hypotheses", []),
        "conclusion": {"key": theorem.get("conclusion_key"), "type": theorem.get("conclusion_type"),
                       "status": ("supplied" if theorem.get("conclusion_key") in graph.supplied else "open")
                       if theorem.get("conclusion_key") else "schematic"},
    }


def cmd_why(graph: builder.Graph, payload: dict[str, Any], args: argparse.Namespace) -> Any:
    view = statement_view(graph, payload, args.key, depth="brief")
    if view["status"] != "supplied":
        return {"key": view["key"], "status": "open", "note": "no kernel witness chain in the export"}
    return graph.proof_tree(view["key"], limit=args.depth)


def cmd_about(graph: builder.Graph, payload: dict[str, Any], args: argparse.Namespace) -> Any:
    name = args.constant
    hits = [k for k, n in graph.statements.items()
            if any(c == name or c.endswith("." + name) for c in n.get("constants", ()))]
    supplied = sorted((k for k in hits if k in graph.supplied), key=lambda k: len(graph.statements[k].get("type") or ""))
    open_ = sorted((k for k in hits if k not in graph.supplied), key=lambda k: -len(graph.leverage(k)))
    return {
        "constant": name,
        "supplied_count": len(supplied),
        "open_count": len(open_),
        "supplied": [{"key": k, "type": graph.statements[k].get("type"),
                      "witness": graph.reductions[graph.witness[k]][1] if graph.witness.get(k, -1) >= 0 else None}
                     for k in supplied[: args.limit]],
        "open": [{"key": k, "type": graph.statements[k].get("type"),
                  "reductions": len(graph.reduced_by_head.get(k, [])), "leverage": len(graph.leverage(k))}
                 for k in open_[: args.limit]],
    }


def cmd_criticality(graph: builder.Graph, payload: dict[str, Any], args: argparse.Namespace) -> Any:
    target = args.target
    if target in graph.theorems or any(n.endswith("." + target) for n in graph.theorems):
        name = target if target in graph.theorems else next(n for n in graph.theorems if n.endswith("." + target))
        lost = graph.criticality(producer=name)
        subject = {"theorem": name}
    else:
        key = statement_view(graph, payload, target, depth="brief")["key"]
        lost = graph.criticality(statement=key)
        subject = {"statement": key, "type": graph.statements[key].get("type")}
    return {**subject, "loses_every_witness_chain": len(lost),
            "sample": [{"key": k, "type": graph.statements[k].get("type")} for k in sorted(lost)[: args.limit]]}


def cmd_transfer(graph: builder.Graph, payload: dict[str, Any], args: argparse.Namespace) -> Any:
    owners = problems_of(payload)
    rows = []
    for head, producer, reading, residuals in graph.reductions:
        producer_problem = graph.theorems.get(producer, {}).get("card", {}).get("problem")
        head_problems = set(owners.get(head, [])) - {producer_problem}
        if not producer_problem or producer_problem in ("cross", "249_257") or not head_problems:
            continue
        if producer_problem in owners.get(head, []):
            continue
        rows.append({"producer": producer, "producer_problem": producer_problem,
                     "supplies": head, "type": graph.statements.get(head, {}).get("type"),
                     "statement_problems": sorted(head_problems), "reading": reading,
                     "open_residuals": [r for r in residuals if r not in graph.supplied]})
    rows.sort(key=lambda r: (r["producer_problem"], r["producer"]))
    return {"cross_problem_reductions": len(rows), "rows": rows[: args.limit]}


def cmd_diff(graph: builder.Graph, payload: dict[str, Any], args: argparse.Namespace) -> Any:
    old_graph, _ = load(args.old)
    new_graph, _ = load(args.new)
    newly_supplied = sorted(new_graph.supplied - old_graph.supplied)
    lost = sorted(old_graph.supplied - new_graph.supplied)
    added = sorted(set(new_graph.statements) - set(old_graph.statements))
    old_classes = {frozenset(c) for c in old_graph.disguise_classes()}
    new_classes = [c for c in new_graph.disguise_classes() if frozenset(c) not in old_classes]
    def rows(graph_: builder.Graph, keys: list[str]) -> list[dict[str, Any]]:
        return [{"key": k, "type": graph_.statements[k].get("type")} for k in keys[: args.limit]]
    return {"newly_supplied": len(newly_supplied), "newly_supplied_sample": rows(new_graph, newly_supplied),
            "no_longer_supplied": len(lost), "no_longer_supplied_sample": rows(old_graph, lost),
            "new_statements": len(added), "new_disguise_classes": len(new_classes)}


def packet_markdown(graph: builder.Graph, payload: dict[str, Any], problem: str, limit: int) -> str:
    keys = open_for_problem(graph, payload, problem)
    sinks = sinks_for(graph, keys)
    source = payload.get("source", {})
    lines = [
        f"# Argument frontier for Erdős #{problem}",
        "",
        f"Generated from the kernel export `{source.get('export_digest', '?')}` "
        f"(Lean {source.get('lean_version', '?')}). Every row cites corpus theorems; "
        "`open` means no chain of corpus theorems found by the export supplies the statement "
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

    for key in sinks[:limit]:
        node = graph.statements[key]
        lines.append(f"### `{key[:12]}` {node.get('type')}")
        reductions = graph.reduced_by_head.get(key, [])
        lines.append(f"Reductions into it: {len(reductions)}.")
        for (_, producer, reading, left) in reductions[:8]:
            residual_text = "; ".join(f"`{r[:12]}` {graph.statements.get(r, {}).get('type')}" for r in left) or "(none)"
            lines.append(f"- `{producer}` ({reading}) {paper_note(producer)} leaves: {residual_text}")
        bundles, truncated = graph.bundles(key)
        if bundles:
            lines.append("Minimal bundles (supply every member of one bundle to close it):")
            for bundle in bundles[:10]:
                lines.append("- " + " AND ".join(f"`{b[:12]}`" for b in bundle))
            if truncated:
                lines.append("- (bundle enumeration hit its budget; more exist)")
        component = graph.component.get(key)
        if component is not None and len(graph.components[component]) >= 2:
            lines.append(f"Disguise class: {len(graph.components[component])} provably equivalent statements "
                         "(see section 2). Moving between them is not progress.")
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
            lines.append(f"- `{m[:12]}` {graph.statements[m].get('type')}")
        lines.append("")

    lines += ["## 3. Partial progress: members of bundles of size two or more", "",
              "Supplying one member of such a bundle leaves a strictly smaller open bundle. "
              "Unless the kernel also proves the converse, each member is weaker than the target it serves.", ""]
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
                lines.append(f"- `{member[:12]}` {graph.statements[member].get('type')} "
                             f"(leverage {len(graph.leverage(member))}; serves `{key[:12]}`)")
    if not seen:
        lines.append("None: every recorded route to these targets is a single open statement.")
    lines.append("")

    lines += ["## 4. Highest leverage open statements", ""]
    levered = sorted(keys, key=lambda k: (-len(graph.leverage(k)), k))
    for key in levered[:limit]:
        gained = graph.leverage(key)
        if not gained:
            break
        lines.append(f"- `{key[:12]}` {graph.statements[key].get('type')}: supplies {len(gained)} open statements")
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
    p = sub.add_parser("criticality"); p.add_argument("target"); p.add_argument("--limit", type=int, default=30)
    p = sub.add_parser("transfer"); p.add_argument("--limit", type=int, default=60)
    p = sub.add_parser("diff"); p.add_argument("old", type=Path); p.add_argument("new", type=Path)
    p.add_argument("--limit", type=int, default=30)
    p = sub.add_parser("packet"); p.add_argument("--problem", required=True); p.add_argument("--limit", type=int, default=12)
    args = parser.parse_args(argv)
    graph, payload = load(args.graph)
    handler = {"summary": cmd_summary, "problem": cmd_problem, "find": cmd_find, "statement": cmd_statement,
               "theorem": cmd_theorem, "why": cmd_why, "about": cmd_about, "criticality": cmd_criticality,
               "transfer": cmd_transfer, "diff": cmd_diff, "packet": cmd_packet}[args.command]
    result = handler(graph, payload, args)
    if isinstance(result, str):
        sys.stdout.write(result)
    else:
        print(json.dumps(result, indent=1, ensure_ascii=False))
    return 0


if __name__ == "__main__":
    sys.exit(main())
