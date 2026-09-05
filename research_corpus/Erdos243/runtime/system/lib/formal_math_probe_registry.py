#!/usr/bin/env python3
"""Cross-problem registry binding formal-math computations to their analytics.

Why this exists
---------------
`formal_math_experiment_contract` already gives each computation a typed
provenance record: hypothesis, predeclared falsifier, stop condition, analytic
bridge, and source hashes.  What it does NOT do is bind a computation to the
*named mechanisms* a problem's research packet actually tracks -- the
`exact_results`, `open_producers`, and `negative_results` ids that the problem
cockpit exposes and that a reader uses to decide what is still open.

Without that binding a probe is durable but unaddressable: nothing answers
"which computations bear on open producer X of problem N", and nothing notices
when an open producer has no computational coverage at all.

This module supplies the missing edges, for every Erdos problem in the repo
rather than one problem's script pile:

  motivates   analytic mechanism id  ->  probe      (what inspired the run)
  eliminates  probe  ->  analytic mechanism id      (what the result killed)
  opens       probe  ->  analytic mechanism id      (what the result opened)
  supports    probe  ->  analytic mechanism id      (what it is evidence for)

A probe emits `mechanism_bindings(...)` next to its experiment contract; the
registry resolves the ids against the live research packets, so a renamed or
deleted mechanism shows up as a dangling edge instead of silently rotting.

Authority boundary: these edges route research attention.  They never promote
finite computation to proof authority; that stays with Lean, an exact
counterexample, or the named owner verifier.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import sys
from pathlib import Path
from typing import Any, Iterable, Mapping

from system.lib.formal_math_experiment_contract import packet_scope_digest

BINDINGS_SCHEMA = "formal_math_mechanism_bindings_v1"
REGISTRY_SCHEMA = "formal_math_probe_registry_v1"
OVERVIEW_SCHEMA = "formal_math_probe_overview_v1"

EDGE_KINDS = ("motivated_by", "eliminates", "opens", "supports")


# --------------------------------------------------------------------------
# probe-side helper
# --------------------------------------------------------------------------

def mechanism_bindings(
    *,
    problem_id: str,
    motivated_by: Iterable[str] = (),
    eliminates: Iterable[str] = (),
    opens: Iterable[str] = (),
    supports: Iterable[str] = (),
    rationale: str = "",
) -> dict[str, Any]:
    """Build the binding block a probe stores beside its experiment contract."""
    if not problem_id.strip():
        raise ValueError("problem_id must be non-empty")
    block: dict[str, Any] = {
        "schema_version": BINDINGS_SCHEMA,
        "problem_id": problem_id.strip(),
        "motivated_by": sorted({v.strip() for v in motivated_by if v.strip()}),
        "eliminates": sorted({v.strip() for v in eliminates if v.strip()}),
        "opens": sorted({v.strip() for v in opens if v.strip()}),
        "supports": sorted({v.strip() for v in supports if v.strip()}),
    }
    if not block["motivated_by"]:
        raise ValueError(
            "every probe must name at least one motivating analytic mechanism; "
            "an unmotivated computation is not addressable research"
        )
    if rationale.strip():
        block["rationale"] = rationale.strip()
    return block


# --------------------------------------------------------------------------
# packet discovery
# --------------------------------------------------------------------------

def _packet_mechanism_ids(packet: Mapping[str, Any]) -> dict[str, set[str]]:
    out: dict[str, set[str]] = {}
    for field in ("exact_results", "open_producers", "negative_results",
                  "finite_evidence"):
        rows = packet.get(field)
        ids: set[str] = set()
        if isinstance(rows, list):
            for row in rows:
                if isinstance(row, Mapping) and isinstance(row.get("id"), str):
                    ids.add(row["id"])
        out[field] = ids
    return out


def discover_problems(repo_root: Path) -> dict[str, dict[str, Any]]:
    """Every Erdos problem packet in the repo, keyed by problem id."""
    problems: dict[str, dict[str, Any]] = {}
    for packet_path in sorted(repo_root.glob("formal_math/*/ErdosProblems/*/research_packet.json")):
        try:
            packet = json.loads(packet_path.read_text(encoding="utf-8"))
        except (OSError, json.JSONDecodeError):
            continue
        if not isinstance(packet, Mapping):
            continue
        pid = packet.get("problem_id")
        if not isinstance(pid, str):
            pid = packet_path.parent.name.lower()
        ids = _packet_mechanism_ids(packet)
        problems[pid] = {
            "problem_id": pid,
            "title": packet.get("title"),
            "packet_ref": str(packet_path.relative_to(repo_root)),
            "target_status": (packet.get("target") or {}).get("status")
            if isinstance(packet.get("target"), Mapping) else None,
            "mechanism_ids": {k: sorted(v) for k, v in ids.items()},
            "all_ids": set().union(*ids.values()) if ids else set(),
        }
    return problems


# --------------------------------------------------------------------------
# receipt discovery
# --------------------------------------------------------------------------

def _sha256(path: Path) -> str | None:
    try:
        return hashlib.sha256(path.read_bytes()).hexdigest()
    except OSError:
        return None


def discover_receipts(repo_root: Path, roots: Iterable[str]) -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    for root in roots:
        base = repo_root / root
        if not base.exists():
            continue
        for path in sorted(base.rglob("*.json")):
            try:
                payload = json.loads(path.read_text(encoding="utf-8"))
            except (OSError, json.JSONDecodeError):
                continue
            if not isinstance(payload, Mapping):
                continue
            bindings = payload.get("mechanism_bindings")
            contract = payload.get("experiment_contract")
            if not isinstance(bindings, Mapping) and not isinstance(contract, Mapping):
                continue
            rows.append({
                "receipt_ref": str(path.relative_to(repo_root)),
                "payload": payload,
                "bindings": bindings if isinstance(bindings, Mapping) else None,
                "contract": contract if isinstance(contract, Mapping) else None,
            })
    return rows


# --------------------------------------------------------------------------
# registry build
# --------------------------------------------------------------------------

def build_registry(repo_root: Path, roots: Iterable[str]) -> dict[str, Any]:
    problems = discover_problems(repo_root)
    receipts = discover_receipts(repo_root, roots)

    probes: list[dict[str, Any]] = []
    dangling: list[dict[str, Any]] = []
    stale_sources: list[dict[str, Any]] = []
    unrelated_source_edits: list[dict[str, Any]] = []
    unbound: list[str] = []
    coverage: dict[str, dict[str, list[str]]] = {
        pid: {mid: [] for mid in prob["mechanism_ids"].get("open_producers", [])}
        for pid, prob in problems.items()
    }

    for row in receipts:
        payload = row["payload"]
        contract = row["contract"] or {}
        bindings = row["bindings"]
        probe_meta = contract.get("probe") if isinstance(contract.get("probe"), Mapping) else {}
        problem_meta = contract.get("problem") if isinstance(contract.get("problem"), Mapping) else {}
        result_meta = contract.get("result") if isinstance(contract.get("result"), Mapping) else {}
        progress = result_meta.get("progress") if isinstance(result_meta.get("progress"), Mapping) else {}

        pid = None
        if isinstance(bindings, Mapping):
            pid = bindings.get("problem_id")
        if not pid:
            pid = problem_meta.get("id")
        probe_id = probe_meta.get("id") or payload.get("probe_id") or row["receipt_ref"]

        if not isinstance(bindings, Mapping):
            unbound.append(row["receipt_ref"])

        known = problems.get(pid, {}).get("all_ids", set()) if pid else set()
        edges: dict[str, list[str]] = {}
        for kind in EDGE_KINDS:
            key = "motivated_by" if kind == "motivated_by" else kind
            values = list(bindings.get(key, [])) if isinstance(bindings, Mapping) else []
            edges[kind] = values
            for value in values:
                if pid and known and value not in known:
                    dangling.append({"receipt_ref": row["receipt_ref"],
                                     "problem_id": pid, "edge": kind,
                                     "mechanism_id": value})
                if kind == "motivated_by" and pid in coverage and value in coverage[pid]:
                    coverage[pid][value].append(probe_id)

        # source staleness: recorded hash vs current file
        for record_key in ("sources", "source_records"):
            records = payload.get(record_key)
            if not isinstance(records, list):
                continue
            for item in records:
                if not isinstance(item, Mapping):
                    continue
                ref, recorded = item.get("path"), item.get("sha256")
                if not isinstance(ref, str) or not isinstance(recorded, str):
                    continue
                current = _sha256(repo_root / ref)
                if current is None:
                    stale_sources.append({"receipt_ref": row["receipt_ref"],
                                          "source_ref": ref, "reason": "missing"})
                    continue
                if current == recorded:
                    continue
                # A research packet is append-mostly.  When the receipt recorded
                # a digest scoped to the mechanism entries it actually bound to,
                # a whole-file change is only stale if that scoped slice moved;
                # otherwise a sibling deposit landed and this receipt still
                # stands.  Receipts without a scoped digest keep the old rule.
                recorded_scope = item.get("scoped_sha256")
                scope_ids = item.get("scope_ids")
                if isinstance(recorded_scope, str) and isinstance(scope_ids, list):
                    try:
                        payload_bytes = (repo_root / ref).read_bytes()
                    except OSError:
                        payload_bytes = b""
                    current_scope = packet_scope_digest(payload_bytes, scope_ids)
                    if current_scope is not None and current_scope == recorded_scope:
                        unrelated_source_edits.append({
                            "receipt_ref": row["receipt_ref"], "source_ref": ref,
                            "reason": "unrelated_packet_edit",
                            "bound_mechanism_ids": list(scope_ids)})
                        continue
                    stale_sources.append({
                        "receipt_ref": row["receipt_ref"], "source_ref": ref,
                        "reason": "bound_mechanism_changed",
                        "bound_mechanism_ids": list(scope_ids)})
                    continue
                stale_sources.append({"receipt_ref": row["receipt_ref"],
                                      "source_ref": ref, "reason": "changed"})

        probes.append({
            "probe_id": probe_id,
            "problem_id": pid,
            "receipt_ref": row["receipt_ref"],
            "question": probe_meta.get("question"),
            "falsifier": probe_meta.get("falsifier"),
            "result_status": result_meta.get("status"),
            "progress_class": progress.get("class"),
            "next_analytic_target": progress.get("next_analytic_target"),
            "edges": edges,
        })

    uncovered = {
        pid: sorted(mid for mid, ps in mids.items() if not ps)
        for pid, mids in coverage.items()
    }
    return {
        "schema_version": REGISTRY_SCHEMA,
        "authority_boundary": (
            "Registry edges route research attention. Finite computation is "
            "evidence, never proof authority."
        ),
        "problem_count": len(problems),
        "probe_count": len(probes),
        "problems": {
            pid: {k: v for k, v in prob.items() if k != "all_ids"}
            for pid, prob in problems.items()
        },
        "probes": probes,
        "open_producer_coverage": {
            pid: {mid: sorted(set(ps)) for mid, ps in mids.items()}
            for pid, mids in coverage.items()
        },
        "uncovered_open_producers": uncovered,
        "integrity": {
            "receipts_without_mechanism_bindings": sorted(unbound),
            "dangling_mechanism_edges": dangling,
            "stale_source_records": stale_sources,
            "unrelated_packet_edits": unrelated_source_edits,
        },
    }



def render_report(registry: Mapping[str, Any]) -> str:
    """Human-readable coverage and integrity report across every problem."""
    lines: list[str] = []
    lines.append("formal-math probe coverage")
    lines.append("=" * 70)
    problems = registry["problems"]
    coverage = registry["open_producer_coverage"]
    total_producers = 0
    total_covered = 0
    for pid in sorted(problems, key=lambda k: int("".join(c for c in k if c.isdigit()) or 0)):
        prob = problems[pid]
        mids = coverage.get(pid, {})
        covered = {m: ps for m, ps in mids.items() if ps}
        total_producers += len(mids)
        total_covered += len(covered)
        probes = [x for x in registry["probes"] if x.get("problem_id") == pid]
        lines.append("")
        lines.append(f"{pid}  {prob.get('title') or ''}")
        lines.append(f"  target status : {prob.get('target_status')}")
        lines.append(f"  probes        : {len(probes)}")
        lines.append(f"  open producers: {len(covered)}/{len(mids)} with computational coverage")
        for mid in sorted(mids):
            mark = "*" if mids[mid] else " "
            who = ", ".join(sorted(set(mids[mid]))) if mids[mid] else "-- none --"
            lines.append(f"    [{mark}] {mid}: {who}")
    lines.append("")
    lines.append("-" * 70)
    lines.append(f"totals: {total_covered}/{total_producers} open producers covered, "
                 f"{registry['probe_count']} probes across {registry['problem_count']} problems")
    integrity = registry["integrity"]
    lines.append(f"integrity: {len(integrity['dangling_mechanism_edges'])} dangling edge(s), "
                 f"{len(integrity['receipts_without_mechanism_bindings'])} receipt(s) with no "
                 f"mechanism binding, {len(integrity['stale_source_records'])} stale source record(s)")
    if integrity["stale_source_records"]:
        lines.append("  stale receipts (declared sources have changed since the run):")
        seen: set[str] = set()
        for row in integrity["stale_source_records"]:
            ref = row["receipt_ref"]
            if ref in seen:
                continue
            seen.add(ref)
            if len(seen) > 12:
                lines.append(f"    ... and {len(set(r['receipt_ref'] for r in integrity['stale_source_records'])) - 12} more")
                break
            lines.append(f"    {ref}")
    unrelated = integrity.get("unrelated_packet_edits") or []
    if unrelated:
        refs = sorted({row["receipt_ref"] for row in unrelated})
        lines.append(f"  {len(refs)} receipt(s) saw a sibling deposit into their packet while "
                     "their own bound mechanisms held; not stale, no rerun needed:")
        for ref in refs[:12]:
            lines.append(f"    {ref}")
        if len(refs) > 12:
            lines.append(f"    ... and {len(refs) - 12} more")
    return "\n".join(lines)


def build_overview(registry: Mapping[str, Any]) -> dict[str, Any]:
    """Return a compact cross-problem computation routing surface.

    The detailed registry can be large because it preserves every mechanism
    binding and receipt route.  This overview intentionally retains only
    per-problem coverage counts, integrity counts, and the exact authority
    paths/commands needed for a later drill-down.  It is not a ranking or a
    mathematical-status projection.
    """

    problems = registry.get("problems")
    coverage = registry.get("open_producer_coverage")
    probes = registry.get("probes")
    integrity = registry.get("integrity")
    if not isinstance(problems, Mapping):
        problems = {}
    if not isinstance(coverage, Mapping):
        coverage = {}
    if not isinstance(probes, list):
        probes = []
    if not isinstance(integrity, Mapping):
        integrity = {}

    def problem_sort_key(problem_id: object) -> tuple[int, str]:
        text = str(problem_id)
        digits = "".join(character for character in text if character.isdigit())
        return (int(digits) if digits else 0, text)

    rows: list[dict[str, Any]] = []
    total_open_producer_count = 0
    total_covered_open_producer_count = 0
    for problem_id in sorted(problems, key=problem_sort_key):
        problem = problems[problem_id]
        if not isinstance(problem, Mapping):
            continue
        producer_map = coverage.get(problem_id)
        producer_map = producer_map if isinstance(producer_map, Mapping) else {}
        open_producer_count = len(producer_map)
        covered_open_producer_count = sum(
            1
            for receipt_ids in producer_map.values()
            if isinstance(receipt_ids, list) and receipt_ids
        )
        total_open_producer_count += open_producer_count
        total_covered_open_producer_count += covered_open_producer_count
        # The coverage route answers the registry-specific question.  Keep a
        # small companion bundle so a reader can return to the packet,
        # source-topology, bounded source inventory, and explicitly declared
        # corpus-computation routes without reconstructing paths from the
        # problem id or widening into a repository search. These are
        # navigation commands only: none run a computation or express a
        # mathematical-status judgement.
        problem_navigation_routes = {
            "problem_cockpit": (
                "./repo-python -m system.lib.mathematical_working_memory "
                f'--query "Erdos #{problem_sort_key(problem_id)[0]}" '
                "--problem-cockpit --context-budget 12000"
            ),
            "packet_frontier": (
                "./repo-python "
                "formal_math/erdos257_period_noncollapse/scripts/"
                "corpus_navigation.py "
                f"--problem {problem_id} --frontier-summary --json"
            ),
            "source_topology": (
                "./repo-python "
                "formal_math/erdos257_period_noncollapse/scripts/"
                "corpus_navigation.py "
                f"--problem {problem_id} --source-summary --json"
            ),
            "bounded_source_inventory": (
                "./repo-python "
                "formal_math/erdos257_period_noncollapse/scripts/"
                "corpus_navigation.py "
                f"--problem {problem_id} --source-paths --source-kind markdown "
                "--source-path-limit 40 --json"
            ),
            "explicit_corpus_computation_routes": (
                "./repo-python "
                "formal_math/erdos257_period_noncollapse/scripts/"
                "corpus_computation_routes.py "
                f"--problem {problem_id} --json"
            ),
        }
        rows.append(
            {
                "problem_id": problem_id,
                "research_packet_ref": problem.get("packet_ref"),
                "open_producer_count": open_producer_count,
                "covered_open_producer_count": covered_open_producer_count,
                "uncovered_open_producer_count": (
                    open_producer_count - covered_open_producer_count
                ),
                "probe_count": sum(
                    1
                    for probe in probes
                    if isinstance(probe, Mapping)
                    and probe.get("problem_id") == problem_id
                ),
                "coverage_route": (
                    "./repo-python -m system.lib.formal_math_probe_registry "
                    f"--problem {problem_id} --coverage"
                ),
                "problem_navigation_routes": problem_navigation_routes,
            }
        )

    return {
        "schema_version": OVERVIEW_SCHEMA,
        "kind": "cross_problem_computation_overview",
        "authority_boundary": (
            "Coverage counts and receipt bindings organize computational evidence; "
            "they do not rank work, state mathematical progress, or replace the "
            "problem-owned research packet and Lean proof authority."
        ),
        "summary": {
            "problem_count": len(rows),
            "probe_count": len(probes),
            "open_producer_count": total_open_producer_count,
            "covered_open_producer_count": total_covered_open_producer_count,
            "uncovered_open_producer_count": (
                total_open_producer_count - total_covered_open_producer_count
            ),
            "dangling_mechanism_edge_count": len(
                integrity.get("dangling_mechanism_edges") or []
            ),
            "unbound_receipt_count": len(
                integrity.get("receipts_without_mechanism_bindings") or []
            ),
            "stale_source_record_count": len(
                integrity.get("stale_source_records") or []
            ),
        },
        "problems": rows,
        "consumer_action": (
            "Select one problem from the compact rows, open its research packet, "
            "then use its coverage route only when a computation-bearing mechanism "
            "needs inspection."
        ),
    }


DEFAULT_ROOTS = ("state/formal_math",)


def _main(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("--repo-root", default=None)
    ap.add_argument("--root", action="append", default=None,
                    help="receipt root (repeatable); default state/formal_math")
    ap.add_argument("--problem", default=None, help="filter to one problem id or number")
    ap.add_argument("--producer", default=None, help="show probes motivated by this mechanism id")
    ap.add_argument("--coverage", action="store_true", help="open-producer coverage only")
    ap.add_argument("--integrity", action="store_true", help="integrity findings only")
    ap.add_argument(
        "--overview",
        action="store_true",
        help="compact per-problem computation coverage and authority routes",
    )
    ap.add_argument("--report", action="store_true",
                    help="human-readable coverage and integrity report")
    ap.add_argument("--out", default=None, help="write the full registry JSON here")
    ap.add_argument("--check", action="store_true",
                    help="exit non-zero on dangling edges or stale sources")
    args = ap.parse_args(argv)

    repo_root = Path(args.repo_root).resolve() if args.repo_root else Path(__file__).resolve().parents[2]
    registry = build_registry(repo_root, args.root or DEFAULT_ROOTS)

    if args.out:
        Path(args.out).write_text(json.dumps(registry, indent=1) + "\n")

    if args.report:
        print(render_report(registry))
        if args.check:
            bad = registry["integrity"]
            if bad["dangling_mechanism_edges"] or bad["stale_source_records"]:
                return 1
        return 0

    if args.overview:
        print(json.dumps(build_overview(registry), indent=1))
        if args.check:
            bad = registry["integrity"]
            if bad["dangling_mechanism_edges"] or bad["stale_source_records"]:
                return 1
        return 0

    view: dict[str, Any] = registry
    if args.problem:
        needle = args.problem.lower().replace("erdos", "").strip("_ ")
        keys = [k for k in registry["problems"] if needle in k.lower()]
        view = {
            "problems": {k: registry["problems"][k] for k in keys},
            "probes": [p for p in registry["probes"] if p.get("problem_id") in keys],
            "open_producer_coverage": {k: registry["open_producer_coverage"].get(k, {}) for k in keys},
            "uncovered_open_producers": {k: registry["uncovered_open_producers"].get(k, []) for k in keys},
        }
    if args.producer:
        view = {"producer": args.producer,
                "probes": [p for p in registry["probes"]
                           if args.producer in p["edges"].get("motivated_by", [])
                           or args.producer in p["edges"].get("eliminates", [])
                           or args.producer in p["edges"].get("opens", [])]}
    if args.coverage:
        view = {"open_producer_coverage": view.get("open_producer_coverage",
                                                   registry["open_producer_coverage"]),
                "uncovered_open_producers": view.get("uncovered_open_producers",
                                                     registry["uncovered_open_producers"])}
    if args.integrity:
        view = {"integrity": registry["integrity"]}

    print(json.dumps(view, indent=1)[:60000])
    if args.check:
        bad = registry["integrity"]
        if bad["dangling_mechanism_edges"] or bad["stale_source_records"]:
            return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(_main())
