#!/usr/bin/env python3
# SPDX-License-Identifier: Apache-2.0
"""Reconcile docs/paper_lean_coverage.json after an editorial revision of the papers.

An editorial pass moves statements between a short paper and its long record, merges a short statement into an
existing long one, adds navigation markup (``\\hypertarget``) inside statements, and occasionally adds a new asserting
environment. ``check_lean_paper_propagation.py`` then reports rows whose statement digest is no longer in the paper and
environments without a row, and asks for the ledger to be regenerated. This program does that regeneration for the
cases a machine can decide, and refuses the rest:

  rebind   a row's label is still in its paper and the statement differs from the recorded one only by navigation
           markup and whitespace (compared against the statement at ``--base``): new digest and source line.
  move     a row's label now names a statement in the other paper of the same problem that has no row: the row moves
           with its evidence (same comparison against the base statement).
  retire   a row's statement was merged into an existing statement with a row. Needs a ``--mapping`` entry naming the
           destination, and the destination row must carry every Lean declaration of the retired row.
  add      an asserting environment without a row gets a row recording no Lean statement, marked uncounted, so the
           maintainer reads it before it counts.

A statement whose mathematical text changed is never rebound: it is reported as ``refused`` and the ledger is left
for review. Run ``check_lean_paper_propagation.py --restamp`` afterwards; it recomputes the summary and digest.

    python3 scripts/reconcile_paper_lean_coverage.py --base <commit> [--mapping map.json] [--apply]

``--mapping`` is a JSON list of {"paper_id", "label", "destination_paper_id", "destination_label"}.
Stdlib only.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import re
import subprocess
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import check_lean_paper_propagation as prop  # noqa: E402

ROOT = Path(__file__).resolve().parents[1]
LEDGER = "docs/paper_lean_coverage.json"
MARKUP = re.compile(r"\\hypertarget\{[^{}]*\}\{\}|\\papersectiontarget\{[^{}]*\}")


def markup_free(body: str) -> str:
    return re.sub(r"\s+", " ", MARKUP.sub("", body)).strip()


def statements(sources: list[tuple[str, str]]) -> list[dict]:
    """Inventory with bodies kept, using the checker's own environment detection."""
    views = [(path, prop.counter_view(text)) for path, text in sources]
    kinds = prop.theorem_kinds(view for _path, view in views)
    out = []
    for path, text in views:
        for start in prop.BEGIN_RE.finditer(text):
            environment = start.group(1)
            kind = kinds.get(environment.rstrip("*"))
            if kind is None or kind in prop.QUESTION_KINDS:
                continue
            end = text.find("\\end{" + environment + "}", start.end())
            if end < 0:
                continue
            body = text[start.end():end]
            out.append({"path": path, "line": prop.line_of(text, start.start()), "environment": environment,
                        "kind": kind, "labels": prop.LABEL_RE.findall(body), "body": body,
                        "statement_sha256": "sha256:" + hashlib.sha256(body.encode()).hexdigest()})
    return out


def git_show(ref: str, path: str) -> str:
    run = subprocess.run(["git", "-C", str(ROOT), "show", f"{ref}:{path}"], capture_output=True, text=True)
    return run.stdout if run.returncode == 0 else ""


def paper_statements(ledger: dict, read) -> dict[str, list[dict]]:
    out = {}
    for paper in ledger["papers"]:
        out[paper["paper_id"]] = statements([(p, read(p)) for p in paper.get("sources", [])])
    return out


def decls(row: dict) -> set[str]:
    return {d["name"] for d in row.get("lean", {}).get("declarations", [])}


def reconcile(base: str, mapping: list[dict]) -> tuple[dict, dict]:
    ledger = json.loads((ROOT / LEDGER).read_text(encoding="utf-8"))
    now = paper_statements(ledger, lambda p: (ROOT / p).read_text(encoding="utf-8"))
    before = paper_statements(ledger, lambda p: git_show(base, p))
    papers = {p["paper_id"]: p for p in ledger["papers"]}
    siblings = {}
    for p in ledger["papers"]:
        siblings.setdefault(p["problem"], []).append(p["paper_id"])
    old_body = {(pid, s["statement_sha256"]): s["body"] for pid, rows in before.items() for s in rows}
    rows = ledger["rows"]
    claimed: set = set()
    report = {"rebind": [], "move": [], "retire": [], "add": [], "refused": []}
    route = {(m["paper_id"], m["label"]): m for m in mapping}
    located_now = {pid: {(s["path"], s["statement_sha256"]) for s in prop.inventory(
        [(q, (ROOT / q).read_text(encoding="utf-8")) for q in papers[pid].get("sources", [])],
        prop.span_specs([r for r in rows if r["paper_id"] == pid]))} for pid in papers}

    def free(pid, stmt):
        return (pid, stmt["path"], stmt["line"]) not in claimed

    def take(row, other, stmt, kind):
        new = dict(row)
        new.update({"statement_sha256": stmt["statement_sha256"], "source": f"{stmt['path']}:{stmt['line']}"})
        if other != row["paper_id"] or (stmt["labels"] and row["label"] not in stmt["labels"]):
            label = row["label"] if row["label"] in stmt["labels"] else stmt["labels"][0]
            new.update({"paper_id": other, "side": papers[other]["side"], "label": label, "id": f"{other}#{label}"})
        claimed.add((other, stmt["path"], stmt["line"]))
        report[kind].append({"row": row["id"], "to": new["id"], "source": new["source"]})
        return new

    pending, keep = [], []
    for row in rows:  # pass 1: still located (environments and registered spans)
        path = row["source"].rsplit(":", 1)[0]
        (keep if (path, row["statement_sha256"]) in located_now.get(row["paper_id"], set()) else pending).append(row)
    for row in keep:
        for stmt in now.get(row["paper_id"], []):
            if stmt["statement_sha256"] == row["statement_sha256"] and row["source"].startswith(stmt["path"] + ":"):
                claimed.add((row["paper_id"], stmt["path"], stmt["line"]))
    unresolved = []
    for row in pending:  # pass 2: same paper, same label, markup-only change
        recorded = old_body.get((row["paper_id"], row["statement_sha256"]))
        hit = [s for s in now.get(row["paper_id"], []) if row["label"] in s["labels"] and free(row["paper_id"], s)]
        if recorded is not None and hit and markup_free(hit[0]["body"]) == markup_free(recorded):
            keep.append(take(row, row["paper_id"], hit[0], "rebind"))
        else:
            unresolved.append(row)
    pending, unresolved = unresolved, []
    for row in pending:  # pass 3: moved to the sibling paper (same label, or the mapped destination label)
        recorded = old_body.get((row["paper_id"], row["statement_sha256"]))
        dest = route.get((row["paper_id"], row["label"]))
        wanted = {row["label"]} | ({dest["destination_label"]} if dest else set())
        target = None
        for other in [p for p in siblings[row["problem"]] if p != row["paper_id"]] + [row["paper_id"]]:
            hit = [s for s in now.get(other, []) if wanted & set(s["labels"]) and free(other, s)]
            if hit:
                target = (other, hit[0])
                break
        if recorded is not None and target and markup_free(target[1]["body"]) == markup_free(recorded):
            keep.append(take(row, target[0], target[1], "move"))
        else:
            unresolved.append((row, recorded, target))
    by_id = {r["id"]: r for r in keep}
    for row, recorded, target in unresolved:  # pass 4: merged into a statement that already has a row
        dest = route.get((row["paper_id"], row["label"]))
        dest_row = by_id.get(f"{dest['destination_paper_id']}#{dest['destination_label']}") if dest else None
        if recorded is None:
            report["refused"].append({"row": row["id"], "why": f"statement not found at base {base}"})
            keep.append(row)
        elif target and dest_row is None:
            report["refused"].append({"row": row["id"], "why": "statement text changed beyond navigation markup",
                                      "at": f"{target[1]['path']}:{target[1]['line']}"})
            keep.append(row)
        elif dest_row is None:
            report["refused"].append({"row": row["id"], "why": "statement gone and no mapping to a row that carries it"})
            keep.append(row)
        elif not decls(row) <= decls(dest_row):
            report["refused"].append({"row": row["id"], "why": f"merged into {dest_row['id']}, which lacks its Lean declarations",
                                      "missing": sorted(decls(row) - decls(dest_row))})
            keep.append(row)
        else:
            report["retire"].append({"row": row["id"], "into": dest_row["id"]})
    ids = {r["id"] for r in keep}
    for pid, found in now.items():
        for stmt in found:
            if not free(pid, stmt):
                continue
            if any(r["paper_id"] == pid and r["statement_sha256"] == stmt["statement_sha256"] for r in keep):
                continue
            label = (stmt["labels"] or ["unlabelled"])[0]
            rid = f"{pid}#{label}"
            if rid in ids:
                continue
            row = {"id": rid, "problem": papers[pid]["problem"], "paper_id": pid, "side": papers[pid]["side"],
                   "label": label, "environment": stmt["environment"], "kind": stmt["kind"],
                   "statement_sha256": stmt["statement_sha256"], "source": f"{stmt['path']}:{stmt['line']}",
                   "lean": {"status": "none", "counted": False, "declarations": [],
                            "reason": "added by an editorial revision; no Lean statement recorded yet"},
                   "comparator": {"status": "not_applicable"}, "palomar": {"status": "not_applicable"}}
            if stmt["labels"][1:]:
                row["other_labels"] = stmt["labels"][1:]
            keep.append(row)
            ids.add(rid)
            report["add"].append({"row": rid, "source": row["source"]})
    ledger["rows"] = keep
    return ledger, report


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--base", required=True, help="commit whose papers the ledger last described")
    parser.add_argument("--mapping", type=Path)
    parser.add_argument("--apply", action="store_true")
    args = parser.parse_args()
    mapping = json.loads(args.mapping.read_text(encoding="utf-8")) if args.mapping else []
    ledger, report = reconcile(args.base, mapping)
    print(json.dumps({k: len(v) for k, v in report.items()}))
    for item in report["refused"]:
        print("  refused", json.dumps(item, ensure_ascii=False))
    if args.apply:
        (ROOT / LEDGER).write_text(json.dumps(ledger, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")
    Path(ROOT / "build").mkdir(exist_ok=True)
    (ROOT / "build/reconcile_paper_lean_coverage.json").write_text(json.dumps(report, indent=1, ensure_ascii=False) + "\n")
    return 1 if report["refused"] else 0


if __name__ == "__main__":
    sys.exit(main())
