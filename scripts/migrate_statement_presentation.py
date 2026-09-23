#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Carry the coverage ledger across edits that change how statements are written, not what they say.

A ledger row is keyed by the digest of its environment's raw body.  Adding a `\\label`,
or removing an inline Lean citation or a status tag from inside a statement, changes that
digest without changing the mathematics.  This script pairs every asserting environment
of a base revision with the environment at the same position of the working tree (per
source file, in document order; the number and kinds of environments must agree), and
classifies each changed pair:

  presentation   the bodies agree once labels, inline Lean citations (\\lean{..}{..}),
                 status tags (\\ev, \\coord, \\scale), `Sources:` sentences and layout are
                 removed;
  reviewed       any other change, admitted only when the review file names the row, the
                 exact old and new digests, and a reason that the mathematics is unchanged.

Every changed row gets its new digest, its new first label (and so its new id when it had
none), and its new source line; its Lean, Comparator and Palomar evidence is carried over
unchanged.  The pairing, class and old and new digests of each row are written to the
migration record.  Any unpaired environment, kind mismatch or unreviewed change is a
failure, and then nothing is written.

  migrate_statement_presentation.py --base <rev> --record docs/statement_migrations/<name>.json
                                    [--reviewed <file>] [--dry-run]
"""
from __future__ import annotations

import argparse
import hashlib
import json
import re
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))
import check_lean_paper_propagation as chk  # noqa: E402

LEDGER = ROOT / "docs/paper_lean_coverage.json"


def _strip_command(text: str, name: str, arity: int) -> str:
    """Remove every `\\name{..}...{..}` (balanced braces)."""
    out = []
    i = 0
    pattern = re.compile(r"\\" + re.escape(name) + r"(?![A-Za-z@])")
    while True:
        m = pattern.search(text, i)
        if m is None:
            out.append(text[i:])
            return "".join(out)
        out.append(text[i:m.start()])
        j = m.end()
        ok = True
        for _ in range(arity):
            while j < len(text) and text[j] in " \t":
                j += 1
            if j >= len(text) or text[j] != "{":
                ok = False
                break
            depth = 0
            while j < len(text):
                if text[j] == "\\":
                    j += 2
                    continue
                if text[j] == "{":
                    depth += 1
                elif text[j] == "}":
                    depth -= 1
                    if depth == 0:
                        j += 1
                        break
                j += 1
        if not ok:
            out.append(text[m.start():m.end()])
            i = m.end()
        else:
            i = j


PRESENTATION = (("label", 1), ("compatlabel", 1), ("lean", 2), ("ev", 1), ("coord", 1), ("scale", 1))


def presentation_form(body: str) -> str:
    text = chk.counter_view(body)
    for name, arity in PRESENTATION:
        text = _strip_command(text, name, arity)
    text = re.sub(r"\\textit\{Sources:\}[^\n]*(?:\n(?!\s*\n)[^\n]*)*", "", text)
    text = re.sub(r"~", " ", text)
    return " ".join(text.split())


def git_show(rev: str, path: str) -> str | None:
    done = subprocess.run(["git", "-C", str(ROOT), "show", f"{rev}:{path}"], capture_output=True)
    return None if done.returncode else done.stdout.decode("utf-8")


def sha(text: str) -> str:
    return "sha256:" + hashlib.sha256(text.encode()).hexdigest()


def bodies(pairs: list[tuple[str, str]], spans: list[dict]) -> list[dict]:
    """inventory() plus each environment's raw body, per file in document order."""
    found = chk.inventory(pairs, spans)
    texts = {path: chk.counter_view(text) for path, text in pairs}
    for env in found:
        text = texts[env["path"]]
        if env["environment"] is None:
            env["body"] = None
            continue
        offset = sum(len(l) for l in text.splitlines(keepends=True)[: env["line"] - 1])
        start = chk.BEGIN_RE.search(text, offset)
        end = text.find("\\end{" + env["environment"] + "}", start.end())
        env["body"] = text[start.end():end]
    return found


def main(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    ap.add_argument("--base", required=True)
    ap.add_argument("--record", required=True)
    ap.add_argument("--reviewed", type=Path)
    ap.add_argument("--dry-run", action="store_true")
    args = ap.parse_args(argv)
    # The ledger is always migrated from the base revision's copy, so the script can be
    # rerun after further presentation edits and still pair every row with its base digest.
    base_ledger = git_show(args.base, "docs/paper_lean_coverage.json")
    if base_ledger is None:
        print(f"FAIL no ledger at {args.base}", file=sys.stderr)
        return 1
    ledger = json.loads(base_ledger)
    reviewed = {}
    if args.reviewed:
        for item in json.loads(args.reviewed.read_text(encoding="utf-8"))["rows"]:
            reviewed[(item["old_statement_sha256"], item["new_statement_sha256"])] = item
    problems: list[str] = []
    rows_by_sha: dict[tuple[str, str], dict] = {}
    for row in ledger["rows"]:
        rows_by_sha[(row["paper_id"], row["statement_sha256"])] = row
    spans_by_paper: dict[str, list[dict]] = {}
    for row in ledger["rows"]:
        if row.get("span"):
            spans_by_paper.setdefault(row["paper_id"], []).append({"label": row["label"], **row["span"]})
    record_rows = []
    counts = {"unchanged": 0, "presentation": 0, "reviewed": 0}
    paired: set[str] = set()
    for paper in ledger["papers"]:
        pid = paper["paper_id"]
        old_pairs, new_pairs = [], []
        for rel in paper["sources"]:
            old = git_show(args.base, rel)
            if old is None:
                problems.append(f"{rel} is absent at {args.base}")
                continue
            old_pairs.append((rel, old))
            new_pairs.append((rel, (ROOT / rel).read_text(encoding="utf-8")))
        spans = spans_by_paper.get(pid, [])
        old_envs = bodies(old_pairs, spans)
        new_envs = bodies(new_pairs, spans)
        for rel in paper["sources"]:
            olds = [e for e in old_envs if e["path"] == rel]
            news = [e for e in new_envs if e["path"] == rel]
            if len(olds) != len(news):
                problems.append(f"{rel}: {len(olds)} asserting environments at the base, {len(news)} now")
                continue
            for o, n in zip(olds, news):
                if o["environment"] != n["environment"]:
                    problems.append(f"{rel}:{n['line']}: {o['environment']} became {n['environment']}")
                    continue
                row = rows_by_sha.get((pid, o["statement_sha256"]))
                if row is None:
                    continue  # not a ledger row (e.g. a non-asserting kind the ledger omits)
                paired.add(row["id"])
                if o["statement_sha256"] == n["statement_sha256"]:
                    counts["unchanged"] += 1
                    kind = "unchanged"
                elif o["body"] is not None and presentation_form(o["body"]) == presentation_form(n["body"]):
                    counts["presentation"] += 1
                    kind = "presentation"
                elif (o["statement_sha256"], n["statement_sha256"]) in reviewed:
                    counts["reviewed"] += 1
                    kind = "reviewed"
                else:
                    problems.append(f"{row['id']}: statement changed beyond presentation "
                                    f"({o['statement_sha256'][:19]} -> {n['statement_sha256'][:19]}); "
                                    "review it or revert it")
                    continue
                labels = n["labels"]
                new_label = labels[0] if labels else ""
                if row.get("label") and new_label != row["label"]:
                    problems.append(f"{row['id']}: its first label changed from {row['label']} to {new_label}")
                    continue
                if kind != "unchanged":
                    record_rows.append({
                        "old_id": row["id"],
                        "new_id": f"{pid}#{new_label}" if new_label else row["id"],
                        "class": kind,
                        "old_statement_sha256": o["statement_sha256"],
                        "new_statement_sha256": n["statement_sha256"],
                        "source": f"{rel}:{n['line']}",
                        **({"reason": reviewed[(o['statement_sha256'], n['statement_sha256'])]["reason"]}
                           if kind == "reviewed" else {}),
                    })
                    row["statement_sha256"] = n["statement_sha256"]
                    row["label"] = new_label
                    row["id"] = f"{pid}#{new_label}" if new_label else row["id"]
                    row["source"] = f"{rel}:{n['line']}"
    unpaired = [row["id"] for row in ledger["rows"] if row["id"] not in paired and
                row["id"] not in {r["new_id"] for r in record_rows}]
    if unpaired:
        problems.append(f"{len(unpaired)} ledger rows were not paired with an environment: {unpaired[:5]}")
    ids = [row["id"] for row in ledger["rows"]]
    if len(ids) != len(set(ids)):
        problems.append("row ids are no longer unique")
    if problems:
        for p in problems:
            print("FAIL", p, file=sys.stderr)
        print(f"{len(problems)} problems; nothing written", file=sys.stderr)
        return 1
    print(json.dumps(counts))
    if args.dry_run:
        return 0
    LEDGER.write_text(json.dumps(ledger, indent=1, ensure_ascii=False) + "\n", encoding="utf-8")
    record = {
        "schema": "plectis-statement-migration/1",
        "base": subprocess.run(["git", "-C", str(ROOT), "rev-parse", args.base], capture_output=True,
                               text=True).stdout.strip(),
        "rule": ("Rows whose statement digest changed between the base and this revision. "
                 "presentation: equal once labels, inline Lean citations, status tags, Sources "
                 "sentences and layout are removed. reviewed: a stated reason that the mathematics "
                 "is unchanged. Lean, Comparator and Palomar evidence is carried over unchanged."),
        "counts": counts,
        "rows": record_rows,
    }
    out = ROOT / args.record
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(record, indent=1, ensure_ascii=False) + "\n", encoding="utf-8")
    return 0


if __name__ == "__main__":
    sys.exit(main())
