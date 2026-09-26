#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Run the decoding certificate over every set of primes of one size below a bound.

For each set P of `--size` primes at most `--bound` this program computes the
first depth k <= `--max-depth` at which the depth-k decoding test of
certificate.py passes, twice: with the outward-rounded outer envelopes (the
certificate the paper describes) and with the exact extreme values (a
cross-check by a different algorithm).  The two verdicts must agree.  It also
compares the automaton with the first `--blocks` actual blocks of each set:
every actual block word must be an automaton path and every exact tail
enclosure must lie in the envelope of its state.  That comparison is a sanity
check; the certificate does not depend on it.

Finite computation versus proof: a passing depth is an exact finite fact.
That a passing test implies irrationality of D_P is proved in the paper (the
decoding criterion in the long record) and is not executed here.  A set with
no passing depth up to the limit is undecided by this automaton at that
depth; nothing is claimed about its rationality.

Examples:
    python3 sweep.py --size 3 --bound 31 --max-depth 4 --output triple_sweep.json
    python3 sweep.py --size 4 --bound 31 --max-depth 3 --output four_prime_sweep.json
"""

from __future__ import annotations

import argparse
import hashlib
import json
import sys
import time
from collections import Counter
from itertools import combinations
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from certificate import (  # noqa: E402
    build_automaton,
    check_actual_paths,
    decode,
    exact_envelopes,
    float_text,
    fraction_text,
    is_prime,
    outer_envelopes,
    run_record,
    type_text,
)


def first_pass(aut, env, max_depth):
    for depth in range(1, max_depth + 1):
        result = decode(aut, env, depth)
        if result["passed"]:
            return depth, result["least_gap"], None
    worst = result["overlaps"][0] if result["overlaps"] else None
    return None, None, worst


def sweep(size: int, bound: int, max_depth: int, blocks: int, outer: bool = True) -> dict:
    primes = [n for n in range(2, bound + 1) if is_prime(n)]
    rows = []
    for P in combinations(primes, size):
        aut = build_automaton(P)
        exact_env = exact_envelopes(aut)
        depth, gap, worst = first_pass(aut, exact_env, max_depth)
        row = {
            "primes": list(P),
            "states": len(aut.states),
            "first_passing_depth": depth,
            "least_gap": fraction_text(gap),
            "least_gap_float": float_text(gap),
        }
        if worst is not None:
            (a, b), amount = worst
            row["largest_overlap_at_limit"] = {"types": [type_text(a), type_text(b)],
                                               "length": float_text(amount)}
        if outer:
            outer_env = outer_envelopes(aut)
            outer_depth, outer_gap, _ = first_pass(aut, outer_env, max_depth)
            row["outer_first_passing_depth"] = outer_depth
            row["outer_least_gap_float"] = float_text(outer_gap)
            row["methods_agree"] = outer_depth == depth
        if blocks:
            row["actual_path_check"] = check_actual_paths(aut, exact_env, blocks)
        rows.append(row)
    counts = Counter(row["first_passing_depth"] for row in rows)
    summary = {
        "sets": len(rows),
        "passing": sum(1 for row in rows if row["first_passing_depth"] is not None),
        "by_first_passing_depth": {str(k): counts[k] for k in sorted(k for k in counts if k)},
        "undecided_through_max_depth": counts[None],
        "methods_agree_everywhere": all(row.get("methods_agree", True) for row in rows),
        "actual_path_violations": sum(row.get("actual_path_check", {}).get("violations", 0)
                                      for row in rows),
    }
    return {"size": size, "bound": bound, "max_depth": max_depth, "summary": summary, "sets": rows}


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    parser.add_argument("--size", type=int, default=3)
    parser.add_argument("--bound", type=int, default=31)
    parser.add_argument("--max-depth", type=int, default=4)
    parser.add_argument("--blocks", type=int, default=400,
                        help="actual blocks compared with the automaton (0 to skip)")
    parser.add_argument("--no-outer", action="store_true",
                        help="skip the outward-rounded method (exact envelopes only)")
    parser.add_argument("--output", type=Path, help="write the JSON receipt here")
    args = parser.parse_args(argv)
    started = time.time()
    report = sweep(args.size, args.bound, args.max_depth, args.blocks, outer=not args.no_outer)
    report["scope"] = (
        "Exact rational arithmetic. A passing depth certifies, through the decoding criterion "
        "proved in the paper, that D_P is irrational. An undecided set is undecided by this "
        "automaton at this depth only. The actual-block comparison is a sanity check.")
    report["run"] = run_record(Path(__file__).resolve(), {
        "size": args.size, "bound": args.bound, "max_depth": args.max_depth,
        "blocks": args.blocks, "outer": not args.no_outer}, started)
    library = Path(__file__).resolve().parent / "certificate.py"
    report["run"]["library"] = library.name
    report["run"]["library_sha256"] = hashlib.sha256(library.read_bytes()).hexdigest()
    if args.output:
        args.output.write_text(json.dumps(report, indent=1, ensure_ascii=False) + "\n",
                               encoding="utf-8")
    s = report["summary"]
    print(f"{s['passing']} of {s['sets']} sets of {args.size} primes <= {args.bound} pass by "
          f"depth {args.max_depth}: {s['by_first_passing_depth']}; undecided "
          f"{s['undecided_through_max_depth']}; methods agree: {s['methods_agree_everywhere']}; "
          f"actual-path violations: {s['actual_path_violations']}")
    ok = s["methods_agree_everywhere"] and s["actual_path_violations"] == 0
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
