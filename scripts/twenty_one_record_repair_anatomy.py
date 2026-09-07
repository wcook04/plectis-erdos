#!/usr/bin/env python3
"""Erdos 257: record-to-repair anatomy on the canonical 1/21 orbit.

Analysis note: formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos257/TwentyOneRepairSupplyDeepAudit.md
Receipt:       state/formal_math/erdos257_period_noncollapse/twenty_one_record_repair_anatomy_receipt.json
Engine:        primorial_producer_falsification.orbit (bracketed, zero-undecided).

MOTIVATION.  Two independent facts meet here:

  * `RecordCofinitenessBoundary.md`: under non-membership every late rank is a
    strict record, so a bounded post-record repair law would contradict the
    fatal branch whenever records persist; and if records stop, the defect is
    bounded, which feeds the existing subexponential membership endpoint.
  * The deep repair audit: maximum global repair gap is 11 through rank
    20,000,002 even though the defect reaches 128.

So the sharpest local question is: how far after each strict record does the
next one-step repair land, and what pays it?  This script answers exactly that,
per record, with divisor anatomy of the paying rank.
"""
from __future__ import annotations

import importlib.util
import json
import pathlib
import sys
import time

import numpy as np

HERE = pathlib.Path(__file__).resolve()
sys.path.insert(0, str(HERE.parents[2] / "erdos257_hole_geometry" / "scripts"))

_spec = importlib.util.spec_from_file_location(
    "ppf",
    HERE.parents[2] / "erdos257_hole_geometry" / "scripts" / "primorial_producer_falsification.py")
ppf = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(ppf)

RECEIPT = pathlib.Path(
    "state/formal_math/erdos257_period_noncollapse/twenty_one_record_repair_anatomy_receipt.json")
DEPTH = 20_000_002


def main() -> int:
    t0 = time.time()
    sel, cnt, undec, min_margin, bracket = ppf.orbit(1, 21, DEPTH)
    assert not undec

    n_all = np.arange(1, DEPTH + 1, dtype=np.int64)
    t = ((n_all % 6 == 0) | (n_all % 6 == 5)).astype(np.int64)
    f_all = cnt[1:DEPTH + 1].astype(np.int64)

    Q = np.empty(DEPTH + 1, dtype=np.int64)
    Q[0] = 0
    for n in range(1, DEPTH + 1):
        Q[n] = 2 * Q[n - 1] + int(t[n - 1]) - int(f_all[n - 1])

    runmax = np.maximum.accumulate(Q[:DEPTH])
    record_mask = Q[1:DEPTH + 1] > runmax[:DEPTH]
    record_ranks = n_all[record_mask]
    rep_margin = f_all - Q[:DEPTH] - t
    repair_at = rep_margin >= 0

    # next repair strictly after each record (repair at rank m uses f(m), so a
    # record at R can itself be followed by repair at R+1 at the earliest)
    rep_positions = np.nonzero(repair_at)[0]          # 0-based rank index: rank = pos+1
    rows = []
    for r in record_ranks.tolist():
        j = int(np.searchsorted(rep_positions, r))     # first repair position >= r
        # search from rank r+1 onward: positions > r-1 (0-based pos of rank p is p-1)
        j = int(np.searchsorted(rep_positions, r))     
        while j < len(rep_positions) and rep_positions[j] <= r - 1:
            j += 1
        if j >= len(rep_positions):
            rows.append({"record_rank": r, "defect": int(Q[r]),
                         "next_repair_rank": None})
            continue
        p = int(rep_positions[j]) + 1                  # repairing rank
        d = p - r
        fs = ppf.factor(p)
        rows.append({
            "record_rank": r, "defect": int(Q[r]),
            "next_repair_rank": p, "distance": d,
            "f_paying": int(cnt[p]), "t_paying": int(t[p - 1]),
            "tau_paying_bound_kind": ("prime" if len(fs) == 1 and sum(fs.values()) == 1
                                      else "composite"),
            "paying_factorisation": {str(a): b for a, b in sorted(fs.items())},
        })

    dists = [row["distance"] for row in rows if row["next_repair_rank"] is not None]
    payload = {
        "depth": DEPTH,
        "engine_validations": {
            "undecided_decisions": len(undec),
            "min_abs_decision_margin_units": min_margin,
            "rigorous_error_bracket_units": bracket,
        },
        "strict_record_count": len(rows),
        "unrepaired_records": [r for r in rows if r["next_repair_rank"] is None],
        "max_record_to_repair_distance": max(dists) if dists else None,
        "distance_histogram": {str(dv): dists.count(dv) for dv in sorted(set(dists))},
        "records_with_anatomy": rows,
        "elapsed_seconds": round(time.time() - t0, 1),
    }
    RECEIPT.parent.mkdir(parents=True, exist_ok=True)
    RECEIPT.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n")
    print(json.dumps({k: v for k, v in payload.items()
                      if k != "records_with_anatomy"}, indent=2))
    print("first six record anatomies:")
    for row in rows[:6]:
        print(json.dumps(row))
    print(f"receipt -> {RECEIPT}")
    return 0 if (len(undec) == 0 and dists) else 1


if __name__ == "__main__":
    raise SystemExit(main())
