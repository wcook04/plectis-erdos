#!/usr/bin/env python3
"""Erdos 257: deep stress-audit of the repair-supply producers (M120R)/(CD120)/(PM120).

Analysis note: formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos257/TwentyOneRepairSupplyDeepAudit.md
Receipt:       state/formal_math/erdos257_period_noncollapse/twenty_one_repair_supply_deep_receipt.json
Engine:        formal_math/erdos257_hole_geometry/scripts/primorial_producer_falsification.py::orbit
               (rigorously bracketed; zero undecided decisions; validated against the sha256-pinned
               canonical itinerary and the certified fixed-point greedy).

WHY THIS AUDIT EXISTS.  `RecordCofinitenessBoundary.md` reduces a disproof of Erdos 257 to a cofinal
supply of one-step repairs

    (M120R)   f(120k) >= Q_(120k-1) + t_(120k)        [t=1 on this column]
    (CD120)   Q_(120k) <= Q_(120k-1)                  [unconditional carry-descent form]
    (PM120)   sum_(d|120k, d<120k) b_d >= Q_(120k-1)+1 [past-owned proper load]

and its companion audit verified all three on every multiple of 120 through rank 2,000,002 with zero
violations.  The stronger past-owned seven-column shortcut (PU120) ALSO passed 2,000,002 and then
failed first at rank 3,175,080 (17 violations by rank 20M).  A producer that survived one audit
horizon has already once been a trap; nobody should attempt an all-depth proof of (M120R) before the
same horizon that killed (PU120) has been applied to it.  This script applies exactly that horizon.

WHAT IS AUDITED at DEPTH = 20,000,002, all exact integer arithmetic on the validated orbit:

  1. (M120R)/(CD120) margins f(120k) - Q_(120k-1) - 1 for all 166,666 rows;
  2. (PM120) margins g(120k) - Q_(120k-1) - 1 with g the proper-divisor load;
  3. the seven U_30 columns at the same rows, separating payment that stays inside the dead
     past-owned shortcut from payment that genuinely needs the full divisor load;
  4. the GLOBAL repair census f(n) >= Q_(n-1) + t_n at every rank (density, maximum gap, last gap),
     because the boundary theorem consumes cofinality of repairs, of which the 120-column is only
     the conjectured periodic subfamily;
  5. strict-record statistics (count, maximum defect, phase of record successors) as cross-checks
     against the landed 2,000,002-receipt and the 20M running-maximum receipt.

NON-CLAIM.  Finite survival is falsification coverage, not proof.  This audit does not decide 1/21
membership and does not prove Erdos 257.  A violation would be a theorem-grade redirection exactly
like the (PU120) falsification.
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
    "state/formal_math/erdos257_period_noncollapse/twenty_one_repair_supply_deep_receipt.json")
DEPTH = 20_000_002
PINNED_RANK, PINNED_COUNT = 500_002, 249_858
EQ_ROWS_2M = [999480, 1699080, 1905240]


def main() -> int:
    t0 = time.time()

    # --- validation: pinned itinerary count (engine self-check on this depth class)
    selp, _, undp, _, _ = ppf.orbit(1, 21, PINNED_RANK)
    pinned_ok = int(selp[:PINNED_RANK + 1].sum()) == PINNED_COUNT and not undp

    # --- the deep orbit (validated engine, ~45s)
    sel, cnt, undec, min_margin, bracket = ppf.orbit(1, 21, DEPTH)

    n_all = np.arange(1, DEPTH + 1, dtype=np.int64)
    t = (n_all % 6 == 0) | (n_all % 6 == 5)
    f_all = cnt[1:DEPTH + 1].astype(np.int64)

    # defect recurrence Q_n = 2 Q_(n-1) + t_n - f(n)
    Q = np.empty(DEPTH + 1, dtype=np.int64)
    Q[0] = 0
    for n in range(1, DEPTH + 1):
        Q[n] = 2 * Q[n - 1] + (1 if t[n - 1] else 0) - int(f_all[n - 1])

    # --- global repair census: repair at n iff f(n) >= Q_(n-1) + t_n
    rep_margin = f_all - Q[:DEPTH] - t.astype(np.int64)
    repairs = rep_margin >= 0
    rep_idx = n_all[repairs]
    gaps = np.diff(rep_idx)
    nonrecords = Q[1:DEPTH + 1] <= np.maximum.accumulate(Q[:DEPTH])
    runmax = np.maximum.accumulate(Q)
    record_mask = Q[1:DEPTH + 1] > runmax[:DEPTH]
    record_ranks = n_all[record_mask]
    maxQ = int(Q.max())
    maxQ_rank = int(Q.argmax())

    # repair-gap growth law by decade of rank: decides whether a cofinality proof
    # must show bounded gaps, logarithmic gaps, or something weaker
    gstart = np.searchsorted(rep_idx, np.array([10 ** e for e in range(1, 9)]))
    gap_by_decade = []
    for e in range(len(gstart)):
        lo = int(gstart[e])
        hi = int(gstart[e + 1]) if e + 1 < len(gstart) else len(gaps)
        seg = gaps[lo:hi]
        if len(seg):
            gap_by_decade.append({"ranks": f"{10**(e+1)}-{10**(e+2) if e+1 < 8 else DEPTH}",
                                  "repairs": int(len(seg)),
                                  "max_gap": int(seg.max()),
                                  "mean_gap": round(float(seg.mean()), 3)})
    late_rep = rep_idx[rep_idx > 3_200_000]
    residue_classes_used = int(len(np.unique(late_rep % 120)))

    # --- the 120-column rows
    rows = np.arange(120, DEPTH + 1, 120, dtype=np.int64)
    m120_margin = cnt[rows] - Q[rows - 1] - 1          # (M120R) = (CD120)
    b_self = sel[rows].astype(np.int64)
    pm120_margin = (cnt[rows] - b_self) - Q[rows - 1] - 1  # (PM120)
    ks = rows // 120
    cols = np.stack([cnt[60 * ks], cnt[40 * ks], cnt[24 * ks],
                     cnt[20 * ks], cnt[12 * ks], cnt[8 * ks], cnt[4 * ks]], axis=1)
    u30 = (cols[:, 0] + cols[:, 1] + cols[:, 2]
           - cols[:, 3] - cols[:, 4] - cols[:, 5] + cols[:, 6]) - Q[rows - 1] - 1

    def worst(idx_margin: np.ndarray, count: int) -> list[list[int]]:
        order = np.argsort(idx_margin)[:count]
        return [[int(rows[i]), int(idx_margin[i])] for i in order]

    v120 = np.nonzero(m120_margin < 0)[0]
    vpm = np.nonzero(pm120_margin < 0)[0]
    vu30 = np.nonzero(u30 < 0)[0]

    # per-decade minimum margin drift of (M120R)
    decade = np.log10(ks).astype(int)
    drift = []
    for dec in range(decade.min(), decade.max() + 1):
        mask = decade == dec
        if mask.any():
            drift.append({"decade_of_k": dec,
                          "rows": int(mask.sum()),
                          "min_margin": int(m120_margin[mask].min()),
                          "mean_margin": round(float(m120_margin[mask].mean()), 2),
                          "equalities": int((m120_margin[mask] == 0).sum())})

    def anatomy(row_i: int) -> dict:
        n = int(rows[row_i]); k = int(ks[row_i])
        fs = ppf.factor(k)
        return {"n": n, "k": k,
                "k_kind": "prime" if len(fs) == 1 and sum(fs.values()) == 1 else
                          ("one" if k == 1 else "composite"),
                "k_factorisation": {str(a): b for a, b in sorted(fs.items())},
                "f_n": int(cnt[n]), "b_n": int(sel[n]),
                "proper_load": int(cnt[n]) - int(sel[n]),
                "U_30": int(u30[row_i] + Q[n - 1] + 1),
                "Q_prev": int(Q[n - 1]),
                "M120R_margin": int(m120_margin[row_i]),
                "PM120_margin": int(pm120_margin[row_i]),
                "PU120_margin": int(u30[row_i]),
                "seven_columns_f_60m_40m_24m_20m_12m_8m_4m":
                    [int(x) for x in cols[row_i]]}

    tightest = np.argsort(m120_margin)[:12]
    payload = {
        "depth": DEPTH,
        "engine": "primorial_producer_falsification.orbit (bracketed, zero-undecided)",
        "validations": {
            "pinned_match_at_500002": bool(pinned_ok),
            "undecided_decisions": len(undec),
            "rigorous_error_bracket_units": bracket,
            "min_abs_decision_margin_units": min_margin,
            "reproduced_2M_equality_rows_still_exact":
                [int(rows[i]) for i in range(len(rows))
                 if rows[i] in EQ_ROWS_2M and m120_margin[i] == 0],
        },
        "M120R_CD120": {
            "rows": int(len(rows)),
            "violations": int(len(v120)),
            "first_violation_rank": int(rows[v120[0]]) if len(v120) else None,
            "min_margin": int(m120_margin.min()),
            "equality_count": int((m120_margin == 0).sum()),
            "tightest_rows": worst(m120_margin, 12),
            "margin_drift_by_decade_of_k": drift,
        },
        "PM120": {
            "violations": int(len(vpm)),
            "first_violation_rank": int(rows[vpm[0]]) if len(vpm) else None,
            "min_margin": int(pm120_margin.min()),
            "equality_count": int((pm120_margin == 0).sum()),
            "tightest_rows": worst(pm120_margin, 8),
        },
        "PU120_crosscheck_at_depth": {
            "violations": int(len(vu30)),
            "first_violation_rank": int(rows[vu30[0]]) if len(vu30) else None,
            "min_margin": int(u30.min()),
        },
        "global_repair_census": {
            "repair_count": int(repairs.sum()),
            "repair_density": round(float(repairs.mean()), 6),
            "maximum_gap": int(gaps.max()) if len(gaps) else None,
            "argmax_gap_after_rank": int(rep_idx[int(np.argmax(gaps))]) if len(gaps) else None,
            "last_repair_rank": int(rep_idx[-1]) if len(rep_idx) else None,
            "gap_law_by_decade": gap_by_decade,
            "residue_classes_mod_120_used_after_3.2M": residue_classes_used,
        },
        "record_statistics": {
            "strict_record_count": int(record_mask.sum()),
            "max_defect": maxQ,
            "max_defect_rank": maxQ_rank,
            "nonrecord_count": int(nonrecords.sum()),
            "record_ranks_tail": [int(r) for r in record_ranks[-12:]],
        },
        "violation_anatomy": [anatomy(int(i)) for i in v120[:8]],
        "tightest_row_anatomy": [anatomy(int(i)) for i in tightest[:6]],
        "elapsed_seconds": round(time.time() - t0, 1),
    }
    RECEIPT.parent.mkdir(parents=True, exist_ok=True)
    RECEIPT.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n")

    summary = {k: payload[k] for k in
               ("M120R_CD120", "PM120", "PU120_crosscheck_at_depth",
                "global_repair_census", "record_statistics")}
    print(json.dumps(summary, indent=2))
    print(f"receipt -> {RECEIPT}")
    ok = (pinned_ok and len(undec) == 0
          and len(vu30) > 0)  # the PU120 falsification must reproduce at this depth
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
