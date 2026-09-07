#!/usr/bin/env python3
"""Erdos 257 -- is the carry look-ahead really target-dependent, or was it the seed?

WHY THIS EXISTS
---------------
`carry_window_automaton.py` reported look-ahead L ~ 7 for 1/21, 4/9, 1/465 but
"L >= 40" (sentinel 99) for y = 1/2, at every m.  Two problems with reading that
as mathematics:

  (1) its L is measured by bisimulating seeds a = 0 and b = BIG = 64 under
      C <- (tau_A + C)//2, which halves their difference each step.  So
      L ~ log2(64) = 6 is forced by the SEED RANGE, not by the carry.  The
      reported "min 7 median 7" is very close to log2(BIG)+1.
  (2) the cap is `for L in range(1,40)`, and failure writes the sentinel 99,
      which then prints inside a min/median/p90/max summary as if it were a value.

THE HONEST QUANTITY.  The carry C[m] is computable exactly from the target:
C[m] = floor(2^m p / q) - sum_{j<=m} tau_A(j) 2^(m-j).  So define

    Lstar(m) = min { L : running C <- (tau_A + C)//2 down from seed 0 at m+L
                         reproduces C[m] exactly }.

No bisimulation, no seed constant, no sentinel below the cap.  That is what the
"is the carry a finite-window function of tau_A" question actually asks.

PREDICTIONS, written before running
-----------------------------------
P1.  Lstar is SMALL and comparable across ALL targets (order 5-15).  The
     apparent 1/2 anomaly is then an artefact of the seed/cap, and the
     even-denominator hypothesis is dead.
P2.  If instead the even-q targets (q = 2,4,8,512,1024,2048,4096) all show
     large Lstar while the odd-q controls (q = 21,9,465,5,3,7) stay small,
     the even-denominator/terminating-eps hypothesis SURVIVES this test.

FALSIFIER for P2, stated in advance: a single even-q target with small Lstar,
or a single odd-q control with large Lstar, kills the hypothesis outright.

CAVEAT carried from the corpus (T56b/T57d): survivor fraction 0.623 = 1/E is
exactly the measure prediction, so deep survival is what a GENERIC point does
and is never on its own evidence of a counterexample.

Bound directions:
  analysis -> here : RunLengthMarginLawAndDivisorMultiplicity.md s10 (constraint
                     system), s11 (forward recursion); CertificateSocketCollapse.md s81
  here -> analysis : CertificateSocketCollapse.md s82, receipt under state/
"""
from __future__ import annotations
import sys, json, hashlib
from pathlib import Path

problem_id = "erdos_257"

sys.path.insert(0, "public-source-redacted://scripts")
from cantor_staircase_run_length_lab import Engine

REPO = Path("public-source-redacted://ai_workflow")
D = int(sys.argv[1]) if len(sys.argv) > 1 else 6000
LCAP = int(sys.argv[2]) if len(sys.argv) > 2 else 200

EVEN_Q = [("1/2", 1, 2), ("1/4", 1, 4), ("3/8", 3, 8), ("1/512", 1, 512),
          ("5/1024", 5, 1024), ("1013/2048", 1013, 2048), ("7/4096", 7, 4096)]
ODD_Q  = [("1/21", 1, 21), ("4/9", 4, 9), ("1/465", 1, 465),
          ("1/5", 1, 5), ("1/3", 1, 3), ("1/7", 1, 7)]

eng = Engine(D)
rows = []

for label, targets in (("even_q", EVEN_Q), ("odd_q", ODD_Q)):
    for name, p, q in targets:
        r = eng.run(p, q)
        if r["status"] != "alive":
            rows.append({"cohort": label, "target": name, "q": q,
                         "status": r["status"]})
            continue
        w = r["word"]; M = len(w)
        A = [i + 1 for i, b in enumerate(w) if b]
        tauA = [0] * (M + 2)
        for d in A:
            for m in range(d, M + 1, d): tauA[m] += 1
        # exact carry, integer arithmetic only
        N = 0; C = [0] * (M + 2); pw = 1
        for m in range(1, M + 1):
            N = 2 * N + tauA[m]; pw <<= 1
            C[m] = (pw * p) // q - N
        lo, hi = M // 3, min(M // 3 + 800, M - LCAP - 5)
        BIGSEED = 4 * max(C[1:M + 1]) + 8
        Lstar, unresolved = [], 0
        Lstar_up, unresolved_up = [], 0
        for m in range(lo, hi):
            hit = None
            for L in range(1, LCAP + 1):
                a = 0
                for j in range(m + L, m, -1): a = (tauA[j] + a) // 2
                if a == C[m]: hit = L; break
            if hit is None: unresolved += 1
            else: Lstar.append(hit)
            hit_up = None
            for L in range(1, LCAP + 1):
                b = BIGSEED
                for j in range(m + L, m, -1): b = (tauA[j] + b) // 2
                if b == C[m]: hit_up = L; break
            if hit_up is None: unresolved_up += 1
            else: Lstar_up.append(hit_up)
        Lstar_up.sort()
        Lstar.sort()
        n = len(Lstar)
        rows.append({
            "cohort": label, "target": name, "q": q, "status": "alive",
            "depth": M, "range": [lo, hi], "n_resolved": n,
            "n_unresolved": unresolved,
            "Lstar_min": Lstar[0] if n else None,
            "Lstar_median": Lstar[n // 2] if n else None,
            "Lstar_max": Lstar[-1] if n else None,
            "max_C": max(C[1:M + 1]),
            "Lstar_up_min": Lstar_up[0] if Lstar_up else None,
            "Lstar_up_median": Lstar_up[len(Lstar_up) // 2] if Lstar_up else None,
            "Lstar_up_max": Lstar_up[-1] if Lstar_up else None,
            "n_unresolved_up": unresolved_up,
            "eps_all_zero_tail": (q & (q - 1)) == 0,
        })
        print(f"{label:>6} {name:>10} q={q:<5} "
              f"Lstar min/med/max = "
              f"{rows[-1]['Lstar_min']}/{rows[-1]['Lstar_median']}/{rows[-1]['Lstar_max']}"
              f"  unresolved={unresolved}/{hi-lo}  maxC={rows[-1]['max_C']}"
              f"  ||  FROM ABOVE: med={rows[-1]['Lstar_up_median']} "
              f"max={rows[-1]['Lstar_up_max']} unresolved_up={unresolved_up}/{hi-lo}")

out = REPO / "state/formal_math/erdos257_period_noncollapse/carry_lookahead_parity_receipt.json"
blob = json.dumps({"depth": D, "Lcap": LCAP, "rows": rows}, indent=2, sort_keys=True)
out.parent.mkdir(parents=True, exist_ok=True)
out.write_text(blob)
print("wrote", out, "sha256=" + hashlib.sha256(blob.encode()).hexdigest()[:16])
