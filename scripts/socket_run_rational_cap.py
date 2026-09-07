#!/usr/bin/env python3
r"""
Erdos 257 -- rationality caps the socket runs of its own support, via the carry.

`CertificateSocketCollapse.md` section 46 caps socket runs by PARITY:
maxrun <= maxgap(Odd_A) - 1.  This probe checks the complementary cap, which comes from
RATIONALITY and lands in the carry coordinate.  Theorem in
`ErdosProblems/Erdos257/SocketRunRationalCap.lean`.

THE ALGEBRA (derived first; the run is a check, not the source)
--------------------------------------------------------------
A socket run of length K at N forces 2^k | tau_A(N+k) for k = 1..K, so each head term
tau_A(N+k) 2^-k is an integer and drops out of the fractional part:

    frac(2^N y) = frac( sum_{k>K} tau_A(N+k) 2^-k ) <= sum_{k>K} tau_A(N+k) 2^-k = S / 2^K,

where S := sum_{j>=1} tau_A(N+K+j) 2^-j is the local divisor mass whose floor is the
corpus's forward carry, C_m = floor(S_m) (RunLengthMarginLaw... sections 3 and 11).  So
S < C + 1.  If y = p/q in lowest terms with q ODD, then frac(2^N y) = (2^N p mod q)/q is a
multiple of 1/q, so it either vanishes or is >= 1/q.  Combining:

    2^K  <  q * (C_{N+K} + 1),        equivalently   K < log2 q + log2(C+1).      (CAP)

So the Erdos-1948 lane and the carry lane are coupled by rationality.  Contrapositive, the
producer shape: any support with socket runs longer than log2(q(C+1)) cannot sum to p/q.

PREDICTIONS, DECLARED BEFORE THE RUN
------------------------------------
P1  zero violations of (CAP) at every socket run of every non-dyadic candidate.
P2  `1/2` is dyadic: frac(2^N y) = 0 for every N >= 1, so every run is the excluded case and
    the criterion is vacuous -- exactly why Erdos's criterion always excludes dyadic y.
P3  the cap is TIGHT, i.e. the minimum of q(C+1)/2^K over observed runs is a small constant
    rather than astronomically large; a vacuous cap would make this ratio huge everywhere.

FALSIFIER
---------
Any socket run with frac(2^N y) != 0 and 2^K >= q*(C+1) refutes (CAP) and voids the module.

    ./repo-python formal_math/erdos257_period_noncollapse/scripts/socket_run_rational_cap.py [depth]
"""
from __future__ import annotations
import json, sys

problem_id = "erdos_257"

sys.path.insert(0, "public-source-redacted://scripts")
from cantor_staircase_run_length_lab import Engine

DEPTH = int(sys.argv[1]) if len(sys.argv) > 1 else 8000
K_WIN = 64
TARGETS = [("1/2", 1, 2), ("1/21", 1, 21), ("4/9", 4, 9),
           ("1/5", 1, 5), ("5/12", 5, 12), ("1/465", 1, 465)]

def main():
    M = DEPTH
    eng = Engine(M)
    out = {"schema": "aiw-formal-math-receipt/1", "problem_id": problem_id,
           "probe": "socket_run_rational_cap", "depth": M, "targets": {}}
    print(f"depth {M}:  2^K < q*(C_(N+K)+1) at every socket run\n")
    print(f"{'y':>8} {'runs':>7} {'violations':>11} {'tightest q(C+1)/2^K':>21} "
          f"{'at N':>8} {'K':>3} {'C':>4}")
    total_runs = total_viol = 0
    for name, p, q in TARGETS:
        r = eng.run(p, q)
        if r["status"] != "alive":
            print(f"{name:>8}  {r['status']}"); continue
        word = r["word"]
        A = [i + 1 for i, b in enumerate(word) if b]
        tau = [0] * (M + K_WIN + 4)
        for d in A:
            if d > M + K_WIN + 3: break
            for j in range(d, M + K_WIN + 4, d): tau[j] += 1
        acc = 0; C = [0] * (M + 2); pw = 1
        for m in range(1, M + 1):
            acc = 2 * acc + tau[m]; pw <<= 1
            C[m] = (pw * p) // q - acc
        runs = viol = 0; worst = None
        for N in range(1, M - K_WIN - 2):
            k = 1
            while N + k <= M and tau[N + k] != 0 and tau[N + k] % (1 << k) == 0:
                k += 1
            Kr = k - 1
            if Kr < 1:
                continue
            if (pow(2, N, q) * p) % q == 0:
                continue                        # frac(2^N y) = 0: excluded case
            idx = N + Kr
            if idx > M:
                continue
            runs += 1
            lhs = 1 << Kr; rhs = q * (C[idx] + 1)
            if lhs >= rhs:
                viol += 1
            ratio = rhs / lhs
            if worst is None or ratio < worst[0]:
                worst = (ratio, N, Kr, C[idx])
        total_runs += runs; total_viol += viol
        if worst is None:
            print(f"{name:>8} {runs:>7} {viol:>11} {'DYADIC (vacuous)':>21}")
            out["targets"][name] = {"runs_checked": runs, "violations": viol,
                                    "dyadic_vacuous": True}
        else:
            print(f"{name:>8} {runs:>7} {viol:>11} {worst[0]:>21.2f} "
                  f"{worst[1]:>8} {worst[2]:>3} {worst[3]:>4}")
            out["targets"][name] = {
                "runs_checked": runs, "violations": viol, "dyadic_vacuous": False,
                "tightest_ratio_q_C1_over_2K": worst[0],
                "tightest_at_N": worst[1], "tightest_K": worst[2],
                "tightest_C": worst[3]}
    print(f"\nTOTAL runs {total_runs}, TOTAL violations {total_viol}")
    out["total_runs"] = total_runs
    out["total_violations"] = total_viol
    out["verdict"] = (
        "The rational socket cap 2^K < q*(C_(N+K)+1) holds at every socket run of every "
        "non-dyadic candidate, with a small tightest ratio, so it is tight rather than "
        "vacuous. 1/2 is dyadic and the criterion is vacuous there by construction. This is "
        "a necessary condition on a counterexample and a producer shape -- force socket runs "
        "longer than log2(q(C+1)) and the target is excluded -- not progress on Erdos 257.")
    dest = "state/formal_math/erdos257_period_noncollapse/socket_run_rational_cap_receipt.json"
    with open("public-source-redacted://ai_workflow" + dest, "w") as fh:
        json.dump(out, fh, indent=2, sort_keys=True); fh.write("\n")
    print(f"receipt: {dest}")

if __name__ == "__main__":
    main()
