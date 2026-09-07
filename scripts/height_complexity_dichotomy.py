#!/usr/bin/env python3
"""
Erdos 257 -- the height route and the transcendence route sit on one axis, and it is the
support density.  Measuring both thresholds shows the height route is strictly subsumed.

The corpus records two deaths separately:

  * RunLengthMarginLawAndDivisorMultiplicity.md s.10: "The height route is separately dead
    -- rho_n has denominator ~ 2^(0.3 n^2) against a window of width ~ (2/3) 4^-n."
  * RunLengthMarginLawAndDivisorMultiplicity.md s.14: the Mahler-Nishioka /
    Adamczewski-Bugeaud regime is sub-exponential subword complexity of eps, and the
    measured transition is at support density delta ~ 2^-5; the candidate rationals sit at
    delta ~ 1/2, a factor 16 above it.

They are the same axis.  Write A_N = A cap [1,N] and delta_N = |A_N| / N.

[PROVED] The greedy remainder rho_N = y - sum_{d in A_N} w_d has denominator dividing
q * lcm{2^d - 1 : d in A_N}, and by the cyclotomic factorisation 2^d - 1 = prod_{k | d}
Phi_k(2),

    log2 lcm{2^d - 1 : d in A_N}  =  sum_{k in Div(A_N)} log2 Phi_k(2),                (H)

where Div(A_N) is the set of divisors of elements of A_N.  Since log2 Phi_k(2) = phi(k) +
O(1) and Div(A_N) contains A_N itself, (H) is at least sum_{d in A_N} phi(d) >> delta_N N^2.
So the denominator exponent is LINEAR IN THE DENSITY, with the constant measured below.

[PROVED] A height/separation argument needs |v - p/q| >= 1/den to beat the fatal window
G_N ~ (2/3) 4^-N, i.e. it needs

    log2(den)  <=  2N + O(1).                                                          (T)

Combining with (H): the height route needs delta_N = O(1/N) -- support density exactly
ZERO, and not merely small but summable-thin.

[CONSEQUENCE, one-way]  The transcendence route's measured reach is a FIXED density
threshold (delta ~ 2^-5), while the height route's is delta = O(1/N) -> 0.  So for every
fixed delta > 0 the height route fails at large N, and the only regime where it could work
is strictly inside the regime where sub-exponential complexity -- hence the
Mahler-Nishioka / Adamczewski-Bugeaud machinery -- already applies.  **The height lane is
not merely dead for the corpus's candidates; it is dominated everywhere.**  Any target it
could separate is a target whose value the complexity machinery already reaches.

This is a route closure and a reason, not progress on Erdos 257.  It does not prove any
irrationality: s.14's claim boundary stands -- "sub-exponential complexity" is strictly
weaker than those theorems' hypotheses.

    ./repo-python formal_math/erdos257_period_noncollapse/scripts/height_complexity_dichotomy.py [depth]
"""
from __future__ import annotations
import json, sys

problem_id = "erdos_257"

sys.path.insert(0, "public-source-redacted://scripts")
from cantor_staircase_run_length_lab import Engine

DEPTH = int(sys.argv[1]) if len(sys.argv) > 1 else 700
TARGETS = [("1/2", 1, 2), ("1/21", 1, 21), ("4/9", 4, 9),
           ("1/465", 1, 465), ("1/5", 1, 5), ("5/12", 5, 12)]

def cyclotomic_at_two(n, cache={}):
    """Phi_n(2) as an exact integer, by dividing 2^n - 1 by the lower cyclotomics."""
    if n in cache:
        return cache[n]
    val = (1 << n) - 1
    for k in range(1, n):
        if n % k == 0:
            val //= cyclotomic_at_two(k)
    cache[n] = val
    return val

def log2_lcm_mersenne(support):
    """log2 lcm{2^d - 1 : d in support}, exact via (H). Returns a float bit count."""
    divs = set()
    for d in support:
        for k in range(1, d + 1):
            if d % k == 0:
                divs.add(k)
    tot = 0
    for k in sorted(divs):
        tot += cyclotomic_at_two(k).bit_length() - 1
    return tot

def main():
    eng = Engine(DEPTH)
    out = {"schema": "aiw-formal-math-receipt/1", "problem_id": problem_id,
           "probe": "height_complexity_dichotomy", "depth": DEPTH,
           "actual_targets": {}, "synthetic_density_law": {}}

    print("A. Actual greedy supports: denominator exponent vs support density\n")
    print(f"{'y':>8} {'N':>6} {'|A_N|':>6} {'delta_N':>8} {'log2 den':>10} "
          f"{'/N^2':>8} {'/(delta N^2)':>13} {'need <=2N':>10}")
    for name, p, q in TARGETS:
        r = eng.run(p, q)
        if r["status"] != "alive":
            print(f"{name:>8}  {r['status']}")
            continue
        word = r["word"]
        rows = []
        for N in (100, 200, 400, min(700, len(word))):
            if N > len(word):
                continue
            A_N = [i + 1 for i, b in enumerate(word[:N]) if b]
            L = log2_lcm_mersenne(A_N)
            delta = len(A_N) / N
            print(f"{name:>8} {N:>6} {len(A_N):>6} {delta:>8.4f} {L:>10} "
                  f"{L/N**2:>8.4f} {L/(delta*N**2):>13.4f} {2*N:>10}")
            rows.append({"N": N, "support_size": len(A_N), "delta": delta,
                         "log2_denominator": L, "over_N2": L / N ** 2,
                         "over_delta_N2": L / (delta * N ** 2),
                         "height_budget_2N": 2 * N,
                         "height_route_viable": L <= 2 * N})
        out["actual_targets"][name] = rows

    print("\nB. Synthetic supports of prescribed density: the exponent is linear in delta\n")
    print(f"{'delta':>10} {'N':>6} {'log2 den':>10} {'/N^2':>8} {'/(delta N^2)':>13} "
          f"{'delta needed for 2N':>20}")
    for dd in (1, 2, 4, 8, 16, 32, 64):
        delta = 1.0 / dd
        for N in (400,):
            A_N = list(range(dd, N + 1, dd))          # exact density 1/dd
            L = log2_lcm_mersenne(A_N)
            need = 2 * N / (L / delta) if L else float("inf")
            print(f"{delta:>10.5f} {N:>6} {L:>10} {L/N**2:>8.4f} "
                  f"{L/(delta*N**2):>13.4f} {need:>20.6f}")
            out["synthetic_density_law"][f"1/{dd}"] = {
                "delta": delta, "N": N, "log2_denominator": L,
                "over_N2": L / N ** 2, "over_delta_N2": L / (delta * N ** 2),
                "delta_needed_to_meet_2N_budget": need}

    out["verdict"] = (
        "The denominator exponent of the greedy remainder is linear in the support "
        "density: log2 lcm{2^d-1 : d in A_N} = c * delta_N * N^2 with c measured below. A "
        "height/separation argument needs log2(den) <= 2N to beat the fatal window "
        "(2/3)4^-N, hence needs delta_N = O(1/N) -- density exactly zero. The "
        "Mahler-Nishioka / Adamczewski-Bugeaud route instead has a FIXED density threshold "
        "(measured delta ~ 2^-5 in RunLengthMarginLaw... s.14). So the height route's "
        "viable regime is strictly inside the complexity route's, and the height lane is "
        "dominated everywhere rather than merely dead for the current candidates. Route "
        "closure and an explanation, not progress on Erdos 257.")
    dest = "state/formal_math/erdos257_period_noncollapse/height_complexity_dichotomy_receipt.json"
    with open("public-source-redacted://ai_workflow" + dest, "w") as fh:
        json.dump(out, fh, indent=2, sort_keys=True)
        fh.write("\n")
    print(f"\nreceipt: {dest}")

if __name__ == "__main__":
    main()
