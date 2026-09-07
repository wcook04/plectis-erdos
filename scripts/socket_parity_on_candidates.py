#!/usr/bin/env python3
r"""
Erdos 257 -- the parity obstruction, pointed at the ACTUAL candidate counterexamples.

`CertificateSocketCollapse.md` section 46 proves the parity obstruction to the Erdos 1948
socket mechanism:  with `Odd_A := {m >= 1 : tau_A(m) odd}`, every socket run must fit
strictly between two consecutive elements of `Odd_A`, so

    maxrun  <=  maxgap(Odd_A) - 1,

and `Odd_A` syndetic makes the mechanism UNAVAILABLE for that support.  Section 66 adds the
complement criterion `Odd_{N\E} = Sq XOR Odd_E`.

**Neither has ever been evaluated on a candidate counterexample.**  Section 46's census
covers `N`, primes, `{2^i}`, `{3^i}`, `3N`; section 66's table covers `{}`, `{2^i}`, primes,
`{2^i} XOR primes`, `4N`.  All are CONSTRUCTED supports.  The corpus's actual candidates --
the greedy supports of `1/2, 1/21, 4/9, 1/465, 1/5, 5/12` -- appear in neither table.  This
probe closes that gap.

THE HANDLE (derived first; the run is a check, not the source)
--------------------------------------------------------------
`RunLengthMarginLawAndDivisorMultiplicity.md` sections 3 and 11 give the carry identity
`eps_m = (tau_A(m) + C_m) mod 2`.  Hence, for the greedy support of any rational target,

    Odd_A  =  { m : tau_A(m) odd }  =  { m : eps_m != C_m mod 2 },              (P)

so `Odd_A` is exactly the disagreement set of the (periodic) digit word and the carry
parity, and `maxgap(Odd_A)` is the longest run on which they AGREE.  Since
`GF2ParityBooleanisation.md` measures the carry parity as high-entropy, the naive model
predicts agreement runs of length ~ log2 M -- unbounded, hence `Odd_A` not syndetic.

PREDICTIONS, DECLARED BEFORE THE RUN
------------------------------------
P1  identity (P) holds at every tested m, for every candidate: 0 violations.
P2  calibrator `A = N` reproduces `Odd_N = Sq` exactly, with maxgap ~ 2 sqrt(M).
P3  for every candidate, maxgap(Odd_A) GROWS with the dyadic band (not syndetic), at a
    rate consistent with ~ log2 M rather than ~ sqrt(M).
P4  observed socket maxrun respects section 46's bound maxrun <= maxgap(Odd_A) - 1.
P5  density(Odd_A) ~ 1/2 for the candidates (against 0 for `Sq`, which is density zero).

FALSIFIER
---------
Any candidate whose maxgap(Odd_A) is FLAT across dyadic bands -- i.e. `Odd_A` syndetic --
refutes P3 and is a genuine discovery: it would make the Erdos-1948 route provably
unavailable for that candidate, and would be an exact non-linear parity regularity of the
greedy support of the kind `CertificateSocketCollapse.md` 73.4 asks for.  Any violation of
P1, P2 or P4 is an instrument error and voids the run.

    ./repo-python formal_math/erdos257_period_noncollapse/scripts/socket_parity_on_candidates.py [depth]
"""
from __future__ import annotations
import json, math, sys

problem_id = "erdos_257"

sys.path.insert(0, "public-source-redacted://scripts")
from cantor_staircase_run_length_lab import Engine

DEPTH = int(sys.argv[1]) if len(sys.argv) > 1 else 20000
TARGETS = [("1/2", 1, 2), ("1/21", 1, 21), ("4/9", 4, 9),
           ("1/465", 1, 465), ("1/5", 1, 5), ("5/12", 5, 12)]

def gaps_by_band(odd_positions, M):
    """max gap between consecutive elements of Odd_A, resolved by dyadic band of m."""
    bands, overall = {}, 0
    prev = 0
    for m in odd_positions:
        g = m - prev
        overall = max(overall, g)
        b = m.bit_length()
        bands[b] = max(bands.get(b, 0), g)
        prev = m
    return overall, bands

def socket_maxrun(tauA, M):
    """longest K with 2^k | tau_A(N+k) for k = 1..K, over all N."""
    best, bestN = 0, 0
    for N in range(1, M - 1):
        k = 1
        while N + k <= M and tauA[N + k] != 0 and tauA[N + k] % (1 << k) == 0:
            k += 1
        if k - 1 > best:
            best, bestN = k - 1, N
    return best, bestN

def main():
    M = DEPTH
    eng = Engine(M)
    out = {"schema": "aiw-formal-math-receipt/1", "problem_id": problem_id,
           "probe": "socket_parity_on_candidates", "depth": M, "targets": {}}

    # ---- calibrator: A = N, where Odd_A must be exactly the perfect squares (P2) ----
    tauN = [0] * (M + 2)
    for d in range(1, M + 1):
        for j in range(d, M + 1, d):
            tauN[j] += 1
    oddN = [m for m in range(1, M + 1) if tauN[m] % 2]
    sq = [k * k for k in range(1, int(math.isqrt(M)) + 1)]
    calib_ok = (oddN == sq)
    gN, _ = gaps_by_band(oddN, M)
    print(f"depth {M}\n")
    print(f"CALIBRATOR  A = N :  Odd_N == squares ? {calib_ok}   maxgap {gN}   "
          f"2*sqrt(M) = {2*math.isqrt(M)}   density {len(oddN)/M:.5f}")
    out["calibrator_A_eq_N"] = {"odd_set_equals_squares": bool(calib_ok),
                                "maxgap": gN, "two_sqrt_M": 2 * math.isqrt(M),
                                "density": len(oddN) / M}
    print()
    print(f"{'y':>7} {'(P) viol':>9} {'|Odd_A| dens':>13} {'maxgap':>7} {'socket maxrun':>14} "
          f"{'bound ok':>9} {'maxTauA':>7} {'magCap':>8} {'parCap':>8} {'binds':>10}   maxgap by dyadic band")
    for name, p, q in TARGETS:
        r = eng.run(p, q)
        if r["status"] != "alive":
            print(f"{name:>7}  {r['status']}"); continue
        word = r["word"]; W = len(word)
        A = [i + 1 for i, b in enumerate(word) if b]
        tauA = [0] * (M + 2)
        for d in A:
            if d > M: break
            for j in range(d, M + 1, d):
                tauA[j] += 1
        # forward integer carry and digit word, exactly as sections 3/11
        acc = 0; C = [0] * (M + 2); pw = 1; eps = [0] * (M + 2)
        for m in range(1, M + 1):
            acc = 2 * acc + tauA[m]; pw <<= 1
            C[m] = (pw * p) // q - acc
            eps[m] = ((pw * p) // q) % 2
        odd = [m for m in range(1, M + 1) if tauA[m] % 2]
        # (P): Odd_A = { m : eps_m != C_m mod 2 }
        viol = sum(1 for m in range(1, M + 1)
                   if (tauA[m] % 2) != ((eps[m] + C[m]) % 2))
        g, bands = gaps_by_band(odd, M)
        mr, mrN = socket_maxrun(tauA, M)
        bound_ok = mr <= g - 1
        bandstr = " ".join(f"b{b}:{bands[b]}" for b in sorted(bands) if b >= 6)
        # WHICH constraint binds: parity (maxgap) or divisor MAGNITUDE?
        # a socket run of length K needs some tau_A(N+k) >= 2^k, so K <= log2(max tau_A).
        mx = max(tauA[1:M + 1]); mxd = max(tauN[1:M + 1])
        mag_cap = int(math.floor(math.log2(mx))) if mx else 0
        par_cap = g - 1
        binding = "magnitude" if mag_cap < par_cap else ("parity" if par_cap < mag_cap else "tie")
        print(f"{name:>7} {viol:>9} {len(odd)/M:>13.5f} {g:>7} {mr:>14} "
              f"{str(bound_ok):>9} {mx:>7} {mag_cap:>8} {par_cap:>8} {binding:>10}   {bandstr}")
        out["targets"][name] = {
            "parity_identity_violations": viol,
            "odd_density": len(odd) / M, "maxgap_Odd_A": g,
            "socket_maxrun": mr, "socket_maxrun_at_N": mrN,
            "section46_bound_holds": bool(bound_ok),
            "max_tau_A": mx, "max_d": mxd,
            "magnitude_cap_log2_max_tau_A": mag_cap,
            "parity_cap_maxgap_minus_1": par_cap,
            "binding_constraint": binding,
            "maxgap_by_bit_length": {str(k): v for k, v in sorted(bands.items())},
            "support_density": len([a for a in A if a <= M]) / M}
    print("\n(P) viol = violations of Odd_A = {m : eps_m != C_m mod 2}; 0 = exact.")
    print("bound ok = section 46's maxrun <= maxgap(Odd_A) - 1.")
    print("A FLAT maxgap-by-band row would mean Odd_A is syndetic for that candidate.")
    dest = "state/formal_math/erdos257_period_noncollapse/socket_parity_on_candidates_receipt.json"
    with open("public-source-redacted://ai_workflow" + dest, "w") as fh:
        json.dump(out, fh, indent=2, sort_keys=True)
        fh.write("\n")
    print(f"\nreceipt: {dest}")

if __name__ == "__main__":
    main()
