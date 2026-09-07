#!/usr/bin/env python3
"""
Erdos 257 -- complexity of the CARRY sequence.

From RunLengthMarginLawAndDivisorMultiplicity.md:
  * sum_{k in A} 1/(2^k-1) = sum_m tau_A(m) 2^-m       (exact)
  * tau_A(m) = eps_m + 2 C_{m-1} - C_m                 (exact, 0 violations)
  * periodic tau_A  =>  A finite                       (exhaustive, r <= 24)

COROLLARY (free).  eps is eventually periodic for rational y.  If C were also
eventually periodic, tau_A = eps + 2*shift(C) - C would be eventually periodic,
hence A finite.  So a counterexample needs an APERIODIC carry sequence.

But the carries are measured to be tiny (max 7..10, settling to 1).  A bounded
APERIODIC low-complexity sequence is exactly the automatic / Sturmian regime
where transcendence theorems for Mahler and Lambert series apply.  So the
sharp question is:  HOW COMPLEX is C?

Integer-exact recurrence (no Fractions):
    N_m = 2 N_{m-1} + tau_A(m),      C_m = floor(2^m p / q) - N_m.
"""
from __future__ import annotations
import sys, json, math

problem_id = "erdos_257"

sys.path.insert(0, "public-source-redacted://scripts")
from cantor_staircase_run_length_lab import Engine

DEPTH = int(sys.argv[1]) if len(sys.argv) > 1 else 12000
TARGETS = [("1/2", 1, 2), ("1/21", 1, 21), ("4/9", 4, 9), ("1/465", 1, 465), ("1/5", 1, 5)]

def complexity(seq, kmax):
    out = {}
    n = len(seq)
    for k in range(1, kmax + 1):
        seen = set()
        for i in range(n - k + 1):
            seen.add(tuple(seq[i:i + k]))
        out[k] = len(seen)
    return out

def eventual_period(seq, pmax, tail_frac=0.5):
    """smallest p <= pmax with seq[i]==seq[i+p] on the last tail_frac of seq."""
    n = len(seq); s = int(n * (1 - tail_frac))
    for p in range(1, pmax + 1):
        if all(seq[i] == seq[i + p] for i in range(s, n - p)):
            return p
    return None

print(f"depth={DEPTH}")
eng = Engine(DEPTH)
out = {}
for name, p, q in TARGETS:
    r = eng.run(p, q)
    if r["status"] != "alive":
        print(f"{name}: {r['status']} @ {r['death']}"); continue
    w = r["word"]; M = len(w)
    A = [i + 1 for i, b in enumerate(w) if b]
    tauA = [0] * (M + 1)
    for d in A:
        for m in range(d, M + 1, d):
            tauA[m] += 1
    N = 0; C = [0] * (M + 1); pw = 1
    for m in range(1, M + 1):
        N = 2 * N + tauA[m]; pw <<= 1
        C[m] = (pw * p) // q - N
    Cs = C[1:]
    hist = {}
    for c in Cs: hist[c] = hist.get(c, 0) + 1
    per = eventual_period(Cs, 3000, 0.4)
    kmax = 12
    comp = complexity(Cs[M // 2:], kmax)          # complexity of the deep tail
    # entropy of the carry alphabet
    tot = len(Cs)
    H = -sum((v / tot) * math.log2(v / tot) for v in hist.values())
    print(f"\n=== {name} (depth {M}) ===")
    print(f"  carry alphabet {sorted(hist)}  max C = {max(Cs)}  mean {sum(Cs)/tot:.4f}  entropy {H:.4f} bits")
    print(f"  P(C=1) = {hist.get(1,0)/tot:.4f}   P(C=0) = {hist.get(0,0)/tot:.4f}   P(C>=3) = {sum(v for k,v in hist.items() if k>=3)/tot:.5f}")
    print(f"  eventual period of C within last 40% (p <= 3000): {per}")
    print(f"  subword complexity of C-tail:  " +
          " ".join(f"p({k})={comp[k]}" for k in range(1, 9)))
    print(f"  ...vs |alphabet|^k:            " +
          " ".join(f"{len(hist)**k}" for k in range(1, 9)))
    out[name] = {"maxC": max(Cs), "entropy": H, "period": per,
                 "alphabet": sorted(hist), "complexity": comp,
                 "P1": hist.get(1, 0) / tot}
json.dump(out, open("/tmp/e257_carry.json", "w"), indent=1)
print("\nwrote /tmp/e257_carry.json")
