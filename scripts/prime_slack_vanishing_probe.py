#!/usr/bin/env python3
"""Erdos 257 -- the prime slack is TWO-VALUED, and this checks the derivation.

THE DERIVATION (algebra first; this script is the check, not the discovery).
--------------------------------------------------------------------------
The forward carry satisfies  tau_A(m) = eps_m + 2 C_{m-1} - C_m.  At a prime p
the only divisor of p that can lie in A is p itself (1 is never in A, since
w_1 = 1 exceeds every target below 1), so tau_A(p) = 1_A(p) in {0,1}.  Hence

    2 C_{p-1} = tau_A(p) - eps_p + C_p                                  (*)

and, since C_{p-1} is an integer, 2 C_{p-1} <= C_p + 1: the prime halving
theorem.  Define the slack

    s(p) = (C_p + 1) // 2  -  C_{p-1}   >= 0.

Read (*) mod 2: the left side is even, so tau_A(p) - eps_p = C_p (mod 2).

  * C_p EVEN  ==> tau_A(p) = eps_p, and s(p) = (eps_p - tau_A(p))/2 = 0.
  * C_p ODD   ==> tau_A(p) != eps_p, and s(p) = (1 + eps_p - tau_A(p))/2,
                  which is 0 when tau_A(p) = 1 and 1 when tau_A(p) = 0.

    THEOREM.  s(p) is in {0,1} for every prime p, and
              s(p) = 1  <==>  C_p is ODD and p is NOT in A.
    Equivalently the vanishing set is  {p : C_p even}  union  {p in A}.

So the "distribution of the slack and where it vanishes" is a two-valued
statistic with a closed characterisation.  That is why no amount of exact
Fraction arithmetic was going to reveal structure in it.

PREDICTIONS, written before running
-----------------------------------
P1.  max s(p) = 1 and min s(p) = 0 on every target: NO value outside {0,1}.
P2.  s(p) = 1 exactly on the primes with C_p odd and p not in A -- zero
     mismatches against the characterisation.
P3.  If C_p parity and membership were independent and unbiased, density of
     {s = 1} would be ~0.25.  Measured departures from 0.25 are reported but
     NOT claimed as signal.

FALSIFIER, stated in advance: a single prime with s(p) outside {0,1}, or a
single mismatch against the characterisation, refutes the derivation outright.

CAVEAT (T59): the corpus measures NO signal separating safe from fatal orbits
(skip position equidistributed to 2^-12).  A clean two-valued law here is a
structural identity, not a discriminator, and must not be read as one.

Bound directions:
  analysis -> here : RunLengthMarginLawAndDivisorMultiplicity.md s10/s11;
                     scripts/carry_peaks_at_primes.py (the halving theorem)
  here -> analysis : CertificateSocketCollapse.md s84, receipt under state/
"""
from __future__ import annotations
import sys, json, hashlib
from pathlib import Path

sys.path.insert(0, "public-source-redacted://scripts")
from cantor_staircase_run_length_lab import Engine

REPO = Path("public-source-redacted://ai_workflow")
D = int(sys.argv[1]) if len(sys.argv) > 1 else 20000

TARGETS = [("1/2", 1, 2), ("1/21", 1, 21), ("4/9", 4, 9), ("1/465", 1, 465),
           ("1/5", 1, 5), ("5/12", 5, 12), ("3/7", 3, 7), ("2/21", 2, 21),
           ("1013/2048", 1013, 2048)]

def primes_upto(N):
    s = bytearray([1]) * (N + 1); s[0] = s[1] = 0
    for i in range(2, int(N ** .5) + 1):
        if s[i]: s[i*i::i] = bytearray(len(s[i*i::i]))
    return [i for i in range(N + 1) if s[i]]

eng = Engine(D)
rows = []

for name, p_num, q in TARGETS:
    r = eng.run(p_num, q)
    if r["status"] != "alive":
        rows.append({"target": name, "status": r["status"]}); continue
    w = r["word"]; M = len(w)
    inA = [False] * (M + 2)
    A = [i + 1 for i, b in enumerate(w) if b]
    for d in A: inA[d] = True
    tauA = [0] * (M + 2)
    for d in A:
        for m in range(d, M + 1, d): tauA[m] += 1
    N = 0; C = [0] * (M + 2); pw = 1
    for m in range(1, M + 1):
        N = 2 * N + tauA[m]; pw <<= 1
        C[m] = (pw * p_num) // q - N
    PR = [x for x in primes_upto(M) if 2 <= x <= M]
    vals, mismatch, outside, vanish = {}, 0, 0, []
    for pp in PR:
        s = (C[pp] + 1) // 2 - C[pp - 1]
        vals[s] = vals.get(s, 0) + 1
        if s not in (0, 1): outside += 1
        pred = 1 if (C[pp] % 2 == 1 and not inA[pp]) else 0
        if s != pred: mismatch += 1
        if s == 0: vanish.append(pp)
        # tau_A(p) must equal 1_A(p): independent check of the premise
        if tauA[pp] != (1 if inA[pp] else 0): mismatch += 1000000
    rows.append({
        "target": name, "status": "alive", "depth": M, "n_primes": len(PR),
        "slack_values": {str(k): v for k, v in sorted(vals.items())},
        "outside_01": outside, "mismatch_vs_characterisation": mismatch,
        "n_vanish": len(vanish), "density_vanish": len(vanish) / len(PR),
        "density_s1": vals.get(1, 0) / len(PR),
        "first_vanish": vanish[:8],
    })
    print(f"{name:>10} primes={len(PR):<5} s-values={rows[-1]['slack_values']}  "
          f"outside{{0,1}}={outside}  mismatch={mismatch}  "
          f"density(s=1)={rows[-1]['density_s1']:.4f}  "
          f"density(vanish)={rows[-1]['density_vanish']:.4f}")

out = REPO / "state/formal_math/erdos257_period_noncollapse/prime_slack_vanishing_receipt.json"
blob = json.dumps({"depth": D, "rows": rows}, indent=2, sort_keys=True)
out.parent.mkdir(parents=True, exist_ok=True)
out.write_text(blob)
tot_out = sum(r.get("outside_01", 0) for r in rows)
tot_mis = sum(r.get("mismatch_vs_characterisation", 0) for r in rows)
print(f"\nTOTAL outside {{0,1}} = {tot_out}   TOTAL mismatch = {tot_mis}")
print("(both zero => the derivation is confirmed on every target and every prime)")
print("wrote", out, "sha256=" + hashlib.sha256(blob.encode()).hexdigest()[:16])
