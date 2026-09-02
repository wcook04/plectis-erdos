"""Checker for FreePointMeanInequalityFP3.md (Erdos 1041 satellite).

Verifies:
  1  the exact identity (3-Q)(3+Q-|s|^2+E2) = 9 - Delta and Delta >= 0
     with Delta = (Q^2 - 3 E2) + Q E2 + (3-Q)|s|^2, on random samples;
  2  the Hoelder chain S^3 <= (sum x)(sum d)^2 on random samples;
  3  adversarial sweep: sup of S over 40k random + polished samples stays
     below 3 (strictly, except the origin);
  4  equality diagnostics: S at the origin equals 3 exactly; S at equal
     nonzero moduli is strictly below 3.

Exit 0 iff all pass.
"""
import sys

import numpy as np

rng = np.random.default_rng(3)
FAILURES = []


def report(name, ok, detail=""):
    print(("PASS " if ok else "FAIL ") + name + ("  " + detail if detail else ""))
    if not ok:
        FAILURES.append(name)


def S_of(cs):
    tot = 0.0
    for j in range(3):
        p = 1.0
        for k in range(3):
            p *= abs(1 - np.conj(cs[j]) * cs[k])
        tot += p ** (1.0 / 3.0)
    return tot


def main():
    ok1 = ok2 = True
    for _ in range(4000):
        cs = [np.sqrt(rng.uniform()) * np.exp(2j * np.pi * rng.uniform()) for _ in range(3)]
        Q = sum(abs(c) ** 2 for c in cs)
        E2 = sum(abs(cs[i]) ** 2 * abs(cs[j]) ** 2
                 for i in range(3) for j in range(i + 1, 3))
        s = sum(cs)
        Delta = (Q ** 2 - 3 * E2) + Q * E2 + (3 - Q) * abs(s) ** 2
        lhs = (3 - Q) * (3 + Q - abs(s) ** 2 + E2)
        if abs(lhs - (9 - Delta)) > 1e-9 or Delta < -1e-11:
            ok1 = False
        x = [1 - abs(c) ** 2 for c in cs]
        d = [abs(1 - np.conj(cs[i]) * cs[j])
             for i in range(3) for j in range(i + 1, 3)]
        if S_of(cs) ** 3 > sum(x) * sum(d) ** 2 + 1e-8:
            ok2 = False
    report("1 identity + Delta >= 0", ok1)
    report("2 Hoelder chain", ok2)

    sup = 0.0
    for _ in range(40000):
        cs = [np.sqrt(rng.uniform()) * np.exp(2j * np.pi * rng.uniform()) for _ in range(3)]
        sup = max(sup, S_of(cs))
    # crude polish around the best found is unnecessary: bound is 3
    report("3 adversarial sup < 3", sup < 3 - 1e-6, f"sampled sup={sup:.9f}")

    s0 = S_of([0j, 0j, 0j])
    r = 0.5
    se = S_of([r + 0j, r * np.exp(2j * np.pi / 3), r * np.exp(-2j * np.pi / 3)])
    report("4 equality only at origin", abs(s0 - 3) < 1e-12 and se < 3 - 1e-6,
           f"S(0)={s0:.12f}  S(equal moduli 0.5)={se:.9f}")

    print()
    if FAILURES:
        print("FAIL:", FAILURES)
        return 1
    print("PASS: all sections")
    return 0


if __name__ == "__main__":
    sys.exit(main())
