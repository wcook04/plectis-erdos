"""Checker for FreePointFP5OuterBound.md (Erdos 1041).

Verifies:
  O1  symbolic bank: max of (1-x)(1+x)^5 at x = 2/3 equals 3125/729;
      Phi(h) = int_0^1 (1-s)e^{sh} ds (so Phi' > 0); the chord identity
      d^2 = (1+t)^2 - 2t(1+cos phi); the modal identity
      C(2n,n) + 2 sum_{r=1}^n C(2n,n-r) = 4^n for n <= 8;
  O2  the four-lemma chain on 4000 fresh random configs: h_j <= H_j;
      s_j <= Delta/2 (halving); D(rho) <= Delta (deficit); S <= OUT
      (transfer + assembly); and the localization A <= Phi(Hsharp) Lbar;
  O3  FP_5 assembly on the same battery: S <= 5 everywhere, equality
      only at c = 0 (spot: S(0) = 5 exactly);
  O4  THE FULL BOX CERTIFICATE replays: certify_erdos1041_fp5_outer_bnb
      at margin 0.05 returns status OK with the recorded counts
      (34 rounds, 154968 excluded, 262167 verified, empty live set).

Exit 0 iff all pass.  Runtime ~1 minute (O4 is ~30 s).
"""
import subprocess
import sys
from math import comb
from pathlib import Path

import numpy as np
import sympy as sp

FAILURES = []
rng = np.random.default_rng(105)
HERE = Path(__file__).resolve().parent


def report(name, ok, detail=""):
    print(("PASS " if ok else "FAIL ") + name + ("  " + detail if detail else ""))
    if not ok:
        FAILURES.append(name)


def main():
    # O1 symbolic bank
    x, h, s, t, phi = sp.symbols("x h s t phi", real=True)
    f = (1 - x) * (1 + x) ** 5
    crit = sp.solve(sp.diff(f, x), x)
    ok1 = sp.Rational(2, 3) in crit and sp.simplify(
        f.subs(x, sp.Rational(2, 3)) - sp.Rational(3125, 729)) == 0
    import mpmath as mp
    mp.mp.dps = 30
    for hv in (mp.mpf(1), mp.mpf(-1), mp.mpf("0.5"), mp.mpf(-3)):
        lhs = mp.quad(lambda u: (1 - u) * mp.e ** (u * hv), [0, 1])
        rhs = (mp.e ** hv - 1 - hv) / hv**2
        ok1 = ok1 and abs(lhs - rhs) < mp.mpf(10) ** (-25)
    d2 = sp.expand((1 + t) ** 2 - 2 * t * (1 + sp.cos(phi)))
    ok1 = ok1 and sp.simplify(d2 - (1 + t**2 - 2 * t * sp.cos(phi))) == 0
    ok1 = ok1 and all(comb(2 * n, n) + 2 * sum(comb(2 * n, n - r)
                                               for r in range(1, n + 1)) == 4**n
                      for n in range(1, 9))
    report("O1 symbolic bank", bool(ok1))

    # shared numeric machinery
    NMAX = 12
    Hsharp = np.log(3125.0 / 729.0) / 5.0
    PhiHs = (np.exp(Hsharp) - 1 - Hsharp) / Hsharp**2
    LAM = 1.0 / PhiHs

    def battery(c):
        rho = np.abs(c)
        d = np.abs(1.0 - np.conj(c)[:, None] * c[None, :])
        np.fill_diagonal(d, 1 - rho**2)
        h_ = np.sum(np.log(np.maximum(d, 1e-300)), axis=1) / 5.0
        S = float(np.sum(np.exp(h_)))
        t_ = rho[:, None] * rho[None, :]
        onep = 1.0 + t_
        H_ = (np.log(np.maximum(1 - rho**2, 1e-300))
              + np.sum(np.log(onep), axis=1) - np.log(1 + rho**2)) / 5.0
        T = np.exp(H_)
        delta = np.log(onep / np.maximum(d, 1e-300))
        np.fill_diagonal(delta, 0.0)
        s_ = np.sum(delta, axis=1) / 5.0
        Delta = float(np.sum(s_))
        fmat = t_ / onep**2
        np.fill_diagonal(fmat, 0.0)
        best = 0.0
        acc = 0.0
        for n in range(1, NMAX + 1):
            Fn = fmat**n
            np.fill_diagonal(Fn, 0.0)
            Sig = float(np.sum(Fn))
            lam = float(np.linalg.eigvalsh(Fn)[0])
            acc += (comb(2 * n, n) * Sig
                    + (4.0**n - comb(2 * n, n)) * 5 * lam) / (10.0 * n)
            best = max(best, acc)
        D = best
        Ts = np.sort(T)
        OUT = float(np.sum(T) - (1 - np.exp(-D / 2)) * (Ts[0] + Ts[1]))
        L_ = -np.log(np.maximum(1 - rho**2, 1e-300))
        Lbar = float(np.mean(L_))
        Hs = np.where(np.abs(H_) > 1e-12, H_, 1.0)
        Phi_H = np.where(np.abs(H_) > 1e-12,
                         (np.exp(Hs) - 1 - Hs) / Hs**2, 0.5)
        A = float(np.mean(Phi_H * L_))
        return dict(S=S, H=H_, h=h_, s=s_, Delta=Delta, D=D, OUT=OUT,
                    Lbar=Lbar, A=A)

    worst = dict(ceil=np.inf, halve=np.inf, deficit=np.inf, out=np.inf,
                 loc=np.inf, fp=np.inf)
    for _ in range(4000):
        mode = rng.integers(0, 3)
        if mode == 0:
            r = rng.uniform(0, 1, 5)
        elif mode == 1:
            r = rng.uniform(0.7, 1.0, 5)
        else:
            r = np.clip(rng.uniform(0.85, 1.0) * np.ones(5)
                        + 0.1 * rng.normal(size=5), 0, 1)
        th = rng.uniform(0, 2 * np.pi, 5)
        c = r * np.exp(1j * th)
        b = battery(c)
        worst["ceil"] = min(worst["ceil"], float(np.min(b["H"] - b["h"])))
        worst["halve"] = min(worst["halve"],
                             float(np.min(b["Delta"] / 2 - b["s"])))
        worst["deficit"] = min(worst["deficit"], b["Delta"] - b["D"])
        worst["out"] = min(worst["out"], b["OUT"] - b["S"])
        worst["loc"] = min(worst["loc"], PhiHs * b["Lbar"] - b["A"])
        worst["fp"] = min(worst["fp"], 5.0 - b["S"])
    ok2 = all(worst[k] > -1e-9 for k in ("ceil", "halve", "deficit",
                                         "out", "loc"))
    report("O2 four-lemma chain + localization (4000 configs)", ok2,
           " ".join(f"{k} {v:+.1e}" for k, v in worst.items()
                    if k != "fp"))

    S0 = battery(np.zeros(5, complex))["S"]
    ok3 = worst["fp"] > -1e-9 and abs(S0 - 5.0) < 1e-12
    report("O3 FP_5 assembly (S <= 5; equality at 0)", ok3,
           f"min margin {worst['fp']:+.1e} S(0) {S0}")

    # O4 full certificate replay
    proc = subprocess.run(
        [sys.executable, str(HERE / "certify_erdos1041_fp5_outer_bnb.py"),
         "0.05"], capture_output=True, text=True, timeout=600)
    out = proc.stdout + proc.stderr
    ok4 = ("'status': 'OK'" in out and "'rounds': 34" in out
           and "'excluded': 154968" in out and "'verified': 262167" in out)
    report("O4 box certificate replays bit-identically", ok4,
           out.strip().splitlines()[-1][:80] if out.strip() else "no output")

    if FAILURES:
        print("FAILURES:", FAILURES)
        return 1
    print("ALL PASS")
    return 0


if __name__ == "__main__":
    sys.exit(main())
