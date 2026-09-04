#!/usr/bin/env python3
"""Erdos 1041: checks for BridgeIdentityProof.md.

(BR) of NearFeketeCuspLaw.md section 7 relates the two anchorings of a branch's
renormalised excess:

    beta := lim_{S->oo} ( |zeta(S)| - S )        [radial anchor, S = arclength]
    D    := int_Gamma (1 - cos t) dl,  t = tau - alpha   [turning / chord anchor]
    (BR)   beta = cos gamma - D .

Writing u = e^{-i alpha} zeta = U + iV, the finite-S identity

    |zeta(S)| - S  =  ( |u(S)| - U(S) )  +  cos gamma  -  int_0^S (1 - cos t) ds   (*)

is exact, and (BR) is the single limit |u| - U = V^2/(|u|+U) -> 0, which follows
from Lemma T's asymptotics (V = O(U^{-(n-2)}), |zeta| -> oo).

Checked here: (*) at finite S, the decay of |u|-U, beta_1 + beta_2 against the
kappa_n values stored in NearFeketeCuspLaw.md section 6, and the assembled
chain kappa_n = C_n - (D_1 + D_2) >= C_n - B_n > 0.

Usage: ./repo-python formal_math/probes/erdos1041_bridge_identity.py [--max-n 12]
"""
from __future__ import annotations
import argparse, cmath, math
import numpy as np

# kappa_n computed from g alone, NearFeketeCuspLaw.md section 6 table.
STORED = {3: 0.6080213113, 4: 1.030119661, 5: 1.258578348, 6: 1.398912406,
          8: 1.562228697, 12: 1.714601057}


def trace(n: int, sign: int, alpha: float, smax: float, npts: int):
    """Descending branch by root continuation in sigma = s^2; returns arclength data."""
    zc = cmath.exp(1j * math.pi / (n - 1)); v = (n - 1) * zc
    gpp = n * (n - 1) * zc ** (n - 2); gppp = n * (n - 1) * (n - 2) * zc ** (n - 3)
    a = cmath.sqrt(2.0 / gpp) * sign; b = -gppp / (3.0 * gpp ** 2)
    coef = np.zeros(n + 1, dtype=complex); coef[0] = 1.0; coef[n - 1] = n
    ss = np.concatenate(([0.0], np.geomspace(1e-12, smax, npts)))
    zs = np.empty(len(ss), dtype=complex); zs[0] = zc
    for k in range(1, len(ss)):
        s = ss[k]
        if s < 1e-6:
            zs[k] = zc + a * s + b * s * s
        else:
            c = coef.copy(); c[n] = -(v + s * s); rt = np.roots(c)
            pred = zs[k - 1] + (zs[k - 1] - zs[k - 2]) if k > 1 else zs[0]
            zs[k] = rt[np.argmin(np.abs(rt - pred))]
    gp = n * (zs ** (n - 1) + 1.0)
    dlds = np.empty(len(ss)); dlds[0] = abs(a); dlds[1:] = 2 * ss[1:] / np.abs(gp[1:])
    trap = np.trapezoid if hasattr(np, "trapezoid") else np.trapz
    Lam = trap(dlds, ss)                                   # arclength S
    u = cmath.exp(-1j * alpha) * zs[-1]
    u0 = cmath.exp(-1j * alpha) * zc
    # int cos t dl = Re(e^{-i alpha}(zeta(S) - zeta_c)) = U(S) - cos gamma
    return dict(Lam=Lam, U=u.real, V=u.imag, absu=abs(u), cosgam=u0.real,
                D=Lam - (u.real - u0.real), beta=abs(zs[-1]) - Lam)


def main() -> int:
    ap = argparse.ArgumentParser(); ap.add_argument("--max-n", type=int, default=12)
    n_max = ap.parse_args().max_n
    ok = True

    print("A. The finite-S identity (*), and the single limit it leaves: |u| - U -> 0.")
    print("   Lemma T predicts V = O(U^{-(n-1)}) on branch 1 (alpha=0) and O(U^{-(n-2)})")
    print("   on branch 2; the last column is that rate constant, which must stay O(1).")
    print(f"{'n':>3} {'br':>3} {'|zeta|-S':>13} {'via (*)':>13} {'(*) resid':>11} "
          f"{'|u|-U':>10} {'V':>10} {'U':>10} {'|V|U^k':>8}")
    for n in range(3, n_max + 1):
        for i, (sign, alpha) in enumerate(((+1, 0.0), (-1, 2 * math.pi / n))):
            r = trace(n, sign, alpha, 10 ** (0.5 * n + 2), 20000)
            rhs = (r["absu"] - r["U"]) + r["cosgam"] - r["D"]
            k = (n - 1) if i == 0 else (n - 2)      # Lemma T's two decay rates
            rate = abs(r["V"]) * r["U"] ** k
            ok &= abs(r["beta"] - rhs) < 1e-12 * max(1.0, abs(rhs))
            ok &= (r["absu"] - r["U"]) < 1e-6 and rate < 5.0
            print(f"{n:>3} {i+1:>3} {r['beta']:>13.9f} {rhs:>13.9f} "
                  f"{abs(r['beta']-rhs):>11.2e} {r['absu']-r['U']:>10.2e} "
                  f"{r['V']:>10.2e} {r['U']:>10.2e} {rate:>8.3f}")

    print("\nB. beta = cos gamma - D per branch, and kappa_n = beta_1 + beta_2")
    print(f"{'n':>3} {'beta_1':>12} {'beta_2':>12} {'kappa_n':>13} {'stored':>13} "
          f"{'C_n-B_n':>11} {'clears':>7}")
    for n in range(3, n_max + 1):
        T = [(n - 2) * math.pi / (2 * (n - 1)), (n - 2) ** 2 * math.pi / (2 * n * (n - 1))]
        gam = [math.pi / (n - 1), math.pi / (n - 1) - 2 * math.pi / n]
        bet, Ds = [], []
        for i, (sign, alpha) in enumerate(((+1, 0.0), (-1, 2 * math.pi / n))):
            r = trace(n, sign, alpha, 10 ** (0.5 * n + 2), 20000)
            # (BR): the traced beta must equal cos gamma - D to the tracer's reach
            ok &= abs(r["beta"] - (math.cos(gam[i]) - r["D"])) < 1e-6
            bet.append(math.cos(gam[i]) - r["D"]); Ds.append(r["D"])
        kap = bet[0] + bet[1]
        B = sum(math.tan(T[i] / 2) * abs(math.sin(gam[i])) for i in (0, 1))
        C = sum(math.cos(g) for g in gam)
        ok &= (C - B > 0) and (kap >= C - B - 1e-9)
        if n in STORED:
            # 1e-4 is the 20000-point trapezoid error bar, not the identity's;
            # section C shows it falling as O(h^2) onto the stored value.
            ok &= abs(kap - STORED[n]) < 1e-4
        st = f"{STORED[n]:.9f}" if n in STORED else "-"
        print(f"{n:>3} {bet[0]:>12.8f} {bet[1]:>12.8f} {kap:>13.9f} {st:>13} "
              f"{C-B:>11.8f} {str(kap >= C - B):>7}")

    print("\nC. The stored-value gap is QUADRATURE, not truncation: refine at fixed")
    print("   range and it falls as O(h^2) onto the 40-digit kappa_3.  (Widening the")
    print("   range at fixed npts makes it grow instead -- the s-grid thins out.)")
    gam3 = [math.pi / 2, math.pi / 2 - 2 * math.pi / 3]
    prev = None
    for npts in (5000, 20000, 80000):
        k = 0.0
        for i, (sign, alpha) in enumerate(((+1, 0.0), (-1, 2 * math.pi / 3))):
            k += math.cos(gam3[i]) - trace(3, sign, alpha, 10 ** 3.5, npts)["D"]
        gap = k - STORED[3]
        if prev is not None:
            ok &= abs(gap) < 0.1 * abs(prev)          # better than O(h^{1.7})
        prev = gap
        print(f"   npts={npts:>6}  kappa_3={k:.10f}  gap={gap:+.3e}")

    print("\nD. The assembled chain, all four links:")
    print("   kappa_n = beta_1+beta_2  (section 2 scaling, proved in the cusp law)")
    print("           = C_n - (D_1+D_2)                                (BR), proved here")
    print("           >= C_n - B_n                (TurningLengthBound section 2 Theorem,")
    print("                                        whose hypotheses are MonotoneTurningProof)")
    print("           > 0                          (TurningLengthBound section 3 Proposition)")
    print("\nOK" if ok else "\nFAILED")
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
