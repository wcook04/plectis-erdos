"""Erdos #1041: the near-field model, reduced to a one-variable identity.

Model: g(zeta) = zeta^n + n zeta.  Hubs zeta_c^{n-1} = -1, |zeta_c| = 1,
critical values g(zeta_c) = (n-1) zeta_c.  A descending branch is
{ g(zeta) - g(zeta_c) = sigma, sigma >= 0 } issuing from zeta_c.

TWO EXACT IDENTITIES (derived, to be checked here).

(I1)  Let G(zeta) := zeta^n + zeta = zeta g'(zeta) / n.  Then the angle theta
      between the branch tangent and the RADIAL direction zeta/|zeta| is
          theta = -arg G(zeta).
      Because d zeta/d sigma = 1/g', so arg(d zeta / zeta) = -arg(zeta g').

(I2)  Along the branch, G = sigma - (n-1)(zeta - zeta_c).
      Because G = g - (n-1) zeta and g = (n-1) zeta_c + sigma.

Consequently, with beta = lim_{Z->oo}(Z - Lambda(Z)) the renormalised excess,
|zeta_c| = 1, and ex := 1 - beta,

      ex  =  int (1 - cos theta) dl  =  Lambda - (radial gain),
      kappa_n = beta_1 + beta_2 = 2 - (ex_1 + ex_2).

So kappa_n > 0 -- the whole near-Fekete half -- is exactly

      ex_1 + ex_2 < 2,

a statement about ONE fixed polynomial with no free parameters.

Writing J_n := (n-1)(ex_1 + ex_2) = (n-1)(2 - kappa_n), the substitution
zeta = zeta_c(1 + tau/n) sends the model to 1 + tau - e^tau as n -> oo, so J_n
should tend to a finite constant; then kappa_n = 2 - J_n/(n-1) > 0 for all
n >= 3 as soon as J_n < 2(n-1), i.e. as soon as J_n < 4.
"""

from mpmath import mp

mp.dps = 40


def branch(n, chi_k=0, nq=24, levels=44, Zmax=None, want_profile=False):
    """The two descending branches at hub zeta_c = exp(i pi (2k+1)/(n-1)).

    Returns (ex_1, ex_2, checks) with ex_i the excess of branch i.
    """
    chi = mp.pi * (2 * chi_k + 1) / (n - 1)
    zc = mp.e ** (1j * chi)
    vc = (n - 1) * zc
    if Zmax is None:
        Zmax = mp.mpf(10) ** 6

    def g(z):
        return z**n + n * z

    def gp(z):
        return n * (z ** (n - 1) + 1)

    def G(z):
        return z**n + z

    a2 = n * (n - 1) * zc ** (n - 2) / 2       # g''(zc)/2

    def newton(sig, z):
        for _ in range(120):
            d = gp(z)
            if d == 0:
                return z
            st = (g(z) - vc - sig) / d
            z -= st
            if abs(st) < mp.mpf(10) ** (-(mp.dps - 8)) * max(1, abs(z)):
                break
        return z

    S = Zmax**n                                 # |zeta| ~ sigma^{1/n}
    K = int(mp.log(S, 2)) + 56
    edges = [mp.mpf(0)] + [S * mp.mpf(2) ** (-k) for k in range(K, 0, -1)] + [S]
    xs, ws = _gl(nq)
    out = []
    checks = {"max_identity_dev": mp.mpf(0)}
    for sgn in (1, -1):
        d0 = sgn * mp.sqrt(1 / a2)
        ex = mp.mpf(0)
        arclen = mp.mpf(0)
        z = None
        sprev = mp.mpf(0)
        for i in range(len(edges) - 1):
            lo, hi = edges[i], edges[i + 1]
            for u, wt in zip(xs, ws):
                sig = lo + (hi - lo) * u
                z = (zc + d0 * mp.sqrt(sig)) if z is None else z + (sig - sprev) / gp(z)
                z = newton(sig, z)
                dz = 1 / gp(z)
                dl = abs(dz) * wt * (hi - lo)
                # theta = angle(dz, z);  identity (I1): theta = -arg G(z)
                th = mp.arg(dz / z)
                th2 = -mp.arg(G(z))
                dev = abs(mp.e ** (1j * th) - mp.e ** (1j * th2))
                if dev > checks["max_identity_dev"]:
                    checks["max_identity_dev"] = dev
                    checks["identity_at"] = z
                # identity (I2): G = sigma - (n-1)(z - zc)
                d2 = abs(G(z) - (sig - (n - 1) * (z - zc)))
                checks["max_I2_dev"] = max(checks.get("max_I2_dev", mp.mpf(0)),
                                           d2 / max(1, abs(G(z))))
                ex += (1 - mp.cos(th)) * dl
                arclen += dl
                sprev = sig
        out.append(ex)
        checks.setdefault("arclen", []).append(arclen)
        checks.setdefault("endz", []).append(z)
    return out[0], out[1], checks


_G = {}


def _gl(nq):
    if nq not in _G:
        import numpy as np
        x, w = np.polynomial.legendre.leggauss(nq)
        _G[nq] = ([mp.mpf(float(t)) / 2 + mp.mpf("0.5") for t in x],
                  [mp.mpf(float(t)) / 2 for t in w])
    return _G[nq]


RECORDED = {3: "0.6080213113", 4: "1.030119661", 5: "1.258578348",
            6: "1.398912406", 8: "1.562228697", 12: "1.714601057",
            20: "1.830805352", 30: "1.887640048"}


def main() -> int:
    import sys
    ok = True
    print("model reduction:  kappa_n = 2 - (ex_1 + ex_2),   J_n = (n-1)(ex_1+ex_2)")
    print(" n    ex_1          ex_2          kappa_n        J_n         "
          "|I1 dev|   |I2 dev|   E")
    for n in sorted(RECORDED):
        e1, e2, ck = branch(n)
        kap = 2 - (e1 + e2)
        J = (n - 1) * (e1 + e2)
        d1 = ck["max_identity_dev"]
        d2 = ck["max_I2_dev"]
        # (E): the near-Fekete half is exactly ex_1 + ex_2 < 2
        E = (e1 + e2) < 2
        good = (d1 < mp.mpf("1e-25") and d2 < mp.mpf("1e-25")
                and abs(kap - mp.mpf(RECORDED[n])) < mp.mpf("1e-8") and E)
        ok = ok and good
        print(f" {n:<4} {mp.nstr(e1,9):13} {mp.nstr(e2,9):13} {mp.nstr(kap,10):14} "
              f"{mp.nstr(J,9):11} {mp.nstr(d1,3):10} {mp.nstr(d2,3):10} "
              f"{'ok' if E else 'VIOLATED'}{'' if good else '   <<< FAIL'}", flush=True)
    print("PASS" if ok else "FAIL")
    return 0 if ok else 1


if __name__ == "__main__":
    import sys
    sys.exit(main())
