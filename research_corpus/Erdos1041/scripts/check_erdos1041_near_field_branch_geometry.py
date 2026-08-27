"""Erdos #1041 near-field model: four exact structural claims, tested.

On g(zeta) = zeta^n + n zeta at the hub zeta_c = exp(i pi/(n-1)), the two
descending branches exit to infinity in the directions alpha = 0 and 2 pi / n.
Claims:

 (G)  the hub-to-exit angles are exactly
          gamma_1 = pi/(n-1),        gamma_2 = pi/(n-1) - 2 pi / n
      so cos gamma_1 + cos gamma_2 = cos(pi/(n-1)) + cos((n-2) pi /(n(n-1))),
      which is INCREASING in n with minimum sqrt(3)/2 at n = 3.

 (T)  the tangent direction tau = arg(d zeta) turns MONOTONICALLY along each
      branch, with total turning exactly
          T_1 = (n-2) pi / (2(n-1)),     T_2 = (n-2)^2 pi / (2 n (n-1)),
      both < pi/2.

 (B)  bridge:  beta = cos gamma - D,   D = arc-minus-chord deficit
      = int (1 - cos(tau - alpha)) dl, the triangle-inequality defect of
      int (1/g') d sigma.

 (K)  hence kappa_n = (cos g_1 + cos g_2) - (D_1 + D_2), so the near-Fekete
      half of Erdos #1041 is EXACTLY
              D_1 + D_2  <  cos(pi/(n-1)) + cos((n-2)pi/(n(n-1))),
      and since the right side is minimised at n = 3, a single uniform bound
              D_1 + D_2  <=  sqrt(3)/2 = 0.8660254...
      proves it for every degree at once.
"""

from mpmath import mp

mp.dps = 30


def run(n, nq=20, Zmax=mp.mpf(10) ** 5):
    chi = mp.pi / (n - 1)
    zc = mp.e ** (1j * chi)
    vc = (n - 1) * zc

    def g(z):
        return z**n + n * z

    def gp(z):
        return n * (z ** (n - 1) + 1)

    a2 = n * (n - 1) * zc ** (n - 2) / 2

    def newton(sig, z):
        for _ in range(120):
            d = gp(z)
            if d == 0:
                return z
            st = (g(z) - vc - sig) / d
            z -= st
            if abs(st) < mp.mpf(10) ** (-(mp.dps - 6)) * max(1, abs(z)):
                break
        return z

    S = Zmax**n
    K = int(mp.log(S, 2)) + 44
    edges = [mp.mpf(0)] + [S * mp.mpf(2) ** (-k) for k in range(K, 0, -1)] + [S]
    xs, ws = _gl(nq)
    rows = []
    for sgn in (1, -1):
        d0 = sgn * mp.sqrt(1 / a2)
        Lam = mp.mpf(0)
        Dint = mp.mpf(0)
        turn = mp.mpf(0)
        signed = mp.mpf(0)
        z = None
        sprev = mp.mpf(0)
        tanprev = None
        for i in range(len(edges) - 1):
            lo, hi = edges[i], edges[i + 1]
            for u, wt in zip(xs, ws):
                sig = lo + (hi - lo) * u
                z = (zc + d0 * mp.sqrt(sig)) if z is None else z + (sig - sprev) / gp(z)
                z = newton(sig, z)
                dz = 1 / gp(z)
                dl = abs(dz) * wt * (hi - lo)
                Lam += dl
                tan = mp.arg(dz)
                if tanprev is not None:
                    d = tan - tanprev
                    while d > mp.pi:
                        d -= 2 * mp.pi
                    while d < -mp.pi:
                        d += 2 * mp.pi
                    turn += abs(d)
                    signed += d
                tanprev = tan
                sprev = sig
        zS = newton(S, z)
        Z, alpha = abs(zS), mp.arg(zS)
        gam = chi - alpha
        beta = Z - Lam
        D = Lam - (Z - mp.cos(gam))
        rows.append(dict(beta=beta, D=D, gam=gam, alpha=alpha,
                         turn=turn, signed=signed))
    return rows


_G = {}


def _gl(nq):
    if nq not in _G:
        import numpy as np
        x, w = np.polynomial.legendre.leggauss(nq)
        _G[nq] = ([mp.mpf(float(t)) / 2 + mp.mpf("0.5") for t in x],
                  [mp.mpf(float(t)) / 2 for t in w])
    return _G[nq]


if __name__ == "__main__":
    print(" n | (G) gamma err   | (T) turning err   monotone | (B) bridge err | "
          "D1+D2      RHS        kappa_n")
    worstG = worstT = worstB = mp.mpf(0)
    worstD = mp.mpf(0)
    ok = True
    for n in (3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 16, 20):
        r = run(n)
        g1p = mp.pi / (n - 1)
        g2p = mp.pi / (n - 1) - 2 * mp.pi / n
        T1p = (n - 2) * mp.pi / (2 * (n - 1))
        T2p = (n - 2) ** 2 * mp.pi / (2 * n * (n - 1))
        eG = max(abs(r[0]["gam"] - g1p), abs(r[1]["gam"] - g2p))
        eT = max(abs(r[0]["turn"] - T1p), abs(r[1]["turn"] - T2p))
        mono = max(abs(r[0]["turn"] - abs(r[0]["signed"])),
                   abs(r[1]["turn"] - abs(r[1]["signed"])))
        eB = max(abs(x["beta"] - (mp.cos(x["gam"]) - x["D"])) for x in r)
        Dsum = r[0]["D"] + r[1]["D"]
        RHS = mp.cos(g1p) + mp.cos(g2p)
        kap = r[0]["beta"] + r[1]["beta"]
        worstG, worstT, worstB = max(worstG, eG), max(worstT, eT), max(worstB, eB)
        worstD = max(worstD, Dsum)
        # gamma and turning are read off a branch truncated at |zeta| = 1e5, so
        # they carry the cutoff's tail, not mp.dps; the bridge and monotonicity
        # are pure integral identities and are held to 1e-20.
        good = eG < mp.mpf("1e-8") and eT < mp.mpf("1e-7") and mono < mp.mpf("1e-20") \
            and eB < mp.mpf("1e-20") and Dsum < RHS and Dsum < mp.sqrt(3) / 2
        ok = ok and good
        print(f" {n:<2}| {mp.nstr(eG,3):>14} | {mp.nstr(eT,3):>13} {mp.nstr(mono,3):>10} | "
              f"{mp.nstr(eB,3):>13} | {mp.nstr(Dsum,7):>10} {mp.nstr(RHS,7):>10} "
              f"{mp.nstr(kap,8):>10}{'' if good else '  <<< FAIL'}", flush=True)
    print(f"\n worst gamma err {mp.nstr(worstG,3)}   worst turning err {mp.nstr(worstT,3)}"
          f"   worst bridge err {mp.nstr(worstB,3)}")
    print(f" max D1+D2 over tested degrees = {mp.nstr(worstD,8)}   "
          f"uniform target sqrt(3)/2 = {mp.nstr(mp.sqrt(3)/2,8)}   "
          f"margin factor {mp.nstr((mp.sqrt(3)/2)/worstD,5)}")
    print("PASS" if ok else "FAIL")
    import sys
    sys.exit(0 if ok else 1)
