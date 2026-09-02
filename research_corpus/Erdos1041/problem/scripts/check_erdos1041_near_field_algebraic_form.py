"""Erdos #1041: the near-field branch in closed algebraic form.

Work in P = zeta / zeta_c, so the hub sits at P = 1 (|zeta_c| = 1, so radii and
arclengths are unchanged and beta, D, kappa_n are all intrinsic to the P-plane).

Using zeta_c^{n-1} = -1:

  (A1)  g(zeta) - g(zeta_c) = -e^{i chi} F(P),   F(P) := P^n - n P + (n-1),
        and F has a DOUBLE root at P = 1:
              F(P) = (P-1)^2 Q(P),   Q(P) = sum_{i=0}^{n-2} (n-1-i) P^i,
        since P^n - nP + (n-1) = (P-1) sum_{j=0}^{n-1}(P^j - 1).
        So the branch is  { P : e^{i chi} F(P) <= 0 },  i.e. a level set of
        arg F -- the preimage of a ray under ONE fixed polynomial with a double
        root at the hub.

  (A2)  g'(zeta) = n(1 - P^{n-1}).

At the BINDING degree n = 3: chi = pi/2, F(P) = (P-1)^2 (P+2), and the branch
condition e^{i pi/2} F <= 0 says Re F = 0, i.e. with P = x + iy

  (A3)        x^3 - 3 x y^2 - 3x + 2 = 0,   equivalently
              y^2 = (x-1)^2 (x+2) / (3x).

So the two descending branches at n = 3 are the two arcs through (1,0) of one
explicit real cubic.  Its x > 0 component has asymptote y = x/sqrt(3) (direction
pi/6) and a vertical end at x -> 0+ (direction -pi/2) -- which are exactly the
measured exit directions, since gamma = chi - alpha gives gamma_2 = -pi/6 and
gamma_1 = pi/2.

Finally, arclength on (A3): y y' = (x^3-1)/(3x^2), so

  (A4)        1 + y'^2 = (4x^6 - 9x^4 + 4x^3 + 1) / (3 x^3 (x^3 - 3x + 2)).

The numerator is NOT a perfect square, so the arclength -- hence beta and
kappa_3 -- is not elementary.  Recorded so nobody hunts for a closed form.
"""

from mpmath import mp

mp.dps = 40


def check_A1_A2(n):
    """(A1) and (A2) as polynomial identities, checked at random points."""
    chi = mp.pi / (n - 1)
    zc = mp.e ** (1j * chi)
    Q = [mp.mpf(n - 1 - i) for i in range(n - 1)]      # ascending

    def Qv(P):
        a = mp.mpc(0)
        for c in reversed(Q):
            a = a * P + c
        return a

    worst1 = worst2 = worstF = mp.mpf(0)
    for k in range(1, 25):
        P = mp.mpc(mp.cos(mp.mpf(k)) * 2, mp.sin(mp.mpf(3) * k) * 2)
        zeta = zc * P
        lhs = (zeta**n + n * zeta) - ((n - 1) * zc)
        F = P**n - n * P + (n - 1)
        worst1 = max(worst1, abs(lhs + zc * F) / max(1, abs(lhs)))
        worstF = max(worstF, abs(F - (P - 1) ** 2 * Qv(P)) / max(1, abs(F)))
        gp = n * (zeta ** (n - 1) + 1)
        worst2 = max(worst2, abs(gp - n * (1 - P ** (n - 1))) / max(1, abs(gp)))
    return worst1, worstF, worst2


def check_A3_A4(nsamp=40):
    """n = 3: sample the actual branch and test it satisfies the cubic."""
    n = 3
    chi = mp.pi / 2
    zc = mp.e ** (1j * chi)
    vc = (n - 1) * zc

    def g(z):
        return z**3 + 3 * z

    def gp(z):
        return 3 * (z**2 + 1)

    a2 = 3 * zc                       # g''(zc)/2
    worst = mp.mpf(0)
    worstQ = mp.mpf(0)
    ends = []
    for sgn in (1, -1):
        d0 = sgn * mp.sqrt(1 / a2)
        z = None
        for j in range(nsamp):
            sig = mp.mpf(10) ** (mp.mpf(-8) + mp.mpf(14) * j / (nsamp - 1))
            z = (zc + d0 * mp.sqrt(sig)) if z is None else z
            for _ in range(200):
                d = gp(z)
                if d == 0:
                    break
                st = (g(z) - vc - sig) / d
                z -= st
                if abs(st) < mp.mpf(10) ** (-(mp.dps - 6)) * max(1, abs(z)):
                    break
            P = z / zc
            x, y = mp.re(P), mp.im(P)
            cubic = x**3 - 3 * x * y**2 - 3 * x + 2
            worst = max(worst, abs(cubic))
            if x > mp.mpf("1e-6"):
                worstQ = max(worstQ, abs(y**2 - (x - 1) ** 2 * (x + 2) / (3 * x)))
        ends.append(mp.arg(z / zc))
    return worst, worstQ, ends


def numerator_is_square():
    """4x^6 - 9x^4 + 4x^3 + 1: is it a perfect square of a cubic?"""
    # (2x^3 + a x^2 + b x + c)^2 matches x^5 => a = 0, x^4 => b = -9/4,
    # x^3 => c = 1; then the x^2 coefficient would be b^2 + 2ac = 81/16 != 0.
    return mp.mpf(81) / 16


if __name__ == "__main__":
    print("(A1)/(A2) polynomial identities, worst relative deviation:")
    print("  n |  g-shift = -e^{i chi} F |  F = (P-1)^2 Q  |  g' = n(1-P^{n-1})")
    ok = True
    for n in (3, 4, 5, 6, 8, 11):
        w1, wF, w2 = check_A1_A2(n)
        print(f"  {n:<2}|  {mp.nstr(w1,3):>22} |  {mp.nstr(wF,3):>14} |  {mp.nstr(w2,3)}")
        if max(w1, wF, w2) > mp.mpf("1e-30"):
            ok = False
    w, wq, ends = check_A3_A4()
    print(f"\n(A3) n=3 branch on the cubic x^3-3xy^2-3x+2: max |cubic| = {mp.nstr(w,4)}")
    print(f"     max |y^2 - (x-1)^2(x+2)/(3x)|          = {mp.nstr(wq,4)}")
    print(f"     branch exit directions in the P-plane  = "
          f"{mp.nstr(ends[0]/mp.pi,6)} pi , {mp.nstr(ends[1]/mp.pi,6)} pi")
    print(f"     predicted                              = 0.166667 pi , -0.5 pi")
    if w > mp.mpf("1e-25") or wq > mp.mpf("1e-20"):
        ok = False
    print(f"\n(A4) arclength numerator's x^2 coefficient obstruction = "
          f"{mp.nstr(numerator_is_square(),6)} != 0, so 1+y'^2 is not a perfect "
          f"square: kappa_3 has no elementary closed form.")
    print("PASS" if ok else "FAIL")
    import sys
    sys.exit(0 if ok else 1)
