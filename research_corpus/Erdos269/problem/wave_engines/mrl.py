"""Wave-6 (MRL') engine.

gamma = log_5 3, ell = log_5 2, J = (1-ell, 1).
F_p(x) = #{0 <= i < p : {x - i*gamma} in J}
       = #{0 <= i < p : x in A_i},  A_i = (i*gamma - ell, i*gamma) mod 1.
mu_p = |{x : F_p(x) odd}|.

Equivalently F_p(x) = #(P cap (x, x+ell)) with P = {{i*gamma} : i < p}, so the
parity of F_p flips at each of the 2p points  Z = P u (P - ell), which are
pairwise distinct by unique factorisation (3^a 2 != 5^b).

Everything is a sweep over the exactly-sorted event list; precision is checked by
requiring the minimal gap of Z to exceed a certified margin.
"""
import mpmath as mp

mp.mp.dps = 60
_L2, _L3, _L5 = mp.log(2), mp.log(3), mp.log(5)
GAM = _L3 / _L5          # log_5 3
ELL = _L2 / _L5          # log_5 2
ALPHA = _L3 / _L2        # log_2 3
BETA = _L5 / _L2         # log_2 5


def events(p, gam=None, ell=None):
    """sorted [(x, d)] : d=+1 at i*gam-ell (F jumps up), d=-1 at i*gam."""
    gam = GAM if gam is None else gam
    ell = ELL if ell is None else ell
    ev = []
    for i in range(p):
        t = mp.frac(i * gam)
        ev.append((t, -1))
        ev.append((mp.frac(t - ell), +1))
    ev.sort(key=lambda z: z[0])
    return ev


def mingap(ev):
    m = 1 + ev[0][0] - ev[-1][0]
    for k in range(len(ev) - 1):
        g = ev[k + 1][0] - ev[k][0]
        if g < m:
            m = g
    return m


def profile(p, gam=None, ell=None, margin=mp.mpf('1e-30')):
    """(mu_p, value-histogram of F_p as {v: measure}, mingap).

    Sweep starts on the interval immediately AFTER the smallest event, whose
    F-value is counted directly at its midpoint (safe: distance to any event
    >= mingap/2 >> precision)."""
    gam = GAM if gam is None else gam
    ell = ELL if ell is None else ell
    ev = events(p, gam, ell)
    mg = mingap(ev)
    assert mg > margin, f"mingap {mg} below margin at p={p}"
    n = len(ev)
    x0 = ev[0][0] + mg / 2
    f = 0
    for i in range(p):
        if mp.frac(x0 - i * gam) > 1 - ell:
            f += 1
    hist = {}
    for k in range(n):
        lo = ev[k][0]
        hi = ev[k + 1][0] if k + 1 < n else ev[0][0] + 1
        hist[f] = hist.get(f, 0) + (hi - lo)
        if k + 1 < n:
            f += ev[k + 1][1]
    mu = sum(v for k, v in hist.items() if k & 1)
    return mu, hist, mg


def mu(p, gam=None, ell=None):
    return profile(p, gam, ell)[0]


def mu_float(p):
    """float64 sweep, same convention; for large p.  Validated against profile()."""
    gam, ell = float(GAM), float(ELL)
    ev = []
    for i in range(p):
        t = (i * gam) % 1.0
        ev.append((t, -1))
        ev.append(((t - ell) % 1.0, +1))
    ev.sort()
    mg = min([ev[k + 1][0] - ev[k][0] for k in range(len(ev) - 1)] +
             [1 + ev[0][0] - ev[-1][0]])
    x0 = ev[0][0] + mg / 2
    f = sum(1 for i in range(p) if (x0 - i * gam) % 1.0 > 1 - ell)
    tot = 0.0
    n = len(ev)
    for k in range(n):
        lo = ev[k][0]
        hi = ev[k + 1][0] if k + 1 < n else ev[0][0] + 1
        if f & 1:
            tot += hi - lo
        if k + 1 < n:
            f += ev[k + 1][1]
    return tot, mg


# ------------------------------------------------------------------ CF machinery
def cf(x, k):
    """CF partial quotients of mpf x (float route)."""
    y = mp.mpf(x)
    out = []
    for _ in range(k):
        a = int(mp.floor(y))
        out.append(a)
        y = y - a
        if y == 0:
            break
        y = 1 / y
    return out


def cf_log_exact(a, b, k):
    """EXACT partial quotients of log_b(a) for integers a,b>1, by integer powers.

    x_0 = log_b a.  a_t = floor(x_t) is the largest e with b^e <= a (exact int
    comparison); then x_{t+1} = 1/(x_t - a_t) = log_{a / b^{a_t}}(b), i.e. swap
    (a, b) -> (b, a / b^{a_t}) with a/b^{a_t} kept as an exact Fraction."""
    from fractions import Fraction
    A, B = Fraction(a), Fraction(b)
    out = []
    for _ in range(k):
        # largest e >= 0 with B^e <= A   (A > 1, B > 1 maintained)
        if not (A > 1 and B > 1):
            break
        e, pw = 0, Fraction(1)
        while pw * B <= A:
            pw *= B
            e += 1
            if e > 10 ** 4:
                break
        out.append(e)
        A, B = B, A / pw
        # size guard
        if max(A.numerator.bit_length(), A.denominator.bit_length(),
               B.numerator.bit_length(), B.denominator.bit_length()) > 200000:
            break
    return out


def denominators(quots):
    """convergent denominators q_j from partial quotients [a0,a1,...]."""
    qm1, q = 1, quots[0] * 0 + 1   # q_0 = 1
    qs = [1]
    prev, cur = 0, 1
    for a in quots[1:]:
        prev, cur = cur, a * cur + prev
        qs.append(cur)
    return qs


def numerators(quots):
    prev, cur = 1, quots[0]
    ps = [quots[0]]
    for a in quots[1:]:
        prev, cur = cur, a * cur + prev
        ps.append(cur)
    return ps


def ostrowski(p, quots, qs):
    """greedy Ostrowski digits c_j with p = sum_j c_j q_j (j>=0), 0<=c_j<=a_{j+1}.

    Greedy from the top is the standard (unique, with the Markov condition)
    representation; we return the digit vector and verify the sum."""
    c = [0] * len(qs)
    r = p
    for j in range(len(qs) - 1, -1, -1):
        if qs[j] <= r:
            c[j] = r // qs[j]
            r -= c[j] * qs[j]
    assert r == 0 and sum(c[j] * qs[j] for j in range(len(qs))) == p
    return c


def dist2Z(t):
    """distance from t to the nearest EVEN integer (in [0,1])."""
    u = mp.frac(mp.mpf(t) / 2) * 2
    return u if u <= 1 else 2 - u
