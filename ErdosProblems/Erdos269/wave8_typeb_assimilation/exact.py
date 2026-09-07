"""Exact-arithmetic engine for Erdos 269 wave-8 assimilation.

All decisions are integer comparisons on certified rational brackets.
No floating point enters any predicate.
"""
from fractions import Fraction
from decimal import Decimal, getcontext

getcontext().prec = 1200

# ---------- certified rational brackets for the logarithm constants ----------
def _bracket(dec_val, guard=60):
    """Rational bracket around a Decimal, dropping `guard` trailing digits."""
    p = getcontext().prec - guard
    q = Fraction(10) ** p
    scaled = (Decimal(dec_val) * Decimal(10) ** p).to_integral_value(rounding='ROUND_FLOOR')
    lo = Fraction(int(scaled), 10 ** p)
    return lo, lo + 1 / q

_LN2, _LN3, _LN5 = Decimal(2).ln(), Decimal(3).ln(), Decimal(5).ln()

GAMMA_LO, GAMMA_HI = _bracket(_LN3 / _LN5)   # gamma = log_5 3
ELL_LO,   ELL_HI   = _bracket(_LN2 / _LN5)   # ell   = log_5 2
ALPHA_LO, ALPHA_HI = _bracket(_LN3 / _LN2)   # alpha = log_2 3
BETA_LO,  BETA_HI  = _bracket(_LN5 / _LN2)   # beta  = log_2 5


def floor_sum(n, m, a, b):
    """sum_{i=0}^{n-1} floor((a*i+b)/m) for integers, m>0, n>=0."""
    assert m > 0 and n >= 0
    ans = 0
    if a < 0:
        a2 = a % m
        ans -= n * (n - 1) // 2 * ((a2 - a) // m)
        a = a2
    if b < 0:
        b2 = b % m
        ans -= n * ((b2 - b) // m)
        b = b2
    while True:
        if a >= m:
            ans += n * (n - 1) // 2 * (a // m)
            a %= m
        if b >= m:
            ans += n * (b // m)
            b %= m
        y_max = a * n + b
        if y_max < m:
            break
        n = y_max // m
        b = y_max % m
        m, a = a, m
    return ans


def _floor_sum_rat(p, g, c):
    """sum_{u<p} floor(u*g + c) for Fractions g, c."""
    m = g.denominator * c.denominator
    a = g.numerator * c.denominator
    b = c.numerator * g.denominator
    return floor_sum(p, m, a, b)


def W(p, M, gamma, ell):
    """-sum_{u<p} floor(u*gamma - M*ell)."""
    return -_floor_sum_rat(p, gamma, -M * ell)


def C_p(p, A, n):
    """#{(u,v) >=0 : u<p, 2^(A+n) <= 3^u 5^v < 2^(A+n+1)}, certified.

    Returns the integer, or None if the two brackets disagree.
    """
    M = A + n
    lo = W(p, M + 1, GAMMA_LO, ELL_LO) - W(p, M, GAMMA_LO, ELL_LO)
    hi = W(p, M + 1, GAMMA_HI, ELL_HI) - W(p, M, GAMMA_HI, ELL_HI)
    return lo if lo == hi else None


def C_p_brute(p, A, n):
    """Direct integer enumeration; only for validating C_p at small p."""
    M = A + n
    lo_b, hi_b = 1 << M, 1 << (M + 1)
    total, pw3 = 0, 1
    for _u in range(p):
        if pw3 >= hi_b:
            break
        x = pw3
        while x < lo_b:
            x *= 5
        if x < hi_b:
            total += 1
        pw3 *= 3
    return total


def convergents(lo, hi, count):
    """Convergents (num, den) common to both rational bounds -> certified."""
    def cf(x, k):
        out = []
        for _ in range(k):
            a = x.numerator // x.denominator
            out.append(a)
            x -= a
            if x == 0:
                return out, True
            x = 1 / x
        return out, False
    n_terms = count + 40
    c1, _ = cf(lo, n_terms)
    c2, _ = cf(hi, n_terms)
    common = 0
    for a, b in zip(c1, c2):
        if a != b:
            break
        common += 1
    common -= 2                      # drop the last, precision-fragile term
    h0, h1, k0, k1 = 1, c1[0], 0, 1
    out = []
    for a in c1[1:common]:
        h0, h1 = h1, a * h1 + h0
        k0, k1 = k1, a * k1 + k0
        out.append((h1, k1))
        if len(out) >= count:
            break
    return out


# ---------- the shell counter T(t) = P35(2^t), certified, O(log t) ----------
def _ceil_div_rat(t, a_lo, a_hi):
    """ceil(t/alpha) certified by both brackets (t>=1, alpha irrational)."""
    lo = -((-t * a_hi.denominator) // a_hi.numerator)
    hi = -((-t * a_lo.denominator) // a_lo.numerator)
    return lo if lo == hi else None


def T(t):
    """#{(u,v)>=0 : 3^u 5^v < 2^t}, exact, via certified floor sums."""
    if t <= 0:
        return 0
    U = _ceil_div_rat(t, ALPHA_LO, ALPHA_HI)
    if U is None:
        return None
    lo = W(U, t, GAMMA_LO, ELL_LO)
    hi = W(U, t, GAMMA_HI, ELL_HI)
    return lo if lo == hi else None


def T_brute(t):
    lim = 1 << t
    tot, p3 = 0, 1
    while p3 < lim:
        x = p3
        while x < lim:
            tot += 1
            x *= 5
        p3 *= 3
    return tot


def s(t):
    """shell population #{(u,v): 2^t <= 3^u 5^v < 2^(t+1)}."""
    a, b = T(t + 1), T(t)
    return None if (a is None or b is None) else a - b


def T_real(t_lo, t_hi):
    """#{(u,v)>=0 : u*alpha+v*beta < t} for a rational bracket [t_lo,t_hi] of t.

    T(t) = -sum_{u<U} floor(u*gamma - t*ell),  U = ceil(t/alpha).
    Certified: computed under both (gamma,ell) endpoints AND both t endpoints.
    Returns the common value, else None.
    """
    if t_hi <= 0:
        return 0
    vals = set()
    for t in (t_lo, t_hi):
        Us = set()
        for al in (ALPHA_LO, ALPHA_HI):
            Us.add(-((-t.numerator * al.denominator) // (t.denominator * al.numerator)))
        if len(Us) != 1:
            return None
        U = Us.pop()
        if U < 0:
            return None
        for g, e in ((GAMMA_LO, ELL_LO), (GAMMA_HI, ELL_HI)):
            vals.add(-_floor_sum_rat(U, g, -t * e))
    return vals.pop() if len(vals) == 1 else None
