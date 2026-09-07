"""Exact dyadic complex-ball arithmetic for the Erdos-1041 certified excess engine.

Everything here is EXACT rational arithmetic (fractions.Fraction over dyadic
rationals) with explicit outward rounding.  No floating point enters any
certified quantity; floats are used only by callers for scouting.

A ball is  B(c, r) = { z : |z - c| <= r },  c = a + b i with a, b dyadic
rationals, r a nonnegative dyadic rational.  Every operation returns a ball
that provably CONTAINS the exact image set.
"""

from fractions import Fraction as Fr

# ---------------------------------------------------------------- rounding --

PREC = 100      # significant bits kept in ball centres
RPREC = 60      # significant bits kept in ball radii (always rounded UP)


def _bits(q):
    """floor(log2|q|)-ish: n.bit_length() - d.bit_length() for q = n/d."""
    return q.numerator.bit_length() - q.denominator.bit_length()


def snap_near(q, prec=PREC):
    """Round q to ~prec significant bits.  Returns (qh, err) with |q-qh| <= err."""
    if q == 0:
        return Fr(0), Fr(0)
    neg = q < 0
    if neg:
        q = -q
    sh = prec - _bits(q)
    if sh >= 0:
        num, den = q.numerator << sh, q.denominator
    else:
        num, den = q.numerator, q.denominator << (-sh)
    m = (2 * num + den) // (2 * den)
    if sh >= 0:
        qh = Fr(m, 1 << sh)
        err = Fr(1, 1 << (sh + 1))
    else:
        qh = Fr(m << (-sh))
        err = Fr(1 << (-sh - 1))
    return (-qh if neg else qh), err


def _snap_pos_up(q, prec):
    sh = prec - _bits(q)
    if sh >= 0:
        num, den = q.numerator << sh, q.denominator
    else:
        num, den = q.numerator, q.denominator << (-sh)
    m = -((-num) // den)                      # ceiling division
    return Fr(m, 1 << sh) if sh >= 0 else Fr(m << (-sh))


def _snap_pos_dn(q, prec):
    sh = prec - _bits(q)
    if sh >= 0:
        num, den = q.numerator << sh, q.denominator
    else:
        num, den = q.numerator, q.denominator << (-sh)
    m = num // den
    return Fr(m, 1 << sh) if sh >= 0 else Fr(m << (-sh))


def snap_up(q, prec=RPREC):
    """Smallest ~prec-bit dyadic >= q  (any sign)."""
    if q == 0:
        return Fr(0)
    if q > 0:
        return _snap_pos_up(q, prec)
    return -_snap_pos_dn(-q, prec)


def snap_dn(q, prec=RPREC):
    """Largest ~prec-bit dyadic <= q  (any sign)."""
    if q == 0:
        return Fr(0)
    if q > 0:
        return _snap_pos_dn(q, prec)
    return -_snap_pos_up(-q, prec)


# ------------------------------------------------------------ integer roots --

def iroot(N, n):
    """floor(N ** (1/n)) for integers N >= 0, n >= 1 (exact)."""
    if N < 0:
        raise ValueError("iroot of negative")
    if N == 0:
        return 0
    if n == 1:
        return N
    x = 1 << ((N.bit_length() + n - 1) // n)
    while True:
        y = ((n - 1) * x + N // (x ** (n - 1))) // n
        if y >= x:
            return x
        x = y


def nthroot_lo(q, n, prec=RPREC):
    """Dyadic t with 0 <= t and t**n <= q  (q >= 0 Fraction)."""
    if q <= 0:
        return Fr(0)
    P = prec + 8
    N = (q.numerator << (n * P)) // q.denominator
    t = iroot(N, n)
    return snap_dn(Fr(t, 1 << P), prec)


def nthroot_hi(q, n, prec=RPREC):
    """Dyadic t with t**n >= q  (q >= 0 Fraction)."""
    if q <= 0:
        return Fr(0)
    P = prec + 8
    num = q.numerator << (n * P)
    N = -((-num) // q.denominator)            # ceil
    t = iroot(N, n) + 1
    return snap_up(Fr(t, 1 << P), prec)


def sqrt_lo(q, prec=RPREC):
    return nthroot_lo(q, 2, prec)


def sqrt_hi(q, prec=RPREC):
    return nthroot_hi(q, 2, prec)


# ------------------------------------------------------------ complex balls --

class CB:
    """Complex ball  {z : |z - (a + b i)| <= r},  a, b, r dyadic Fractions."""

    __slots__ = ("a", "b", "r")

    def __init__(self, a, b=0, r=0, _raw=False):
        a = Fr(a)
        b = Fr(b)
        r = Fr(r)
        if _raw:
            self.a, self.b, self.r = a, b, r
            return
        ah, ea = snap_near(a)
        bh, eb = snap_near(b)
        # displacement of the centre is bounded by ea + eb (>= sqrt(ea^2+eb^2))
        self.a, self.b = ah, bh
        self.r = snap_up(r + ea + eb)

    # -- basic accessors ---------------------------------------------------
    def cabs2(self):
        return self.a * self.a + self.b * self.b

    def abs_hi(self):
        return snap_up(sqrt_hi(self.cabs2()) + self.r)

    def abs_lo(self):
        v = sqrt_lo(self.cabs2()) - self.r
        return snap_dn(v) if v > 0 else Fr(0)

    def re_lo(self):
        return self.a - self.r

    def re_hi(self):
        return self.a + self.r

    def re_interval(self):
        return (self.a - self.r, self.a + self.r)

    def contains_zero(self):
        return self.cabs2() <= self.r * self.r

    # -- arithmetic --------------------------------------------------------
    def __add__(self, o):
        o = _as_cb(o)
        return CB(self.a + o.a, self.b + o.b, self.r + o.r)

    __radd__ = __add__

    def __sub__(self, o):
        o = _as_cb(o)
        return CB(self.a - o.a, self.b - o.b, self.r + o.r)

    def __rsub__(self, o):
        return _as_cb(o).__sub__(self)

    def __neg__(self):
        return CB(-self.a, -self.b, self.r, _raw=True)

    def __mul__(self, o):
        o = _as_cb(o)
        a, b, r = self.a, self.b, self.r
        c, d, s = o.a, o.b, o.r
        na = a * c - b * d
        nb = a * d + b * c
        if r == 0:
            nr = Fr(0) if s == 0 else sqrt_hi(a * a + b * b) * s
        elif s == 0:
            nr = sqrt_hi(c * c + d * d) * r
        else:
            nr = (sqrt_hi(a * a + b * b) * s + sqrt_hi(c * c + d * d) * r
                  + r * s)
        return CB(na, nb, nr)

    __rmul__ = __mul__

    def inv(self):
        """1 / B.  Exact disc inverse; requires |c| > r."""
        den = self.cabs2() - self.r * self.r
        if den <= 0:
            raise ZeroDivisionError("ball contains 0")
        return CB(self.a / den, -self.b / den, self.r / den)

    def __truediv__(self, o):
        return self * _as_cb(o).inv()

    def __rtruediv__(self, o):
        return _as_cb(o) * self.inv()

    def conj(self):
        return CB(self.a, -self.b, self.r, _raw=True)

    def widen(self, extra):
        return CB(self.a, self.b, snap_up(self.r + Fr(extra)), _raw=True)

    def mid(self):
        return CB(self.a, self.b, Fr(0), _raw=True)

    def __repr__(self):
        return "CB(%.17g%+.17gj, r=%.3g)" % (float(self.a), float(self.b),
                                             float(self.r))


def _as_cb(o):
    if isinstance(o, CB):
        return o
    if isinstance(o, complex):
        return CB(Fr(o.real), Fr(o.imag))
    return CB(Fr(o), 0)


def cb(a, b=0, r=0):
    return CB(Fr(a), Fr(b), Fr(r))


def mpf_to_fr(x):
    """EXACT conversion of an mpmath mpf to a Fraction (via its (s,m,e) triple)."""
    t = x._mpf_
    sign, man, exp = t[0], t[1], t[2]
    if man == 0:
        return Fr(0)
    v = Fr(man << exp) if exp >= 0 else Fr(man, 1 << (-exp))
    return -v if sign else v


def cb_pt(z):
    """Zero-radius ball at a SCOUTED point (coordinates snapped to PREC bits).

    The scout's accuracy is never trusted: callers always build a disc around
    this point that provably covers the a-priori reachable set.
    """
    try:
        a, b = mpf_to_fr(z.real), mpf_to_fr(z.imag)
    except AttributeError:
        a, b = mpf_to_fr(z), Fr(0)
    return CB(snap_dn(a, PREC), snap_dn(b, PREC), Fr(0), _raw=True)


def cb_from_mp(z, r=0):
    """Ball around an mpmath/complex value; r is an ADDITIONAL radius."""
    try:
        re, im = Fr(str(z.real)), Fr(str(z.imag))
    except Exception:
        re, im = Fr(repr(complex(z).real)), Fr(repr(complex(z).imag))
    return CB(re, im, Fr(r))


def poly_cb(coeffs, x):
    """Horner evaluation of sum coeffs[i] x^(n-i) over balls."""
    acc = coeffs[0]
    for c in coeffs[1:]:
        acc = acc * x + c
    return acc


# ---------------------------------------------------- Krawczyk root test ----

def krawczyk(coeffs, dcoeffs, target, centre, rad, iters=3):
    """Certify a unique root of  P(x) - target  in the disc D(centre, rad).

    coeffs / dcoeffs : ball coefficient lists of P and P' (high degree first)
    centre           : CB with r == 0 (an exact point)
    rad              : Fraction > 0
    Returns a CB enclosure of THE unique root in D(centre, rad), or None.

    Validity: for holomorphic f, f(z)-f(c) = (int_0^1 f'(c+t(z-c))dt)(z-c) and
    the disc D is convex, so the average lies in f'(D).  Hence
    g(z) = z - Y f(z) maps D into K(D); K(D) subset int D gives a contraction
    with a unique fixed point (Brouwer + Banach), i.e. a unique zero of f.
    """
    c = centre
    R = Fr(rad)
    best = None
    for _ in range(iters):
        D = CB(c.a, c.b, R, _raw=True)
        fc = poly_cb(coeffs, c) - target
        fpc = poly_cb(dcoeffs, c)
        if fpc.contains_zero():
            return best
        Y = fpc.inv()
        Yfc = Y * fc
        fpD = poly_cb(dcoeffs, D)
        M = CB(1, 0, 0) - Y * fpD
        mhi = M.abs_hi()
        step_hi = Yfc.abs_hi()
        newR = snap_up(Yfc.r + mhi * R)
        if step_hi + newR >= R:          # K(D) not strictly inside D
            return best
        # unique root exists in D and lies in K(D)
        na, ea = snap_near(c.a - Yfc.a)
        nb, eb = snap_near(c.b - Yfc.b)
        newR = snap_up(newR + ea + eb)
        best = CB(na, nb, newR, _raw=True)
        if newR >= R:
            break
        c, R = CB(na, nb, Fr(0), _raw=True), newR
    return best
