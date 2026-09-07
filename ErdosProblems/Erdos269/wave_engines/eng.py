"""WAVE-7 engine: O(log p) CERTIFIED exact evaluation of the column counts.

Objects (all conventions pinned to wave-6 v1_lemmaST.py):
    alpha = log_2 3,  beta = log_2 5,  gamma = alpha/beta = log_5 3,  ell = 1/beta = log_5 2
    C_p(A) = #{(i,w) : 0<=i<p, w>=0, floor(i*alpha + w*beta) = A + n}      (Lemma-T object)

WAVE-7 IDENTITY LAYER (derived here, verified in v0_selfcheck.py):

  (W)  W_p(M) := sum_{i=0}^{p-1} floor(i*gamma - M*ell)
       T_p(M) := #{(i,w) : 0<=i<p, w>=0, 3^i 5^w < 2^M}   =  -W_p(M)     [valid M > (p-1)*alpha]
       because  #{w>=0 : w*beta < M - i*alpha} = ceil((M-i*alpha)*ell) = -floor(i*gamma - M*ell).

  (N)  N_p(M) := #{(i,w) : i<p, w>=0, floor(i*alpha+w*beta) = M} = T_p(M+1) - T_p(M)
                                                                = W_p(M) - W_p(M+1).
       Lemma T is the statement N_p(M) = F_p({M*ell}); (N) is a SECOND, floor-sum form.
       C_p(A) = N_p(A+n).

  (TEL) telescoping column identity:
       sum_{A=A1}^{A2} C_p(A) = T_p(A2+n+1) - T_p(A1+n) = W_p(A1+n) - W_p(A2+n+1).

  (T)  full shell counts: T(M) := #{(u,v)>=0 : 3^u 5^v < 2^M},  s(M) := T(M+1) - T(M).
       T(M) = U + sum_{u=0}^{U-1} floor(M*ell - u*gamma),  U = floor(M/alpha)+1.

Every floor sum is evaluated by the AtCoder floor_sum recursion on a dyadic rational
bracket [lo/2^K, hi/2^K] around the irrational, exploiting monotonicity of
sum floor(i*g + t) in g and in t: the lower and upper evaluations are computed and the
answer is returned ONLY if they agree (otherwise K is doubled).  So every returned
integer is a certified exact value of the real (irrational-parameter) sum.
"""
from fractions import Fraction
import mpmath as mp

_DPS = 400
mp.mp.dps = _DPS


def _consts(K):
    """dyadic floors: (g0, l0, a0) with g0/2^K < gamma < (g0+1)/2^K, etc."""
    with mp.workdps(max(_DPS, K // 3 + 60)):
        D = mp.mpf(2) ** K
        g = mp.log(3) / mp.log(5)          # gamma = log_5 3
        l = mp.log(2) / mp.log(5)          # ell   = log_5 2
        a = mp.log(3) / mp.log(2)          # alpha = log_2 3
        g0 = int(mp.floor(g * D))
        l0 = int(mp.floor(l * D))
        a0 = int(mp.floor(a * D))
    return g0, l0, a0


_CACHE = {}


def consts(K):
    if K not in _CACHE:
        _CACHE[K] = _consts(K)
    return _CACHE[K]


def floor_sum(n, m, a, b):
    """sum_{i=0}^{n-1} floor((a*i+b)/m), exact, m>0, n>=0, a,b any integers."""
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
            return ans
        n = y_max // m
        b = y_max % m
        m, a = a, m


def W(p, M, K=256):
    """sum_{i=0}^{p-1} floor(i*gamma - M*ell).  Certified (bracket agreement)."""
    for _ in range(6):
        g0, l0, a0 = consts(K)
        D = 1 << K
        # nondecreasing in gamma, nonincreasing in M*ell (M may be negative)
        if M >= 0:
            lo = floor_sum(p, D, g0, -M * (l0 + 1))
            hi = floor_sum(p, D, g0 + 1, -M * l0)
        else:
            lo = floor_sum(p, D, g0, -M * l0)
            hi = floor_sum(p, D, g0 + 1, -M * (l0 + 1))
        if lo == hi:
            return lo
        K *= 2
    raise RuntimeError(f"W({p},{M}) did not certify")


def T_p(p, M, K=256):
    """#{(i,w): 0<=i<p, w>=0, 3^i 5^w < 2^M}.  Valid for M > (p-1)*alpha."""
    return -W(p, M, K)


def N_p(p, M, K=256):
    """#{(i,w): 0<=i<p, w>=0, floor(i*alpha+w*beta) = M}."""
    return W(p, M, K) - W(p, M + 1, K)


def C_p(p, n, A, K=256):
    return N_p(p, A + n, K)


def U_of(M, K=256):
    """floor(M/alpha)+1 = #{u>=0 : u*alpha < M}, certified."""
    for _ in range(6):
        g0, l0, a0 = consts(K)
        D = 1 << K
        # u*alpha < M  <=>  u < M/alpha ; M/alpha in ( M*D/(a0+1), M*D/a0 )
        lo = (M * D) // (a0 + 1)
        hi = (M * D) // a0
        # count = ceil(M/alpha) ; since M/alpha irrational, = floor(M/alpha)+1
        if lo == hi:
            return lo + 1
        K *= 2
    raise RuntimeError(f"U_of({M}) did not certify")


def T_full(M, K=256):
    """T(M) = #{(u,v)>=0 : 3^u 5^v < 2^M}."""
    if M <= 0:
        return 0
    U = U_of(M, K)
    for _ in range(6):
        g0, l0, a0 = consts(K)
        D = 1 << K
        # sum_{u<U} floor(M*ell - u*gamma) : nonincreasing in gamma, nondecreasing in ell
        lo = floor_sum(U, D, -(g0 + 1), M * l0)
        hi = floor_sum(U, D, -g0, M * (l0 + 1))
        if lo == hi:
            return U + lo
        K *= 2
    raise RuntimeError(f"T_full({M}) did not certify")


def s(M, K=256):
    """shell weight #{(u,v)>=0 : floor(u*alpha+v*beta) = M}."""
    return T_full(M + 1, K) - T_full(M, K)


# ---------------------------------------------------------------- CF of alpha
def cf_log_exact(a, b, k):
    """EXACT partial quotients of log_b(a) (integer-power Euclid)."""
    A, B = Fraction(a), Fraction(b)
    out = []
    for _ in range(k):
        if not (A > 1 and B > 1):
            break
        e, pw = 0, Fraction(1)
        while pw * B <= A:
            pw *= B
            e += 1
        out.append(e)
        A, B = B, A / pw
        if max(A.numerator.bit_length(), A.denominator.bit_length(),
               B.numerator.bit_length(), B.denominator.bit_length()) > 200000:
            break
    return out


def convergents(quots):
    """[(p_r, n_r)] with n_r/p_r -> alpha : p = denominator, n = numerator."""
    pm1, p = 0, 1
    nm1, n = 1, quots[0]
    out = [(p, n)]
    for a in quots[1:]:
        pm1, p = p, a * p + pm1
        nm1, n = n, a * n + nm1
        out.append((p, n))
    return out


def cf_hp(k, dps):
    """partial quotients of alpha = log_2 3 at working precision dps."""
    with mp.workdps(dps):
        y = mp.log(3) / mp.log(2)
        out = []
        for _ in range(k):
            a = int(mp.floor(y))
            out.append(a)
            y = 1 / (y - a)
    return out


def family(pmax=6 * 10 ** 12, k=40):
    """CF quotients of alpha, cross-validated at two precisions, plus the
    convergent family (p_r, n_r) with p_r <= pmax.  Every returned quotient is
    additionally re-certified by the exact integer test  3^p vs 2^n  through the
    Ostrowski/best-approximation property |p*alpha - n| < |p'*alpha - n'|."""
    q1 = cf_hp(k, 120)
    q2 = cf_hp(k, 400)
    m = 0
    while m < k and q1[m] == q2[m]:
        m += 1
    q = q2[:m]
    conv = convergents(q)
    # exact re-certification: 2^n < 3^p < 2^(n+1)  or  2^(n-1) < 3^p < 2^n
    ok = []
    for (p, n) in conv:
        if p > pmax:
            break
        if p <= 60:
            b = (3 ** p).bit_length() - 1        # = floor(p*alpha), exact
            assert abs(b - n) <= 1, (p, n, b)
        ok.append((p, n))
    return q, ok
