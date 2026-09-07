"""Exact lattice layer for the J-lemma instantiation.

Lambda = { c in Z^m : sum_r c_r * Ehat'_r = 0  (mod m0) },  m0 = P/2.

Everything that enters a certificate is exact Python-integer arithmetic.
LLL runs on a float64 Gram-Schmidt but only performs UNIMODULAR row ops,
so the output is a basis of Lambda no matter how bad the float GSO is;
we independently re-verify membership and determinant afterwards.
"""
from math import gcd


# --------------------------------------------------------------- Lambda basis
def _xgcd(a, b):
    if b == 0:
        return (abs(a), 1 if a >= 0 else -1, 0)
    old_r, r = a, b
    old_s, s = 1, 0
    old_t, t = 0, 1
    while r:
        q = old_r // r
        old_r, r = r, old_r - q * r
        old_s, s = s, old_s - q * s
        old_t, t = t, old_t - q * t
    if old_r < 0:
        old_r, old_s, old_t = -old_r, -old_s, -old_t
    return old_r, old_s, old_t


def lambda_basis(g, m0):
    """Upper-triangular basis of {c : sum c_r g_r = 0 mod m0}.
    Returns (rows, diag, index) with index = prod(diag) = [Z^m : Lambda]."""
    m = len(g)
    g = [x % m0 for x in g]
    h = [0] * (m + 1)
    h[m] = m0
    for r in range(m - 1, -1, -1):
        h[r] = gcd(g[r], h[r + 1])
    # Bezout at each level: h[s] = u_s*g_s + w_s*h[s+1]
    U = [0] * m
    Wc = [0] * m
    for s in range(m):
        d, u, w = _xgcd(g[s], h[s + 1])
        assert d == h[s], (s, d, h[s])
        U[s] = u
        Wc[s] = w

    def express(t, r):
        """coefficients c_{r+1..m-1} with sum c_s g_s = t (mod m0); needs h[r+1] | t."""
        c = [0] * m
        for s in range(r + 1, m):
            assert t % h[s] == 0
            q = t // h[s]
            c[s] = q * U[s]
            t = q * Wc[s] * h[s + 1]
        assert t % m0 == 0
        return c

    rows = []
    diag = []
    for r in range(m):
        vr = h[r + 1] // h[r]
        row = express((-vr * g[r]) % m0, r)
        row[r] = vr
        rows.append(row)
        diag.append(vr)
    # HNF back-reduction: bound off-diagonal entries by the diagonal
    for r in range(m - 1, -1, -1):
        for s in range(r + 1, m):
            q = rows[r][s] // rows[s][s]
            if q:
                for t2 in range(s, m):
                    rows[r][t2] -= q * rows[s][t2]
    idx = 1
    for d in diag:
        idx *= d
    return rows, diag, idx


def in_lambda(c, g, m0):
    return sum(ci * gi for ci, gi in zip(c, g)) % m0 == 0


def det_bareiss(M):
    """Exact determinant, fraction-free."""
    n = len(M)
    A = [row[:] for row in M]
    sign = 1
    prev = 1
    for k in range(n - 1):
        if A[k][k] == 0:
            piv = None
            for i in range(k + 1, n):
                if A[i][k] != 0:
                    piv = i
                    break
            if piv is None:
                return 0
            A[k], A[piv] = A[piv], A[k]
            sign = -sign
        for i in range(k + 1, n):
            for j in range(k + 1, n):
                A[i][j] = (A[i][j] * A[k][k] - A[i][k] * A[k][j]) // prev
            A[i][k] = 0
        prev = A[k][k]
    return sign * A[n - 1][n - 1]


# ------------------------------------------------------------------- LLL
def lll(B, delta=0.99, max_steps=200000):
    """LLL on integer rows. Unimodular row ops only -> output is a basis
    of the same lattice regardless of float-GSO accuracy."""
    import numpy as np
    n = len(B)
    d = len(B[0])
    B = [list(r) for r in B]
    mx = max(abs(x) for r in B for x in r) or 1
    sc = 1e60 / float(mx)
    Bf = np.array([[float(x) * sc for x in r] for r in B], dtype=np.float64)

    def gso():
        mu = np.zeros((n, n))
        Bs = np.zeros((n, d))
        Bn = np.zeros(n)
        for i in range(n):
            v = Bf[i].copy()
            for j in range(i):
                if Bn[j] > 0.0:
                    m_ij = float(Bf[i] @ Bs[j]) / Bn[j]
                    mu[i, j] = m_ij
                    if m_ij != 0.0:
                        v -= m_ij * Bs[j]
            Bs[i] = v
            Bn[i] = float(v @ v)
        return mu, Bn

    MU, BS, BN = None, None, None

    def gso_full():
        nonlocal MU, BS, BN
        MU, BS, BN = np.zeros((n, n)), np.zeros((n, d)), np.zeros(n)
        for i in range(n):
            v = Bf[i].copy()
            for j in range(i):
                if BN[j] > 0.0:
                    m_ij = float(Bf[i] @ BS[j]) / BN[j]
                    MU[i, j] = m_ij
                    if m_ij != 0.0:
                        v -= m_ij * BS[j]
            BS[i] = v
            BN[i] = float(v @ v)

    def gso_row(k):
        """Refresh row k of the GSO (rows < k unchanged by size reduction)."""
        v = Bf[k].copy()
        for j in range(k):
            if BN[j] > 0.0:
                m = float(Bf[k] @ BS[j]) / BN[j]
                MU[k, j] = m
                if m != 0.0:
                    v -= m * BS[j]
            else:
                MU[k, j] = 0.0
        BS[k] = v
        BN[k] = float(v @ v)

    def size_reduce(k):
        """Iterate size reduction until stable -- float mu can be off by
        many ulps when |mu| ~ 1e28, so ONE pass is not enough."""
        for _ in range(10):
            changed = False
            for l in range(k - 1, -1, -1):
                if abs(MU[k, l]) <= 0.5:
                    continue
                q = int(round(MU[k, l]))
                if q == 0:
                    continue
                Bk, Bl = B[k], B[l]
                B[k] = [x - q * y for x, y in zip(Bk, Bl)]
                MU[k, l] -= q
                for i in range(l):
                    MU[k, i] -= q * MU[l, i]
                changed = True
            if not changed:
                return
            Bf[k] = np.array([float(x) * sc for x in B[k]])
            gso_row(k)

    gso_full()
    k = 1
    steps = 0
    while k < n and steps < max_steps:
        steps += 1
        size_reduce(k)
        if BN[k] >= (delta - MU[k, k - 1] ** 2) * BN[k - 1]:
            k += 1
        else:
            B[k], B[k - 1] = B[k - 1], B[k]
            Bf[[k, k - 1]] = Bf[[k - 1, k]]
            gso_full()
            k = max(k - 1, 1)
    return B, steps


# -------------------------------------------------- weighted reduce + polish
def budget(c, S):
    return sum(abs(ci) * si for ci, si in zip(c, S))


def weighted_reduce(rows, S, polish_rounds=6):
    """LLL under the diagonal weighting diag(S), then greedy L1 polish.
    Returns basis rows in the ORIGINAL (unweighted) coordinates."""
    m = len(rows)
    Bw = [[rows[i][j] * S[j] for j in range(m)] for i in range(m)]
    # ITERATED LLL.  A single float64-GSO pass loses accuracy badly when the
    # entries are hundreds of bits (observed: ~100 bits of margin lost at
    # L=128).  Re-seeding the GSO from the already-shrunk basis recovers it.
    # Every pass is unimodular, so the lattice is unchanged either way.
    steps = 0
    prev = None
    for _ in range(6):
        Rw, st = lll(Bw)
        steps += st
        cur = max(abs(x) for r in Rw for x in r)
        Bw = Rw
        if prev is not None and cur >= prev:
            break
        prev = cur
    out = []
    for r in Rw:
        v = []
        for j in range(m):
            assert r[j] % S[j] == 0, "weighted LLL broke divisibility"
            v.append(r[j] // S[j])
        out.append(v)
    # greedy L1 polish: v_i <- v_i +- v_j is unimodular
    for _ in range(polish_rounds):
        moved = False
        for i in range(m):
            bi = budget(out[i], S)
            best = None
            for j in range(m):
                if i == j:
                    continue
                for sgn in (1, -1):
                    cand = [out[i][t] + sgn * out[j][t] for t in range(m)]
                    bc = budget(cand, S)
                    if bc < bi:
                        bi = bc
                        best = cand
            if best is not None:
                out[i] = best
                moved = True
        if not moved:
            break
    return out, steps
