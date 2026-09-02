"""Erdos #269 wave-2 engine.

Exact Q_a exponents, b_a, and the CORRECTED four-count identity for e_a:

    e_a = N(2^{a+1}) + 2*N(Y_a) + 4*N(Z_a) + 8*N(W_a) - 15*N(2^a)

with Y_a = min(3^{B_a+1}, 2^{a+1}), Z_a = min(5^{C_a+1}, 2^{a+1}),
W_a = min(Y_a, Z_a), B_a = floor(a*log_3 2), C_a = floor(a*log_5 2),
N(x) = #{2,3,5-smooth h : h < x}  (STRICT).

All integer/floor decisions that enter a certificate are exact:
  * B_a, C_a, b_a           -> exact big-integer power walk
  * counting-function tables -> float64 bulk kernels with a global
    min-distance-to-integer monitor AND per-entry exact big-integer
    repair of every flagged near-integer.  Threshold 1e-6 sits >4 orders
    of magnitude above the float64 error (~1e-11 at this scale).
"""
import math, time, json
from decimal import Decimal, getcontext
import numpy as np

getcontext().prec = 80
ALPHA = float(Decimal(3).ln() / Decimal(2).ln())   # log_2 3
BETA = float(Decimal(5).ln() / Decimal(2).ln())    # log_2 5
THRESH = 1e-6


# ---------------------------------------------------------------- exact radix
def radix(A):
    """B[a]=floor(a log_3 2), C[a]=floor(a log_5 2) for a=0..A+1; b[a] for a=0..A.
    Also D3[v]=#{k>=0: 5^k < 3^v}-1 = floor(v log_5 3) and
         D5[v]=#{r>=0: 3^r < 5^v}-1 = floor(v log_3 5), for the base-3/base-5 sweeps.
    Pure exact big-integer power comparisons."""
    B = [0] * (A + 2)
    C = [0] * (A + 2)
    p2 = 1
    p3 = 1
    p5 = 1
    j = k = 0
    for a in range(A + 2):
        while p3 * 3 <= p2:
            p3 *= 3
            j += 1
        while p5 * 5 <= p2:
            p5 *= 5
            k += 1
        B[a] = j
        C[a] = k
        p2 *= 2
    b = [2 * (3 if B[a + 1] > B[a] else 1) * (5 if C[a + 1] > C[a] else 1)
         for a in range(A + 1)]
    return B, C, b


def radix35(Jmax, Kmax):
    """E35[v] = floor(v*log_5 3) for v=0..Jmax  (i.e. max k with 5^k < 3^v).
       E53[v] = floor(v*log_3 5) for v=0..Kmax."""
    E35 = [0] * (Jmax + 1)
    p3 = 1
    p5 = 1
    k = 0
    for v in range(Jmax + 1):
        while p5 * 5 <= p3:
            p5 *= 5
            k += 1
        E35[v] = k
        p3 *= 3
    E53 = [0] * (Kmax + 1)
    p3 = 1
    p5 = 1
    r = 0
    for v in range(Kmax + 1):
        while p3 * 3 <= p5:
            p3 *= 3
            r += 1
        E53[v] = r
        p5 *= 5
    return E35, E53


# ----------------------------------------------------- exact near-integer fix
def _max_exp(est, X, p, TT):
    """max e >= 0 with X * p**e < TT, seeded from float estimate est."""
    e = int(est)
    if e < 0:
        e = 0
    while e > 0 and X * p ** e >= TT:
        e -= 1
    if X * p ** e >= TT:
        return -1
    while X * p ** (e + 1) < TT:
        e += 1
    return e


# ------------------------------------------------------------- sweep kernel
class Sweep:
    def __init__(self):
        self.min_dist = 1.0
        self.n_elts = 0
        self.n_flag = 0
        self.n_fix = 0

    def run(self, V, T_of_v, base_step, div, count_of_v, exact_cb):
        """out[v] = sum_{t<n} floor((T(v) - t*base_step)/div) + n,  n = count_of_v(v).

        exact_cb(v, t, est) -> exact value of floor((T(v)-t*step)/div)."""
        nmax = max(count_of_v(v) for v in range(1, V + 1))
        base = np.arange(nmax + 1, dtype=np.float64) * base_step
        buf = np.empty(nmax + 1, dtype=np.float64)
        fbuf = np.empty(nmax + 1, dtype=np.float64)
        out = np.zeros(V + 1, dtype=np.int64)
        inv = 1.0 / div
        for v in range(1, V + 1):
            n = count_of_v(v)
            bs = buf[:n]
            fs = fbuf[:n]
            np.subtract(T_of_v(v), base[:n], out=bs)
            if div != 1.0:
                np.multiply(bs, inv, out=bs)
            np.floor(bs, out=fs)
            s = fs.sum()
            np.subtract(bs, fs, out=bs)
            mn = bs.min()
            mx = bs.max()
            d = mn if mn < 1.0 - mx else 1.0 - mx
            if d < self.min_dist:
                self.min_dist = d
            if d < THRESH:
                idx = np.flatnonzero((bs < THRESH) | (bs > 1.0 - THRESH))
                self.n_flag += idx.size
                for t in idx:
                    t = int(t)
                    ex = exact_cb(v, t, fs[t])
                    if ex != int(fs[t]):
                        s += ex - int(fs[t])
                        self.n_fix += 1
            out[v] = int(s) + n
            self.n_elts += n
        return out


# ------------------------------------------------------------- N-tables
def build_tables(A, verbose=True):
    t0 = time.time()
    B, C, b = radix(A)
    Jmax = B[A + 1] + 2
    Kmax = C[A + 1] + 2
    E35, E53 = radix35(Jmax + 2, Kmax + 2)
    t1 = time.time()

    sw = Sweep()

    # ---- M2[v] = #{(r,k)>=0 : 3^r 5^k < 2^v}
    #      = sum_{r<n} floor((v - r*ALPHA)/BETA) + n,  n = B[v]+1
    def cb2(v, r, est):
        return _max_exp(est, 3 ** r, 5, 1 << v)
    M2 = sw.run(A + 1, lambda v: float(v), ALPHA, BETA,
                lambda v: B[v] + 1, cb2)
    t2 = time.time()

    # ---- M3[v] = #{(i,k)>=0 : 2^i 5^k < 3^v}
    #      = sum_{k<n} floor(v*ALPHA - k*BETA) + n,  n = E35[v]+1
    def cb3(v, k, est):
        return _max_exp(est, 5 ** k, 2, 3 ** v)
    M3 = sw.run(Jmax, lambda v: v * ALPHA, BETA, 1.0,
                lambda v: E35[v] + 1, cb3)
    t3 = time.time()

    # ---- M5[v] = #{(i,r)>=0 : 2^i 3^r < 5^v}
    def cb5(v, r, est):
        return _max_exp(est, 3 ** r, 2, 5 ** v)
    M5 = sw.run(Kmax, lambda v: v * BETA, ALPHA, 1.0,
                lambda v: E53[v] + 1, cb5)
    t4 = time.time()

    N2 = np.zeros(A + 2, dtype=np.int64)
    N2[1:] = np.cumsum(M2[1:])
    N3 = np.zeros(Jmax + 1, dtype=np.int64)
    N3[1:] = np.cumsum(M3[1:])
    N5 = np.zeros(Kmax + 1, dtype=np.int64)
    N5[1:] = np.cumsum(M5[1:])

    e = [0] * (A + 1)
    for a in range(A + 1):
        n1 = int(N2[a + 1])
        NY = int(N3[B[a] + 1]) if B[a + 1] > B[a] else n1
        NZ = int(N5[C[a] + 1]) if C[a + 1] > C[a] else n1
        NW = NY if NY < NZ else NZ
        e[a] = n1 + 2 * NY + 4 * NZ + 8 * NW - 15 * int(N2[a])
    t5 = time.time()

    diag = dict(A=A, t_radix=t1 - t0, t_M2=t2 - t1, t_M3=t3 - t2, t_M5=t4 - t3,
                t_e=t5 - t4, t_total=t5 - t0,
                min_dist=sw.min_dist, n_elts=int(sw.n_elts),
                n_flagged=int(sw.n_flag), n_repaired=int(sw.n_fix),
                Jmax=Jmax, Kmax=Kmax)
    if verbose:
        print(json.dumps(diag, indent=1))
    return dict(B=B, C=C, b=b, e=e, N2=N2, N3=N3, N5=N5, diag=diag)


# ------------------------------------------------------------ ground truth
def e_direct(a):
    """Brute-force e_a by enumerating the smooth numbers in [2^a, 2^{a+1})."""
    lo = 1 << a
    hi = 1 << (a + 1)
    p3 = 1
    while p3 * 3 <= lo:
        p3 *= 3
    p5 = 1
    while p5 * 5 <= lo:
        p5 *= 5
    t3 = p3 * 3
    t5 = p5 * 5
    tot = 0
    g = 1
    while g < hi:
        gg = g
        while gg < hi:
            h = gg
            while h < lo:
                h <<= 1
            tot += 15 // ((3 if h >= t3 else 1) * (5 if h >= t5 else 1))
            gg *= 5
        g *= 3
    return tot


def N_direct(x):
    """#{2,3,5-smooth h < x} by enumeration (small x only)."""
    c = 0
    g = 1
    while g < x:
        gg = g
        while gg < x:
            h = gg
            while h < x:
                c += 1
                h <<= 1
            gg *= 5
        g *= 3
    return c


def Q_exp(a, B, C):
    return (a, B[a], C[a])


def Q_of(a, B, C):
    return (1 << a) * 3 ** B[a] * 5 ** C[a]


# ------------------------------------------------------------- windows
def window(a, L, e, b):
    """(P, Ehat) with Y_{a+L} = P*Y_a - Ehat, exact ints."""
    P = 1
    E = 0
    for t in range(L):
        bb = b[a + t]
        E = bb * (E + e[a + t])
        P = bb * P
    return P, E


def W_width(a):
    """Disk-proved width bound  X_a <= a^2 + 6a + 11."""
    return a * a + 6 * a + 11
