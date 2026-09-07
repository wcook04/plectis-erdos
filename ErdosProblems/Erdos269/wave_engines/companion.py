"""Wave-5: the MULTIPLICATIVE companion identity for the shell parity.

alpha = log_2 3, beta = log_2 5, L(u,v) = u*alpha + v*beta.
  s(A) = #{(u,v) in Z^2_{>=0} : A <= L(u,v) < A+1}   (= T(A+1) - T(A))
Pick (p,q) in Z^2, delta = p*alpha + q*beta - 1 = log_2( 3^p 5^q / 2 ).
The lattice translation (u,v) -> (u-p, v-q) carries the strip [A+1,A+2) onto
[A-delta, A+1-delta).  With S = {L in [A,A+1)}, S* = {L in [A-delta,A+1-delta)},
Q0 = {u>=0,v>=0}, Q1 = {u>=-p, v>=-q}:

    s(A+1) = #(S* cap Q1)
    s(A+1) - s(A) = C_bdry(A) + C_slv(A)
    C_bdry(A) = #(S* cap Q1\\Q0) - #(S* cap Q0\\Q1)      (|.| <= |p| + |q|)
    C_slv(A)  = #(S* cap Q0) - #(S cap Q0)

All arithmetic is exact integer arithmetic (cross-multiplication), no logs in any
decision; mpmath is used only to seed integer search windows that are then verified.
"""
import mpmath as mp

mp.mp.dps = 150
AL = mp.log(3, 2)
BE = mp.log(5, 2)


def floor_log2_ratio(n, d):
    """floor(log2(n/d)), n,d positive ints.  Exact."""
    k = n.bit_length() - d.bit_length()
    ge = lambda kk: (d << kk) <= n if kk >= 0 else d <= (n << (-kk))
    while not ge(k):
        k -= 1
    while ge(k + 1):
        k += 1
    return k


def ratio(u, v):
    """3^u 5^v as exact (num, den)."""
    n = (3 ** u if u >= 0 else 1) * (5 ** v if v >= 0 else 1)
    d = (3 ** (-u) if u < 0 else 1) * (5 ** (-v) if v < 0 else 1)
    return n, d


def level(u, v):
    return floor_log2_ratio(*ratio(u, v))


# ------------------------------------------------------------------ delta search
def best_pq(pmax):
    """(|delta|, p, q) for q = argmin over the integers, p = 1..pmax; sorted."""
    out = []
    for p in range(1, pmax + 1):
        q = int(mp.nint((1 - p * AL) / BE))
        d = p * AL + q * BE - 1
        out.append((abs(d), p, q, d))
    out.sort()
    return out


# ------------------------------------------------------------- lattice inventory
def inventory(Amax):
    """buckets[b] = list of exact values 3^u5^v (u,v>=0) with floor(L)=b, b<=Amax."""
    buckets = [[] for _ in range(Amax + 3)]
    p3 = 1
    while p3.bit_length() - 1 <= Amax:
        w = p3
        while w.bit_length() - 1 <= Amax:
            buckets[w.bit_length() - 1].append(w)
            w *= 5
        p3 *= 3
    return buckets


# --------------------------------------------------------------------- the pieces
def count_Sstar_Q0(A, buckets, Fn, Fd):
    """#(S* cap Q0) = #{(u,v)>=0 : floor(L(u,v)+1+delta) == A+1}, exact.
    |delta| < 1 forces those points into buckets A-1, A, A+1."""
    n = 0
    for b in (A - 1, A, A + 1):
        if b < 0 or b >= len(buckets):
            continue
        for V in buckets[b]:
            if floor_log2_ratio(V * Fn, Fd) == A + 1:
                n += 1
    return n


def strip_pts(A, i_lo, i_hi, w_lo, axis):
    """(i,w) with level(i,w)==A, in a bounded band; axis='i' bands i, 'w' bands w."""
    out = []
    if axis == 'i':
        for i in range(i_lo, i_hi):
            w0 = int(mp.floor((A - i * AL) / BE))
            for w in range(max(w_lo, w0 - 2), w0 + 3):
                if level(i, w) == A:
                    out.append((i, w))
    else:
        for w in range(i_lo, i_hi):
            u0 = int(mp.floor((A - w * BE) / AL))
            for i in range(max(w_lo, u0 - 2), u0 + 3):
                if level(i, w) == A:
                    out.append((i, w))
    return out


def C_bdry(A, p, q):
    """#(S* cap Q1\\Q0) - #(S* cap Q0\\Q1), exact.  In (i,w) = (u+p, v+q):
       Q1 -> {i>=0, w>=0},  Q0 -> {i>=p, w>=q},  S* -> {level(i,w) == A+1}.
       Any point where the two memberships differ has i in [min(0,p),max(0,p))
       or w in [min(0,q),max(0,q)), so a bounded band search is complete."""
    cand = set(strip_pts(A + 1, min(0, p), max(0, p), min(0, q), 'i'))
    cand |= set(strip_pts(A + 1, min(0, q), max(0, q), min(0, p), 'w'))
    plus = minus = 0
    for (i, w) in cand:
        inQ1 = (i >= 0 and w >= 0)
        inQ0 = (i >= p and w >= q)
        if inQ1 and not inQ0:
            plus += 1
        elif inQ0 and not inQ1:
            minus += 1
    return plus - minus
