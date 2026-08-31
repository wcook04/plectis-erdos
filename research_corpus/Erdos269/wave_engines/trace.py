"""The wave-4 Euclid/Ostrowski mod-2 trace, re-implemented standalone (renorm.py
has top-level side effects).  Identical algorithm; re-verified in selfcheck.py."""


def trace_parity(n, m, a, b, trace=None):
    """parity of sum_{i<n} floor((a i + b)/m); records the (n_t, q_t, d_t) trace."""
    par = 0
    steps = 0
    while True:
        steps += 1
        q = d = 0
        if a >= m:
            q = a // m
            par ^= ((n - 1) * n // 2) & 1 & q
            a %= m
        if b >= m:
            d = b // m
            par ^= (n & 1) & (d & 1)
            b %= m
        if trace is not None:
            trace.append((n & 3, q & 1, d & 1,
                          (((n - 1) * n // 2) & 1 & q) ^ ((n & 1) & (d & 1))))
        y = a * n + b
        if y < m:
            break
        n = y // m
        b = y % m
        m, a = a, m
    return par, steps


def T_parity_renorm(A, cert, trace=None):
    """T(A) mod 2 via the renormalized trace, using the certified rational model."""
    fa, fb = cert.ahi, cert.bhi
    p, q = fa.numerator, fa.denominator
    r, s = fb.numerator, fb.denominator
    P, R, M = p * s, r * q, A * q * s
    Jm = (M - 1) // P
    b0 = (M - 1) % P
    par, steps = trace_parity(Jm + 1, R, P, b0, trace)
    return ((Jm + 1) + par) & 1, steps
