"""Erdos 1049: the cyclotomic endpoint obstruction, and the accelerated-series audit.

Receipt for two results in the #1049 note (landed in PR #50 on
wcook04/plectis-lean-erdos249-257):

  PROPOSITION 3.6 (check 3 below).  For coprime a > b >= 1 the homogenised
  cyclotomic value Phi_m(a,b) = b^{phi(m)} Phi_m(a/b) is coprime to a*b, because
  Phi_m is monic with constant term +-1 and Theorem 3.1 (endpoint residues) then
  applies with W = phi(m).  At (3,2) every homogenised cyclotomic value is a
  6-unit.  Consequence: the denominator reductions that work at integer bases --
  Rhin-Viola factorial cosets, Zudilin's order-twelve cyclotomic divisor --
  supply NO 2- or 3-primary gain when transported through the homogenisation,
  whatever their size.  They can still reduce Archimedean height as large odd
  divisors; that is a different account of the same product formula.

  THE ACCELERATED SERIES ARE NOT APPROXIMANT FAMILIES (checks 1 and 2).  The two
  identities printed after Theorems 1 and 2 of Amdeberhan-Zeilberger are
  arithmetically negative even at INTEGER q, before rational-base clearing:
      A:  D = 1/2 + 3/pi^2  = 0.80396,  G = -0.30396 < 0
      B:  D = 1/2 + 12/pi^2 = 1.71585,  G = -0.21585 < 0
  The exact reduced common denominators are (q)_N prod_{d<=N} Phi_d and
  (q)_N prod_{d<=2N} Phi_d respectively; both closed forms are checked against
  the true lcm.  At most these identities are kernels for a further telescoping,
  Pade or Hankel transformation -- they are not truncation families.

Sibling of verify_qapery_rational_endpoint.py (the q-Apery rows at 3/2) and
verify_qapery_transduction.py (the source recurrence).  Exact integer arithmetic
throughout.  Exit 0 iff every check passes.
"""

from fractions import Fraction
from math import gcd, pi, log
import sys

# ---------- dense Z[q] ----------

def trim(p):
    while len(p) > 1 and p[-1] == 0:
        p.pop()
    return p

def padd(a, b):
    n = max(len(a), len(b))
    return trim([(a[i] if i < len(a) else 0) + (b[i] if i < len(b) else 0) for i in range(n)])

def psub(a, b):
    n = max(len(a), len(b))
    return trim([(a[i] if i < len(a) else 0) - (b[i] if i < len(b) else 0) for i in range(n)])

def pmul(a, b):
    if a == [0] or b == [0]:
        return [0]
    out = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        if x:
            for j, y in enumerate(b):
                if y:
                    out[i + j] += x * y
    return trim(out)

def pshift(a, k):
    return [0] * k + list(a) if a != [0] else [0]

def pdeg(a):
    return len(trim(list(a))) - 1

def pdivmod(a, b):
    """exact division in Z[q] assuming b monic-ish; returns (quotient, remainder)."""
    a = list(a); q = [0] * max(1, len(a) - len(b) + 1)
    db, lb = pdeg(b), b[pdeg(b)]
    while pdeg(a) >= db and a != [0]:
        d = pdeg(a) - db
        c = Fraction(a[pdeg(a)], lb)
        q[d] = c
        a = psub(a, [int(x) if isinstance(x, int) else x for x in pmul(pshift(b, d), [c])])
        a = trim([Fraction(x) for x in a])
        if all(x == 0 for x in a):
            a = [0]; break
    return q, a

# ---------- cyclotomic polynomials over Z ----------

_cyc = {}

def cyclotomic(m):
    """Phi_m(q) by dividing q^m - 1 by the product of Phi_d for proper divisors d."""
    if m in _cyc:
        return _cyc[m]
    num = psub(pshift([1], m), [1])              # q^m - 1
    den = [1]
    for d in range(1, m):
        if m % d == 0:
            den = pmul(den, cyclotomic(d))
    # exact polynomial division (den divides num over Z)
    quo = [0] * (pdeg(num) - pdeg(den) + 1)
    rem = list(num)
    while pdeg(rem) >= pdeg(den) and rem != [0]:
        d = pdeg(rem) - pdeg(den)
        c = rem[pdeg(rem)] // den[pdeg(den)]
        quo[d] = c
        rem = psub(rem, pshift([c * x for x in den], d))
    assert rem == [0], f"Phi_{m} division left remainder"
    _cyc[m] = trim(quo)
    return _cyc[m]

def qpoch(n):
    out = [1]
    for j in range(1, n + 1):
        out = pmul(out, psub([1], pshift([1], j)))
    return out

def qbin(n, k, cache={}):
    if k < 0 or k > n:
        return [0]
    if k in (0, n):
        return [1]
    if (n, k) in cache:
        return cache[(n, k)]
    cache[(n, k)] = padd(qbin(n - 1, k - 1), pshift(qbin(n - 1, k), k))
    return cache[(n, k)]

# ---------- claim 1 & 2: exact common denominators of the accelerated truncations ----------

def phi_exponent_in(poly_factors, d):
    return poly_factors.get(d, 0)

def denom_A(n):
    """(1-q^n)(q)_n as a multiset of cyclotomic exponents."""
    e = {}
    for j in range(1, n + 1):                    # (q)_n = prod (1-q^j)
        for d in range(1, j + 1):
            if j % d == 0:
                e[d] = e.get(d, 0) + 1
    for d in range(1, n + 1):                    # (1-q^n)
        if n % d == 0:
            e[d] = e.get(d, 0) + 1
    return e

def denom_B(n):
    """(q^n-1) (q)_{2n} / (q)_n."""
    e = {}
    for j in range(1, 2 * n + 1):
        for d in range(1, j + 1):
            if j % d == 0:
                e[d] = e.get(d, 0) + 1
    for j in range(1, n + 1):
        for d in range(1, j + 1):
            if j % d == 0:
                e[d] = e.get(d, 0) - 1
    for d in range(1, n + 1):
        if n % d == 0:
            e[d] = e.get(d, 0) + 1
    return e

def lcm_exponents(fn, N):
    out = {}
    for n in range(1, N + 1):
        for d, v in fn(n).items():
            if v > out.get(d, 0):
                out[d] = v
    return out

def deg_from_exponents(e):
    return sum(v * pdeg(cyclotomic(d)) for d, v in e.items() if v > 0)


def check_accelerated():
    print("=" * 78)
    print("CLAIMS 1 & 2: exact common denominators of the accelerated truncations")
    print("=" * 78)
    print(f"{'N':>3} | {'deg lcm A':>10} {'claimed A':>10} | {'deg lcm B':>10} {'claimed B':>10}")
    okA = okB = True
    for N in (4, 6, 8, 10, 12, 16, 20, 28, 40):
        eA = lcm_exponents(denom_A, N)
        eB = lcm_exponents(denom_B, N)
        dA, dB = deg_from_exponents(eA), deg_from_exponents(eB)
        # claimed closed forms: (q)_N * prod_{d<=N} Phi_d   and   (q)_N * prod_{d<=2N} Phi_d
        clA = N * (N + 1) // 2 + sum(pdeg(cyclotomic(d)) for d in range(1, N + 1))
        clB = N * (N + 1) // 2 + sum(pdeg(cyclotomic(d)) for d in range(1, 2 * N + 1))
        okA &= (dA == clA); okB &= (dB == clB)
        print(f"{N:>3} | {dA:>10} {clA:>10} | {dB:>10} {clB:>10}")
    print(f"\n  claimed closed form for A exact: {'YES' if okA else 'NO'}")
    print(f"  claimed closed form for B exact: {'YES' if okB else 'NO'}")

    print("\n  asymptotic rates (deg / N^2), claimed limits:")
    print(f"{'N':>5} {'A rate':>10} {'B rate':>10}")
    for N in (40, 80, 160, 320):
        eA = lcm_exponents(denom_A, N); eB = lcm_exponents(denom_B, N)
        print(f"{N:>5} {deg_from_exponents(eA)/N**2:>10.5f} {deg_from_exponents(eB)/N**2:>10.5f}")
    DA, DB = 0.5 + 3 / pi**2, 0.5 + 12 / pi**2
    print(f"{'limit':>5} {DA:>10.5f} {DB:>10.5f}   <- 1/2+3/pi^2 and 1/2+12/pi^2")
    GA, GB = -3 / pi**2, 1 - 12 / pi**2
    print(f"\n  G_A = 1/2 - D_A = {0.5 - DA:+.6f}  (claimed {GA:+.6f})   negative -> route dead")
    print(f"  G_B = 3/2 - D_B = {1.5 - DB:+.6f}  (claimed {GB:+.6f})   negative -> route dead")
    return okA, okB


# ---------- claim 3: homogenised cyclotomic values are 6-units ----------

def H(P, W, a, b):
    return sum(P[i] * a**i * b**(W - i) for i in range(len(P)))

def check_cyclotomic_units():
    print()
    print("=" * 78)
    print("CLAIM 3: Phi_m(a,b) = b^{phi(m)} Phi_m(a/b) is coprime to a*b   [(a,b)=(3,2)]")
    print("=" * 78)
    bad = []
    for m in range(1, 61):
        P = cyclotomic(m)
        W = pdeg(P)
        h = H(P, W, 3, 2)
        g = gcd(abs(h), 6)
        if g != 1:
            bad.append((m, h, g))
    print(f"  m = 1..60 checked; gcd(Phi_m(3,2), 6) != 1 for: {bad if bad else 'NONE'}")
    # also check other coprime bases to confirm the general statement
    print("  general (a,b) spot-check, m = 1..30:")
    for (a, b) in [(3, 2), (5, 2), (5, 3), (7, 4), (9, 2), (7, 2)]:
        viol = [m for m in range(1, 31)
                if gcd(abs(H(cyclotomic(m), pdeg(cyclotomic(m)), a, b)), a * b) != 1]
        print(f"    (a,b)=({a},{b}): violations {viol if viol else 'none'}")
    # the reason, made explicit
    print("\n  reason: Phi_m is monic and Phi_m(0) = +-1, so mod p|b only the top term")
    print("  survives and mod p|a only the constant term does -- the same endpoint")
    print("  argument as Theorem 3.1 of the #1049 note, applied to Phi_m.")
    return not bad


if __name__ == "__main__":
    a, b = check_accelerated()
    c = check_cyclotomic_units()
    print("\n" + "=" * 78)
    print(f"SUMMARY  claim1_A={a}  claim2_B={b}  claim3_cyclotomic={c}")
    print("=" * 78)
    sys.exit(0 if (a and b and c) else 1)
