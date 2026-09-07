"""Erdos 1049: what the Amdeberhan-Zeilberger q-Apery construction does at q = 3/2.

Zeilberger replied to the #1049 outreach asking whether the work is related to
"q-Apery Irrationality Proofs by q-WZ Pairs" (arXiv math/9804122; annexed at
annexes/arxiv-math9804122-amdeberhan-zeilberger-q-apery, source.pdf sha256
339a4324a6cd0bcfd8eb872d0a408140fcba06ee383bf421248a91919b1430e2).

It is related: h_q(1) = sum_{k>=1} 1/(q^k - 1) is exactly F(t) = sum 1/(t^n - 1) at
t = q.  This script settles what happens when the construction is taken to the
rational base 3/2 that #1049 is about.  Sibling of verify_qapery_transduction.py,
which checks the source recurrence; this one checks the ARITHMETIC at the endpoint.

Four checks, all exact (integer / Fraction arithmetic, no floats in the proofs):

  A  exact degrees.  The k-th summand of b(n) has q-degree 2nk - (k^2-k)/2, whose
     forward difference 2n-k is strictly positive for 0 <= k < n.  So k = n is the
     UNIQUE top-degree summand; deg b(n) = (3n^2+n)/2, LC = (-1)^n, b(n)(0) = 1.

  B  exact clearing width.  deg z_n = (19n^2+22n+8)/8 (n even), (19n^2+24n+5)/8
     (n odd).  So D = 19/8 is exact, not the paper's O-bound.  LC(z_n) = +-1 and
     z_n(0) = 1.

  C  endpoint units.  By Theorem 3.1 of the #1049 note (endpoint residues at (3,2)),
     unit top and constant endpoints force H_W(z_n) = 2^W z_n(3/2) to be odd and
     nonzero mod 3.  Hence gcd(H_W(z_n), 6) = 1 and the reduced denominator of
     z_n(3/2) is EXACTLY 2^{deg z_n}: there is no hidden scalar 2-adic or 3-adic
     cancellation in the published denominator coordinate.  This replaces a planned
     numerical v_2 sweep with a proof.

  D  measured margin.  Evaluate the cleared rows directly against F(3/2), bracketed
     to 1300 bits, and measure log|rho_n|/n^2 for the cleared integer linear form.
     It is POSITIVE and converging to D log 2 - G log(3/2) = +1.393: the forms
     diverge.  Nothing here relies on a transfer principle or an O-bound.

Scope.  C covers z_n only.  The numerator coordinate, cross-row / Casoratian
divisibility, cyclotomic or permutation-group reduction, deformed mollifiers, the two
accelerated series printed after Theorems 1 and 2, and non-linear-form routes are all
untouched.  Nothing here proves or disproves irrationality of F(3/2); #1049 is open.

Run:  ./repo-python formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1049/\
scripts/verify_qapery_rational_endpoint.py
Exit 0 iff every check passes.
"""

from fractions import Fraction
from math import gcd, log
import sys

Q = Fraction(3, 2)


# ---------- dense polynomials over Z[q], little-endian ----------

def _trim(p):
    while len(p) > 1 and p[-1] == 0:
        p.pop()
    return p


def padd(a, b):
    n = max(len(a), len(b))
    return _trim([(a[i] if i < len(a) else 0) + (b[i] if i < len(b) else 0) for i in range(n)])


def psub(a, b):
    n = max(len(a), len(b))
    return _trim([(a[i] if i < len(a) else 0) - (b[i] if i < len(b) else 0) for i in range(n)])


def pmul(a, b):
    if a == [0] or b == [0]:
        return [0]
    out = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        if x:
            for j, y in enumerate(b):
                if y:
                    out[i + j] += x * y
    return _trim(out)


def pshift(a, k):
    return [0] * k + list(a) if a != [0] else [0]


def pdeg(a):
    return len(_trim(list(a))) - 1


# ---------- q-objects ----------

_qbin = {}


def qbin(n, k):
    """[n choose k]_q by q-Pascal: [n,k] = [n-1,k-1] + q^k [n-1,k]."""
    if k < 0 or k > n:
        return [0]
    if k in (0, n):
        return [1]
    if (n, k) in _qbin:
        return _qbin[(n, k)]
    _qbin[(n, k)] = padd(qbin(n - 1, k - 1), pshift(qbin(n - 1, k), k))
    return _qbin[(n, k)]


def qpoch(n):
    out = [1]
    for j in range(1, n + 1):
        out = pmul(out, psub([1], pshift([1], j)))
    return out


def tail_product(n):
    """prod_{s=[n/2]}^{n} (1-q^s); degenerate for n < 2 where s = 0 gives the zero factor."""
    out = [1]
    for s in range(n // 2, n + 1):
        out = pmul(out, psub([1], pshift([1], s)))
    return out


def b_term(n, k):
    """b(n,k) = (-1)^k q^{k(k+1)/2} [n+k,k]_q [n,k]_q   (section 1.3)"""
    t = pmul(qbin(n + k, k), qbin(n, k))
    t = pshift(t, k * (k + 1) // 2)
    return _trim([c * (-1) ** k for c in t])


def B(n):
    out = [0]
    for k in range(n + 1):
        out = padd(out, b_term(n, k))
    return out


def Z(n):
    return pmul(pmul(B(n), qpoch(n + 1)), tail_product(n))


def deg_Z_closed(n):
    return (19 * n * n + 22 * n + 8) // 8 if n % 2 == 0 else (19 * n * n + 24 * n + 5) // 8


def H(P, W):
    """Homogeneous endpoint evaluation of the #1049 note, section 3: H_W(P) = 2^W P(3/2)."""
    return sum(P[i] * 3 ** i * 2 ** (W - i) for i in range(len(P)))


# ---------- rational-endpoint evaluation ----------

_qb_at = {}


def qbin_at(n, k):
    if k < 0 or k > n:
        return Fraction(0)
    if k in (0, n):
        return Fraction(1)
    if (n, k) in _qb_at:
        return _qb_at[(n, k)]
    _qb_at[(n, k)] = qbin_at(n - 1, k - 1) + Q ** k * qbin_at(n - 1, k)
    return _qb_at[(n, k)]


def qpoch_at(n):
    v = Fraction(1)
    for j in range(1, n + 1):
        v *= (1 - Q ** j)
    return v


def rows_at(n):
    """(u_n(3/2), z_n(3/2)) from sections 1.2, 1.3, 1.4, 1.7."""
    clear = qpoch_at(n + 1)
    for s in range(n // 2, n + 1):
        clear *= (1 - Q ** s)
    s1 = sum(Q ** m / ((1 - Q ** m) * qpoch_at(m)) for m in range(1, n + 1))
    bn = an = Fraction(0)
    for k in range(n + 1):
        bk = (-1) ** k * Q ** (k * (k + 1) // 2) * qbin_at(n + k, k) * qbin_at(n, k)
        s2 = sum(Fraction(1) / (Q ** m - 1) / (qbin_at(n + m, m) * qpoch_at(n))
                 for m in range(1, k + 1))
        bn += bk
        an += (s1 + s2) * bk
    return an * clear, bn * clear


def F_bracket(bits=1300):
    """(lo, hi) for F(3/2) = sum_{k>=1} 2^k/(3^k - 2^k), in scaled integer arithmetic."""
    S = 1 << bits
    total, k = 0, 1
    while S * 2 ** k >= 3 ** k - 2 ** k:
        total += (S * 2 ** k) // (3 ** k - 2 ** k)
        k += 1
    lo = Fraction(total, S)
    return lo, lo + Fraction(k, S) + Fraction(3 * 2 ** k, 3 ** k - 2 ** k), k - 1


def v2_den(fr):
    d, e = fr.denominator, 0
    while d % 2 == 0:
        d //= 2
        e += 1
    return e, d          # (2-adic width, odd part)


# ---------- section 1.5, corrected against the authors' arXiv LaTeX ----------
# See the correction block in the annex extracted.md: y_0 reads q(alpha-1)(q alpha+2),
# and y_1's linear term is (q^2-4q+1) alpha.  Both matter; either alone leaves a residual.

def _alpha(n):
    return pshift([1], n + 1)


def _apow(n, e):
    out = [1]
    for _ in range(e):
        out = pmul(out, _alpha(n))
    return out


def y0(n):
    a = _alpha(n)
    return pmul([0, 1], pmul(psub(a, [1]), padd(pshift(a, 1), [2])))


def y2(n):
    a = _alpha(n)
    return pmul(psub(pshift(a, 1), [1]), padd(a, [2]))


def y1(n):
    t = pshift(_apow(n, 5), 3)
    t = padd(t, pmul(pshift([2, 2], 2), _apow(n, 4)))
    t = padd(t, pshift(_apow(n, 3), 2))
    t = psub(t, pmul(pshift([4, 4], 1), _apow(n, 2)))
    t = padd(t, pmul([1, -4, 1], _alpha(n)))
    return padd(t, [2, 2])


def main(nmax=12):
    ok = {}

    print("A/B  exact degrees, leading coefficients, constant terms")
    print(f"{'n':>3} {'deg b(n)':>9} {'(3n^2+n)/2':>11} {'LC':>4} {'b(0)':>5}"
          f" {'deg z_n':>8} {'closed':>7} {'LC':>4} {'z(0)':>5}")
    a = b = True
    for n in range(2, nmax + 1):
        Bn, Zn = B(n), Z(n)
        a &= (pdeg(Bn) == (3 * n * n + n) // 2 and Bn[-1] == (-1) ** n and Bn[0] == 1)
        b &= (pdeg(Zn) == deg_Z_closed(n) and abs(Zn[-1]) == 1 and Zn[0] == 1)
        print(f"{n:>3} {pdeg(Bn):>9} {(3*n*n+n)//2:>11} {Bn[-1]:>4} {Bn[0]:>5}"
              f" {pdeg(Zn):>8} {deg_Z_closed(n):>7} {Zn[-1]:>4} {Zn[0]:>5}")
    ok["A_exact_degree"], ok["B_exact_width"] = a, b

    print("\nC  endpoint residues at (3,2): gcd(H_W(z_n), 6) and den z_n(3/2)")
    print(f"{'n':>3} {'W':>6} {'H mod 2':>8} {'H mod 3':>8} {'gcd(H,6)':>9} {'den == 2^W':>11}")
    c = True
    for n in range(2, nmax + 1):
        Zn = Z(n)
        W = pdeg(Zn)
        h = H(Zn, W)
        _, zval = rows_at(n)
        c &= (gcd(h, 6) == 1 and zval.denominator == 2 ** W)
        print(f"{n:>3} {W:>6} {h % 2:>8} {h % 3:>8} {gcd(h, 6):>9}"
              f" {str(zval.denominator == 2 ** W):>11}")
    ok["C_endpoint_unit"] = c

    print("\nD  the actual linear form at 3/2")
    lo, hi, terms = F_bracket()
    print(f"   F(3/2) bracketed with {terms} terms, width < 2^-1300")
    print(f"{'n':>3} {'odd den u':>10} {'odd den z':>10} {'W':>6}"
          f" {'log|l_n|/n^2':>14} {'log|rho_n|/n^2':>16}")
    d = True
    last = None
    for n in range(2, nmax + 1):
        U, Zv = rows_at(n)
        wU, oddU = v2_den(U)
        wZ, oddZ = v2_den(Zv)
        W = max(wU, wZ)
        mid = ((Zv * lo - U) + (Zv * hi - U)) / 2
        lm = log(abs(float(mid))) / (n * n)
        rm = log(abs(float(mid * 2 ** W))) / (n * n)
        d &= (oddU == 1 and oddZ == 1 and rm > 0)
        last = rm
        print(f"{n:>3} {oddU:>10} {oddZ:>10} {W:>6} {lm:>14.6f} {rm:>16.6f}")
    predicted = 2.375 * log(2) - 0.625 * log(1.5)
    print(f"   predicted limit  D log2 - G log(3/2) = {predicted:+.6f};"
          f"  observed at n={nmax}: {last:+.6f}")
    print("   cleared integer linear forms DIVERGE -> this family does not reach 3/2")
    ok["D_margin_positive"] = d

    print("\nE  section 1.5 recurrence (LaTeX-corrected coefficients) annihilates b(n)")
    e = True
    for n in range(0, 7):
        r = padd(padd(pmul(y2(n), B(n + 2)), pmul(y1(n), B(n + 1))), pmul(y0(n), B(n)))
        e &= (r == [0])
        print(f"   n={n}: {'0' if r == [0] else f'NONZERO deg {pdeg(r)}'}")
    ok["E_recurrence"] = e

    print("\n" + "=" * 60)
    for k, v in ok.items():
        print(f"  {k:<22} {'PASS' if v else 'FAIL'}")
    print("=" * 60)
    return 0 if all(ok.values()) else 1


if __name__ == "__main__":
    sys.exit(main())
