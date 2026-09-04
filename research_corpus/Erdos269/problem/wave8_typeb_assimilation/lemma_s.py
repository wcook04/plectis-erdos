"""Wave-8 probe: is sliver-emptiness elementary (no Baker/Matveev)?

Lemma S (note s12):  s(A+n) = C_p(A) + s(A) + Sigma^+ - Sigma^-,
the slivers being the two width-|delta| log2-intervals abutting 2^A and 2^(A+1),
delta = p*alpha - n.

ELEMENTARY CLAIM (Return 5, sharpened here): every 3^u 5^v is an integer != 2^A,
so |3^u5^v - 2^A| >= 1, hence |log2(3^u5^v) - A| >= log2(1 + 2^-A).
Therefore BOTH slivers are empty as soon as |delta| <= log2(1 + 2^-(A+1)).
No linear form in logarithms is involved.
"""
from fractions import Fraction
from decimal import Decimal, getcontext
import exact

getcontext().prec = 1200


def sep_lower(A):
    """Rational LOWER bound for log2(1 + 2^-(A+1)) = the binding separation."""
    v = (Decimal(1) + Decimal(2) ** (-(A + 1))).ln() / Decimal(2).ln()
    p = 400
    scaled = (v * Decimal(10) ** p).to_integral_value(rounding='ROUND_FLOOR')
    return Fraction(int(scaled), 10 ** p)


def delta_upper(p, n):
    """Rational UPPER bound for |p*alpha - n|."""
    lo, hi = p * exact.ALPHA_LO - n, p * exact.ALPHA_HI - n
    return max(abs(lo), abs(hi))


conv = exact.convergents(exact.ALPHA_LO, exact.ALPHA_HI, 1200)
print("r      p_digits  window A_max  tested  LemmaS_exact_failures")
tot_checked = tot_fail = 0
for r in [4, 9, 19, 39, 59, 79, 99, 124, 149, 183, 249]:
    n, p = conv[r]
    du = delta_upper(p, n)
    A_max = -1
    while A_max < 60 and du <= sep_lower(A_max + 1):
        A_max += 1
    checked = fails = 0
    for A in range(0, min(A_max, 14) + 1):
        lhs = exact.s(A + n)
        rhs = exact.C_p(p, A, n) + exact.s(A)
        assert lhs is not None and rhs is not None
        checked += 1
        if lhs != rhs:
            fails += 1
            print("   FAIL r=%d A=%d  s(A+n)=%d  C_p+s(A)=%d" % (r, A, lhs, rhs))
    tot_checked += checked
    tot_fail += fails
    print("%-6d %-9d %-13d %-7d %d" % (r, len(str(p)), A_max, checked, fails))
print("\nTOTAL: %d exact Lemma-S instances in the elementary window, %d failures"
      % (tot_checked, tot_fail))
