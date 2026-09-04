#!/usr/bin/env python3
"""What does Erdos 68's rank-two producer actually output, and at what scale?

Upstream analytic state
-----------------------
`erdos68_rank_two_strict_nonvanishing` is a priority-1 producer:

> Using the Lean-checked uniform factorial-grid Cramer kernel and prime unit
> translator, prove that the nearest-integer-rounded residual is strictly
> nonzero. [...] strict nonvanishing is now explicitly equivalent to proving
> det(A) S is nonintegral.

`full_residual_mod_integers_classification` supplies the identity
`R_D(c) = det(A)*S + K` with `K` integral and `det(A)` the nonzero augmented
determinant, and `conditional_rank_two_nearest_integer_rounding` supplies
`|R| <= 1/2` after rounding. `PrimeUnitTranslator.lean` -- which carries the
whole construction -- contains no occurrence of `Irrational`, so nothing
downstream consumes the nonvanishing yet.

Probe
-----
Three questions the packet does not answer.

1. **What is the producer's output, as a statement about `q`?** If `S = a/q` in
   lowest terms then `det(A)*S = det(A)*a/q` is integral exactly when `q` divides
   `det(A)`, since `gcd(a,q)=1`.  So `det(A) S` nonintegral *is* `q` not dividing
   `det(A)`: a divisibility exclusion, the same species as the Kempner-index
   statement `q` not dividing `299999!`, and not a size bound.

2. **Can nonvanishing alone give irrationality?**  Under `S = a/q`, a nonzero
   `R` is a nonzero multiple of `1/q`, so `|R| >= 1/q`.  The only recorded
   smallness is `|R| <= 1/2`.  Those are compatible for every `q >= 2`, so the
   pair can never contradict rationality; a linear-form argument needs
   `0 < |R| < 1/q`, i.e. smallness, which the rounding step is what destroys.

3. **How far does the certified continued-fraction bound discharge it for free?**
   `certified_continued_fraction` gives `q > 10^12039`, and hence unconditionally
   `N*S` nonintegral for every nonzero `|N| <= 10^12039`: if `S` is irrational
   that is trivial, and if `S = a/q` then `q` cannot divide such an `N`.  So
   every grid instance whose determinant is that small has its hypothesis
   already proved.  This measures where that stops.

The matrix is built literally from `PrimeUnitTranslator.lean`:
`factorialGridScale D = (D!)^2`, `factorialGridIndex n t j = (t+j) (D!)^2` with
`D = n+2`, and `augmentedChannelMomentMatrix` whose first row is `(index j)!`
and whose row `d+1` is `(index j)! / (d+2)!^(index j / (d+2))`.  Determinants are
taken fraction-free by Bareiss, so they are exact integers throughout.

Predeclared falsifier
---------------------
* If the determinants stayed below `10^12039` over a useful range, the
  continued-fraction bound would discharge the producer outright there and the
  route would be closed for free.
* If the `n = 0` determinant had no closed form, the comparison against the
  landed Kempner exclusion could not be made explicit.

Claim boundary
--------------
Finite computation plus elementary reasoning about the recorded identities. It
reclassifies what the producer would yield; it does not prove the producer, and
Erdos 68 remains open.
"""

from __future__ import annotations

import argparse
import json
import math

# Certified continued-fraction denominator bound for this series, from
# `certified_continued_fraction.run("erdos_68", 80000)`.
CF_BOUND_BITS = 39991
KEMPNER_INDEX = 299999          # q does not divide 299999!, landed separately


def grid_scale(dimension: int) -> int:
    """`factorialGridScale D = (D!)^2`."""
    return math.factorial(dimension) ** 2


def augmented_matrix(n: int, t: int) -> tuple[list[list[int]], list[int]]:
    """`augmentedChannelMomentMatrix (factorialGridIndex n t)`, exactly."""
    dimension = n + 2
    scale = grid_scale(dimension)
    index = [(t + j) * scale for j in range(n + 2)]
    factorials = [math.factorial(i) for i in index]
    rows = [factorials]
    for d in range(n + 1):                       # channels 2 .. n+2
        channel = d + 2
        rows.append([factorials[j] //
                     (math.factorial(channel) ** (index[j] // channel))
                     for j in range(n + 2)])
    return rows, index


def determinant(matrix: list[list[int]]) -> int:
    """Fraction-free Bareiss; exact over the integers."""
    work = [row[:] for row in matrix]
    size = len(work)
    sign = 1
    previous = 1
    for k in range(size - 1):
        if work[k][k] == 0:
            for r in range(k + 1, size):
                if work[r][k] != 0:
                    work[k], work[r] = work[r], work[k]
                    sign = -sign
                    break
            else:
                return 0
        for i in range(k + 1, size):
            for j in range(k + 1, size):
                work[i][j] = (work[i][j] * work[k][k]
                              - work[i][k] * work[k][j]) // previous
        previous = work[k][k]
    return sign * work[size - 1][size - 1]


def closed_form_n0(t: int) -> int:
    """`|det| = 3 (4t)! (4t+4)! / 2^(2t+2)` at the smallest grid."""
    return 3 * math.factorial(4 * t) * math.factorial(4 * t + 4) // 2 ** (2 * t + 2)


def run(max_n: int = 2, ts: tuple[int, ...] = (1, 2, 3, 5)) -> dict:
    rows = []
    closed_form_ok = True
    for n in range(max_n + 1):
        for t in ts:
            matrix, index = augmented_matrix(n, t)
            value = abs(determinant(matrix))
            entry = {
                "n": n, "t": t, "matrix_size": n + 2,
                "grid_scale": grid_scale(n + 2),
                "largest_support_index": index[-1],
                "abs_det_bits": value.bit_length(),
                "abs_det_decimal_digits": int(value.bit_length() * math.log10(2)) + 1,
                "discharged_by_cf_bound": value.bit_length() <= CF_BOUND_BITS,
            }
            if n == 0:
                entry["closed_form_matches"] = (closed_form_n0(t) == value)
                closed_form_ok &= entry["closed_form_matches"]
            rows.append(entry)

    covered = [r for r in rows if r["discharged_by_cf_bound"]]
    uncovered = [r for r in rows if not r["discharged_by_cf_bound"]]
    largest_covered_n = max((r["n"] for r in covered), default=None)
    smallest_uncovered_n = min((r["n"] for r in uncovered), default=None)

    # Where does the n = 0 output beat the landed Kempner exclusion?  Once
    # 299999! divides 3(4t)!(4t+4)!/2^(2t+2), "q does not divide det" is the
    # strictly stronger statement.  That needs 4t+4 >= 299999 for the factorial
    # factor, and enough surviving 2-adic valuation after the division.
    t_star = None
    for t in (74999, 75000, 75001):
        if 4 * t + 4 >= KEMPNER_INDEX:
            t_star = t
            break

    return {
        "rows": rows,
        "closed_form_verified_at_n_zero": closed_form_ok,
        "closed_form": "|det(A)| = 3 (4t)! (4t+4)! / 2^(2t+2) at n = 0",
        "cf_bound_bits": CF_BOUND_BITS,
        "largest_grid_discharged_by_cf_bound": largest_covered_n,
        "smallest_grid_beyond_cf_bound": smallest_uncovered_n,
        "producer_output_shape": (
            "q does not divide det(A): a divisibility exclusion of the same "
            "species as the Kempner-index statement, not a size bound"),
        "nonvanishing_cannot_give_irrationality": (
            "under S = a/q a nonzero R is a nonzero multiple of 1/q so |R| >= 1/q, "
            "while the only recorded smallness is |R| <= 1/2; the two are "
            "compatible for every q >= 2"),
        "beats_kempner_exclusion_from_t": t_star,
        "kempner_index": KEMPNER_INDEX,
    }


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--max-n", type=int, default=2)
    args = ap.parse_args()
    print(json.dumps(run(args.max_n), indent=2, default=str))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
