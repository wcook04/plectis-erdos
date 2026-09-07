#!/usr/bin/env python3
"""Exact certificate for the {2,3,5} jump-constraint carry majorant.

Independently regenerates Type B's proposed bound

    Q̃(n) = (1210 n² + 9130 n + 18847) / 11979

from the generating function of weights forced by the prohibition on three
consecutive 2-jumps, checks that prohibition by unique-factorisation
arithmetic, and compares the resulting majorant with truncated exact tails of
X_a.  Every decision is an integer or ``Fraction`` comparison.

This is a certificate for the ordinary majorant, not an irrationality proof.
"""

from __future__ import annotations

import argparse
import json
import sys
from fractions import Fraction
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[4]
SCRIPTS = (
    REPO_ROOT
    / "formal_math"
    / "erdos257_period_noncollapse"
    / "scripts"
)
if str(SCRIPTS) not in sys.path:
    sys.path.insert(0, str(SCRIPTS))

from check_erdos269_block_mass_identity import (  # noqa: E402
    height235,
    integer_log,
    smooth_values_through,
)


problem_id = "erdos_269"

M0 = Fraction(20, 11)
M1 = Fraction(170, 121)
M2 = Fraction(4694, 1331)
QTILDE_LEAD = Fraction(1210, 11979)
QTILDE_LIN = Fraction(9130, 11979)
QTILDE_CONST = Fraction(18847, 11979)


def q_old(n: int) -> Fraction:
    return Fraction(n * n + 8 * n + 18, 9)


def q_tilde(n: int) -> Fraction:
    return Fraction(1210 * n * n + 9130 * n + 18847, 11979)


def q_tilde_from_moments(n: int) -> Fraction:
    t = n + 3
    return (M0 * t * t + 2 * M1 * t + M2) / 18


def generating_function_algebra() -> dict[str, object]:
    """Closed-form moments of A(z) = (1 + z/2 + z²/6) / (1 − z³/12)."""

    z = Fraction(1)
    numer = 1 + z / 2 + z * z / 6
    denom = 1 - z * z * z / 12
    a_at_one = numer / denom
    n_prime = Fraction(1, 2) + z / 3
    d_prime = -(z * z) / 4
    a_prime_num = n_prime * denom - numer * d_prime
    a_prime = a_prime_num / (denom * denom)
    # A'' via quotient rule on A' = P/Q with Q = D^2.
    n_second = Fraction(1, 3)
    d_second = -z / 2
    p_prime = (
        n_second * denom
        + n_prime * d_prime
        - n_prime * d_prime
        - numer * d_second
    )
    # P = N'D - ND', so P' = N''D + N'D' - (N'D' + ND'') = N''D - ND''.
    p_prime = n_second * denom - numer * d_second
    q = denom * denom
    q_prime = 2 * denom * d_prime
    a_second = (p_prime * q - a_prime_num * q_prime) / (q * q)
    m0 = a_at_one
    m1 = z * a_prime
    m2 = z * (a_prime + z * a_second)
    mismatch = []
    if m0 != M0:
        mismatch.append(("M0", str(m0), str(M0)))
    if m1 != M1:
        mismatch.append(("M1", str(m1), str(M1)))
    if m2 != M2:
        mismatch.append(("M2", str(m2), str(M2)))
    n_samples = [1, 2, 5, 10, 17]
    form_ok = all(q_tilde(n) == q_tilde_from_moments(n) for n in n_samples)
    diff_ok = all(
        q_old(n) - q_tilde(n) == Fraction(121 * n * n + 1518 * n + 5111, 11979)
        and q_old(n) - q_tilde(n) > 0
        for n in n_samples
    )
    unconstrained_ok = True
    # Q(n) is the same 1/18-moment formula with weights 2^{-k}.
    s0 = Fraction(2)  # sum 2^{-k}
    s1 = Fraction(2)  # sum k 2^{-k}
    s2 = Fraction(6)  # sum k^2 2^{-k}
    for n in n_samples:
        unconstrained = (s0 * (n + 3) ** 2 + 2 * s1 * (n + 3) + s2) / 18
        if unconstrained != q_old(n):
            unconstrained_ok = False
            break
    return {
        "A_one": str(m0),
        "zA_prime_one": str(m1),
        "z_zA_prime_prime_one": str(m2),
        "moment_targets": {"M0": str(M0), "M1": str(M1), "M2": str(M2)},
        "moment_mismatch": mismatch,
        "qtilde_matches_moments": form_ok,
        "q_minus_qtilde_identity": diff_ok,
        "unconstrained_recovers_Q": unconstrained_ok,
        "algebra_ok": not mismatch and form_ok and diff_ok and unconstrained_ok,
    }


def three_power_between(e: int) -> int:
    n = 1 << e
    v = integer_log(3, n) + 1
    return 3**v


def jump_constraint_scan(e_max: int) -> dict[str, object]:
    """No three consecutive 2-powers in the merged {2,3,5}-power list."""

    limit = 1 << (e_max + 2)
    powers: list[tuple[int, int, int]] = []
    for p in (2, 3, 5):
        e = 1
        val = p
        while val <= limit:
            powers.append((val, p, e))
            e += 1
            val *= p
    powers.sort()
    consecutive_two = 0
    triple_failures: list[list[int]] = []
    for _val, p, _e in powers:
        if p == 2:
            consecutive_two += 1
            if consecutive_two >= 3:
                triple_failures.append([_val])
        else:
            consecutive_two = 0
    between_failures: list[int] = []
    for e in range(0, e_max + 1):
        t = three_power_between(e)
        lo = 1 << e
        hi = 1 << (e + 2)
        if not (lo < t < hi):
            between_failures.append(e)
    return {
        "e_max": e_max,
        "merged_count": len(powers),
        "three_consecutive_two_jumps": len(triple_failures),
        "between_interval_failures": between_failures,
        "jump_constraint_ok": not triple_failures and not between_failures,
    }


def rank_index(a: int) -> int:
    """n_a = #{p^e : p in {2,3,5}, e>=1, p^e <= 2^a}."""

    cutoff = 1 << a
    return (
        integer_log(2, cutoff)
        + integer_log(3, cutoff)
        + integer_log(5, cutoff)
    )


def tail_majorant_scan(max_a: int, trunc_a: int) -> dict[str, object]:
    """Compare truncated X_a plus a Lean-width remainder against Q̃(n_a)."""

    if trunc_a <= max_a:
        raise ValueError("trunc_a must exceed max_a")
    smooth = smooth_values_through(1 << (trunc_a + 1))
    shell: dict[int, Fraction] = {}
    for a in range(1, trunc_a + 1):
        lo, hi = 1 << a, 1 << (a + 1)
        shell[a] = sum(
            (Fraction(1, height235(x)) for x in smooth if lo <= x < hi),
            Fraction(),
        )
    tails: dict[int, Fraction] = {trunc_a + 1: Fraction()}
    for a in range(trunc_a, 0, -1):
        tails[a] = shell[a] + tails[a + 1]
    rows = []
    violations = []
    for a in range(1, max_a + 1):
        h_a = height235(1 << a)
        x_trunc = Fraction(h_a, 2) * tails[a]
        # Missing mass is x ≥ 2^{trunc_a+1}.  Scale the already-landed
        # exact_checker width X_m ≤ m^2+6m+11 at m = trunc_a+1 by the
        # height ratio H(2^a)/H(2^m) ≤ 2^{-(m-a)}.
        m = trunc_a + 1
        remainder = Fraction(m * m + 6 * m + 11, 1 << (m - a))
        n_a = rank_index(a)
        qt = q_tilde(n_a)
        qo = q_old(n_a)
        certified_upper = x_trunc + remainder
        ok = certified_upper <= qt
        row = {
            "a": a,
            "n_a": n_a,
            "X_trunc": str(x_trunc),
            "remainder_majorant": str(remainder),
            "certified_upper": str(certified_upper),
            "Qtilde": str(qt),
            "Q": str(qo),
            "trunc_le_Qtilde": x_trunc <= qt,
            "certified_le_Qtilde": ok,
        }
        rows.append(row)
        if not ok:
            violations.append(a)
    return {
        "max_a": max_a,
        "trunc_a": trunc_a,
        "violations": violations,
        "tail_ok": not violations,
        "rows": rows,
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--quick",
        action="store_true",
        help="algebra + jumps to 2^16 + tails a<=8 truncated at 16",
    )
    parser.add_argument(
        "--json-out",
        type=Path,
        default=None,
        help="optional receipt path",
    )
    args = parser.parse_args()
    if args.quick:
        e_max, max_a, trunc_a = 16, 8, 20
    else:
        e_max, max_a, trunc_a = 24, 12, 24
    algebra = generating_function_algebra()
    jumps = jump_constraint_scan(e_max)
    tails = tail_majorant_scan(max_a, trunc_a)
    payload = {
        "problem_id": problem_id,
        "claim": "jump_constraint_carry_majorant",
        "algebra": algebra,
        "jumps": jumps,
        "tails": {
            "max_a": tails["max_a"],
            "trunc_a": tails["trunc_a"],
            "violations": tails["violations"],
            "tail_ok": tails["tail_ok"],
            "first_rows": tails["rows"][:3],
            "last_row": tails["rows"][-1],
        },
        "ok": algebra["algebra_ok"]
        and jumps["jump_constraint_ok"]
        and tails["tail_ok"],
        "claim_boundary": (
            "Exact generating-function algebra, unique-factorisation jump "
            "constraint, and a certified finite tail comparison. Not an "
            "irrationality theorem, and not a weakening of the window-escape "
            "producer (still equivalent on the whole quadratic family)."
        ),
    }
    text = json.dumps(payload, indent=2, sort_keys=True)
    print(text)
    if args.json_out is not None:
        args.json_out.parent.mkdir(parents=True, exist_ok=True)
        args.json_out.write_text(text + "\n", encoding="utf-8")
    return 0 if payload["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
