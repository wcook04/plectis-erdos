#!/usr/bin/env python3
"""Arithmetic core of an exact-even-identity rational comparison sequence (Erdos 249).

The construction under audit builds f from a sparse set of odd "roots" m by
f(m) = phi(m) + r(m) with 2^(floor(log2 m) - lambda(m) - C) | r(m), extended to
every even argument by the exact totient doubling law

    f(2^a m) = 2^(a-1) f(m)      (m odd, a >= 1),

equivalently f(2m) = f(m) for odd m and f(2m) = 2 f(m) for even m.

Three separable things are checked here.

(A) The decisive interval-overlap inequality of the construction reduces, after
    cancelling the common factor m_i 2^(-m_i), to the pure inequality
        2^(g_i + 1) <= (eps/2) 2^(lambda(m_i) + C),   g_i = m_(i+1) - m_i,
    which the stated hypotheses 2^(-C) <= eps/4 and g_i <= lambda(m_i) make an
    equality-tight consequence.  The grid below certifies both the sufficiency
    and the exact tightness (it fails at g_i = lambda(m_i) + 1).

(B) The weight identity W_m = 2^(-m) + sum_(a>=1) 2^(a-1) 2^(-2^a m) and its
    two-sided bound 2^(-m) <= W_m <= 2^(1-m), exactly, with a rigorous tail.

(C) A finite structural surrogate of f (small lambda, small C, explicit
    deterministic digits) on which the pointwise conclusions -- exact even
    identities, phi <= f <= n-1, additive error <= eps n, prime-power
    agreement, 2-adic precision f = phi mod 2^kappa(n), and the exact dyadic
    section rank 2^e + 1 -- are verified by exhaustive computation.

The surrogate is NOT an instance of the theorem: the theorem's own thresholds
lambda(B_k) >= 8 M_k with M_0 = 15 force the first root above
2^(8*15 + C + 1) >= 2^121, so no finite computation can carry its series value.
That non-instantiability is reported as a numeric receipt.
"""

from __future__ import annotations

import argparse
import json
from fractions import Fraction


def totient_sieve(limit: int) -> list[int]:
    phi = list(range(limit + 1))
    for p in range(2, limit + 1):
        if phi[p] == p:
            for m in range(p, limit + 1, p):
                phi[m] -= phi[m] // p
    return phi


def floor_log2(n: int) -> int:
    return n.bit_length() - 1


# ---------------------------------------------------------------- (A) chain

def chain_grid(eps: Fraction, c_exp: int, lam_values: list[int],
               gap_offsets: list[int]) -> dict:
    """Reduced form of the decisive inequality, exactly.

    The displayed step is
        2 m 2^(-lam-C) 2^(-m)  <=  (eps m / 2) 2^(-m-g)
    which is equivalent to 2^(g+1) <= (eps/2) 2^(lam+C).
    """
    assert Fraction(1, 2 ** c_exp) <= eps / 4
    rows = []
    for lam in lam_values:
        for off in gap_offsets:
            g = lam + off
            if g < 0:
                continue
            lhs = Fraction(2 ** (g + 1))
            rhs = (eps / 2) * Fraction(2 ** (lam + c_exp))
            rows.append(
                {
                    "lambda": lam,
                    "gap_offset": off,
                    "g": g,
                    "lhs_2^(g+1)": str(lhs),
                    "rhs_(eps/2)2^(lambda+C)": str(rhs),
                    "holds": lhs <= rhs,
                }
            )
    ok_at_gap_le_lambda = all(r["holds"] for r in rows if r["gap_offset"] <= 0)
    fails_at_gap_plus_one = all(
        not r["holds"] for r in rows if r["gap_offset"] == 1
    )
    return {
        "eps": str(eps),
        "C": c_exp,
        "hypothesis_2^-C_le_eps_over_4": str(Fraction(1, 2 ** c_exp)) + " <= "
        + str(eps / 4),
        "rows": rows,
        "sufficient_when_g_le_lambda": ok_at_gap_le_lambda,
        "tight_fails_when_g_eq_lambda_plus_1": fails_at_gap_plus_one,
        "note": "with 2^-C = eps/4 exactly the chain is equality-tight at g = lambda",
    }


# ---------------------------------------------------------------- (B) weights

def ray_weight(m: int, guard: int = 4096) -> tuple[Fraction, Fraction]:
    """Rigorous [lo, hi] bracket for W_m = 2^-m + sum_(a>=1) 2^(a-1) 2^(-2^a m)."""
    lo = Fraction(1, 2 ** m)
    a = 1
    while (1 << a) * m <= guard:
        lo += Fraction(2 ** (a - 1), 2 ** ((1 << a) * m))
        a += 1
    # remaining terms: sum_(b>=a) 2^(b-1) 2^(-2^b m) < 2^a * 2^(-2^a m)
    tail = Fraction(2 ** a, 2 ** ((1 << a) * m))
    return lo, lo + tail


def weight_bounds(max_m: int) -> dict:
    rows = []
    for m in range(1, max_m + 1):
        lo, hi = ray_weight(m)
        rows.append(
            {
                "m": m,
                "lower_ok_2^-m_le_W": Fraction(1, 2 ** m) <= lo,
                "upper_ok_W_le_2^(1-m)": hi <= Fraction(2, 2 ** m),
                "equality_at_m_1": m == 1 and hi <= Fraction(2, 2 ** m),
            }
        )
    return {
        "checked_m_range": [1, max_m],
        "all_lower_bounds_hold": all(r["lower_ok_2^-m_le_W"] for r in rows),
        "all_upper_bounds_hold": all(r["upper_ok_W_le_2^(1-m)"] for r in rows),
    }


def ray_decomposition_check(phi: list[int], odd_limit: int,
                            series_bits: int) -> dict:
    """S = sum_(m odd) phi(m) W_m, checked against the prefix bracket for S."""
    acc = Fraction(0)
    for m in range(1, odd_limit + 1, 2):
        lo, _hi = ray_weight(m)
        acc += phi[m] * lo
    blocks = 0
    for n in range(1, series_bits + 1):
        blocks = 2 * blocks + phi[n]
    s_lo = Fraction(blocks, 2 ** series_bits)
    s_hi = s_lo + Fraction(series_bits + 2, 2 ** series_bits)
    # the truncated ray sum omits odd roots m > odd_limit; their total mass is
    # bounded by sum_(m > odd_limit) m * 2^(1-m)
    omitted = Fraction(0)
    m = odd_limit + 1
    while m <= odd_limit + 200:
        omitted += Fraction(2 * m, 2 ** m)
        m += 1
    return {
        "odd_root_cutoff": odd_limit,
        "ray_sum_lower": float(acc),
        "S_lower": float(s_lo),
        "S_upper": float(s_hi),
        "consistent": bool(acc <= s_hi and acc + omitted >= s_lo),
    }


# ---------------------------------------------------------------- (C) surrogate

def build_surrogate(phi: list[int], limit: int, eps: Fraction, c_exp: int,
                    lam: int, root_modulus: int) -> tuple[list[int], list[int]]:
    """f on [0, limit] with exact even identities and root increments."""
    root_floor = 1 << (lam + c_exp + 1)  # smallest m with floor(log2 m)-lam-C >= 1
    f = [0] * (limit + 1)
    roots: list[int] = []
    for m in range(1, limit + 1, 2):
        val = phi[m]
        if m >= root_floor and m % root_modulus == 0:
            d = 1 << (floor_log2(m) - lam - c_exp)
            a = int(eps * m) // d
            if a >= 1:
                t = m % (a + 1)
                val = phi[m] + t * d
                if t > 0:
                    roots.append(m)
        f[m] = val
        # extend along the doubling ray
        n, a = 2 * m, 1
        while n <= limit:
            f[n] = (1 << (a - 1)) * val
            n *= 2
            a += 1
    return f, roots


def odd_part(n: int) -> int:
    while n % 2 == 0:
        n //= 2
    return n


def is_prime_power(n: int) -> bool:
    if n == 1:
        return True
    p = 2
    while p * p <= n:
        if n % p == 0:
            while n % p == 0:
                n //= p
            return n == 1
        p += 1
    return True


def kappa(n: int, lam: int, c_exp: int) -> int:
    return max(0, floor_log2(n) - lam - c_exp - 1)


def surrogate_audit(phi: list[int], f: list[int], roots: list[int],
                    limit: int, eps: Fraction, c_exp: int, lam: int) -> dict:
    fails: dict[str, list[int]] = {
        "even_identity": [],
        "lower_phi_le_f": [],
        "upper_f_le_n_minus_1": [],
        "additive_error": [],
        "prime_power_agreement": [],
        "two_adic_precision": [],
        "root_upper_47_over_60": [],
    }
    for n in range(2, limit + 1):
        if 2 * n <= limit:
            want = f[n] if n % 2 == 1 else 2 * f[n]
            if f[2 * n] != want:
                fails["even_identity"].append(n)
        if f[n] < phi[n]:
            fails["lower_phi_le_f"].append(n)
        if f[n] > n - 1:
            fails["upper_f_le_n_minus_1"].append(n)
        if Fraction(f[n] - phi[n]) > eps * n:
            fails["additive_error"].append(n)
        if is_prime_power(odd_part(n)) and f[n] != phi[n]:
            fails["prime_power_agreement"].append(n)
        if (f[n] - phi[n]) % (1 << kappa(n, lam, c_exp)) != 0:
            fails["two_adic_precision"].append(n)
    for m in roots:
        if Fraction(f[m]) > Fraction(47, 60) * m:
            fails["root_upper_47_over_60"].append(m)
    changed = sum(1 for n in range(1, limit + 1) if f[n] != phi[n])
    # Proposition 5 mechanism: relative error is constant along a doubling ray
    ray_rows = []
    for m in roots[:5]:
        vals = []
        n, a = m, 0
        while n <= limit:
            vals.append(str(Fraction(f[n] - phi[n], n)))
            n *= 2
            a += 1
        ray_rows.append({"root": m, "relative_errors_along_ray": vals})
    return {
        "limit": limit,
        "root_count": len(roots),
        "first_roots": roots[:8],
        "changed_arguments": changed,
        "changed_density": float(Fraction(changed, limit)),
        "failures": {k: v[:8] for k, v in fails.items()},
        "all_pointwise_claims_hold": all(not v for v in fails.values()),
        "prop5_ray_relative_error_constant": ray_rows,
    }


def sharpened_rigidity_witness(phi: list[int], f: list[int], roots: list[int],
                               limit: int) -> dict:
    """Exact even identities are incompatible with all-modulus eventual agreement.

    If g obeys g(2m)=g(m) (m odd) and g(2m)=2g(m) (m even), then
    delta(2^a m) = 2^(a-1) delta(m) for odd m.  If in addition for every q there
    is N_q with q | delta(n) for n >= N_q, pick an odd prime q > |delta(m)| and
    a with 2^a m >= N_q: q | 2^(a-1) delta(m) and q odd force q | delta(m),
    hence delta(m) = 0.  So g = phi.  The witness below exhibits, on the
    surrogate, an odd prime q and arbitrarily large n with q not dividing
    f(n) - phi(n) -- the failure that the proposition predicts.
    """
    if not roots:
        return {"witness": None}
    m = roots[0]
    d = f[m] - phi[m]
    q = 3
    while d % q == 0 or q == 2:
        q += 2
    positions = []
    n = m
    while n <= limit:
        if (f[n] - phi[n]) % q != 0:
            positions.append(n)
        n *= 2
    return {
        "root": m,
        "delta_at_root": d,
        "odd_prime_q_not_dividing_delta": q,
        "large_arguments_with_q_not_dividing_delta": positions[-6:],
        "count_along_ray": len(positions),
        "conclusion": "no exact-even-identity deformation can agree with phi "
                      "eventually modulo every fixed integer",
    }


def matrix_rank_q(rows: list[list[int]]) -> int:
    mat = [[Fraction(x) for x in r] for r in rows]
    rank = 0
    ncols = len(mat[0]) if mat else 0
    row = 0
    for col in range(ncols):
        piv = None
        for r in range(row, len(mat)):
            if mat[r][col] != 0:
                piv = r
                break
        if piv is None:
            continue
        mat[row], mat[piv] = mat[piv], mat[row]
        pv = mat[row][col]
        mat[row] = [x / pv for x in mat[row]]
        for r in range(len(mat)):
            if r != row and mat[r][col] != 0:
                factor = mat[r][col]
                mat[r] = [a - factor * b for a, b in zip(mat[r], mat[row])]
        row += 1
        rank += 1
        if row == len(mat):
            break
    return rank


def dyadic_section_rank(seq: list[int], limit: int, e: int,
                        samples: int) -> int:
    """rank of {n -> seq(2^j n + r) : 0<=j<=e, 0<=r<2^j} on n = 0..samples-1."""
    fam = []
    for j in range(e + 1):
        for r in range(1 << j):
            row = []
            for n in range(samples):
                idx = (1 << j) * n + r
                if idx > limit:
                    row = None
                    break
                row.append(seq[idx])
            if row is None:
                return -1
            fam.append(row)
    return matrix_rank_q(fam)


def build_payload(limit: int, eps_den: int, c_exp: int, lam: int,
                  root_modulus: int, rank_levels: int,
                  rank_samples: int) -> dict:
    eps = Fraction(1, eps_den)
    phi = totient_sieve(limit + 2)
    f, roots = build_surrogate(phi, limit, eps, c_exp, lam, root_modulus)
    parity_control = list(phi)  # corpus parity-perturbed shape, digits in {-2..1}
    for m in range(2, limit // 2 + 1):
        if 2 * m <= limit:
            parity_control[2 * m] = phi[2 * m] + ((m % 4) - 2)
    ranks = {}
    for e in range(1, rank_levels + 1):
        ranks[f"e={e}"] = {
            "expected_totient_rank_2^e+1": (1 << e) + 1,
            "totient": dyadic_section_rank(phi, limit, e, rank_samples),
            "even_identity_control_f": dyadic_section_rank(
                f, limit, e, rank_samples
            ),
            "parity_perturbed_shape": dyadic_section_rank(
                parity_control, limit, e, rank_samples
            ),
        }
    return {
        "probe": "even_identity_control_arithmetic",
        "chain_inequality": chain_grid(
            eps, c_exp, [4, 8, 16, 32, 120], [-4, -2, -1, 0, 1, 2]
        ),
        "weight_bounds": weight_bounds(40),
        "ray_decomposition": ray_decomposition_check(phi, 61, 200),
        "surrogate_parameters": {
            "eps": str(eps),
            "C": c_exp,
            "lambda_constant": lam,
            "root_modulus": root_modulus,
            "root_floor_2^(lambda+C+1)": 1 << (lam + c_exp + 1),
            "note": "structural surrogate; lambda is constant so the value-side "
                    "gap hypothesis g_i <= lambda(m_i) is deliberately not met",
        },
        "surrogate_audit": surrogate_audit(
            phi, f, roots, limit, eps, c_exp, lam
        ),
        "sharpened_rigidity": sharpened_rigidity_witness(phi, f, roots, limit),
        "dyadic_section_ranks": ranks,
        "non_instantiability": {
            "M_0": 15,
            "required_lambda_at_B_0_ge_8*M_0": 120,
            "required_floor_log2_B_0_ge_lambda+C+1": 121,
            "minimum_first_root_B_0": "2^121",
            "smallest_ray_weight_scale": "about 2^(-2^121)",
            "conclusion": "the theorem admits no finite numeric witness; only "
                          "its pointwise arithmetic can be computed",
        },
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--limit", type=int, default=200000)
    parser.add_argument("--eps-denominator", type=int, default=4)
    parser.add_argument("--c-exp", type=int, default=4)
    parser.add_argument("--lambda-constant", type=int, default=4)
    parser.add_argument("--root-modulus", type=int, default=15)
    parser.add_argument("--rank-levels", type=int, default=3)
    parser.add_argument("--rank-samples", type=int, default=64)
    parser.add_argument("--quick", action="store_true")
    args = parser.parse_args()
    if args.quick:
        args.limit = 50000
        args.rank_levels = 3
        args.rank_samples = 48
    print(
        json.dumps(
            build_payload(
                args.limit,
                args.eps_denominator,
                args.c_exp,
                args.lambda_constant,
                args.root_modulus,
                args.rank_levels,
                args.rank_samples,
            ),
            indent=2,
        )
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
