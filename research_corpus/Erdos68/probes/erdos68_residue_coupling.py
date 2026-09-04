#!/usr/bin/env python3
"""Erdos #68: the Archimedean gap is an explicit weighted sum of factorial residues.

Upstream analytic state
-----------------------
The packet carries a priority-2 producer, `actual_cross_index_archimedean_
profinite_coupling`, asking for "a global invariant of the true divisor-factorial
coefficients that rules out eventual q_m = 1".  The coupling it asks for was
never written down as a formula.

The identity
------------
Write `a_n = n!-1` and `P_m = sum_(n=2)^m 1/a_n`.  Since `n! = 1 (mod a_n)`,

    m! = (m!/n!) * n! = (m!/n!)   (mod a_n),

so with `r_n(m) := m! mod a_n` the integer part of each term splits off exactly
and

    { m! P_m }  =  { sum_(n=2)^m  r_n(m) / a_n }

hence, with `A_m = 1 - {m! P_m}` the scaled predecessor gap that carries the
whole problem,

    A_m  =  1 - { sum_(n=2)^m  r_n(m)/a_n } .

That is the coupling, explicitly: the Archimedean quantity whose escape from a
`1/m` window is equivalent to Erdos #68 is a weighted sum of the *profinite*
data `m! mod (n!-1)`.

Three regimes
-------------
The terms split by comparing `m!/n!` with `a_n`:

  * **absorbed**  -- `a_n | m!`, so `r_n(m) = 0` exactly.  This is the Kempner
    condition, and it is the same statement as the packet's landed denominator
    exclusion `q` does not divide `299999!`.
  * **active**    -- `m!/n! > a_n`, a genuine modular reduction.  These carry
    essentially all of the fractional part; their measured mean sits somewhat
    below `1/2` (see the falsifier note).
  * **unreduced** -- `m!/n! < a_n` (equivalently `m! < (n!)^2`), so
    `r_n(m) = m!/n!` exactly and the term is about `m!/(n!)^2`, which collapses
    super-exponentially.

The dynamics
------------
The residues are not a static table.  From `m! = (m+1)^-1 (m+1)!` one gets

    r_n(m+1) = (m+1) * r_n(m)   (mod a_n),

verified for `n = 2..59`, `m = n..119`.  So with `x_n(m) = r_n(m)/a_n`,

    x_n(m+1) = { (m+1) * x_n(m) }

for EVERY n simultaneously: one multiplier drives every coordinate at each step.
The seed is `r_n(n) = 1` for `n >= 3` (since `n! = 1 mod a_n`); `n = 2` is the
degenerate case `a_2 = 1`, where every residue is 0.  So `x_n(m)` is the orbit of
`1/a_n` under multiplication by `n+1, n+2, ..., m`, and a coordinate is
`absorbed` exactly when that orbit hits 0, i.e. at the Kempner index of `a_n`.

That makes `A_m` the fractional part of a sum of coordinates on a product of
cyclic groups, all driven by the same growing multiplier -- a simultaneous
`x -> kx` system, not an unstructured residue table.

Why this is the route
---------------------
The active band holds about `m/2` terms.  If they are jointly equidistributed,
their sum mod 1 is uniform to within an error that shrinks far faster than the
`1/m` window the problem needs, and non-concentration follows.  So Erdos #68
reduces to an equidistribution statement about factorials in residue classes
modulo `n!-1`.

The packet already source-verified two papers on exactly that object --
Garaev-Luca-Shparlinski (prime and prime-power hit bounds for `n!` mod `q`) and
Garaev-Garcia (moments of the fibre counts `#{n <= N : n! = lambda mod p}`).
Both were imported for the *private support* route, which the packet's own claim
ceiling then closed as asymptotically impossible.  They are statements about the
distribution of factorial residues, which is what this formula consumes.

Probe
-----
Verify the identity exactly for a range of `m`, classify the three regimes, and
measure the active band against `Uniform[0,1)`.

Predeclared falsifier
---------------------
Any `m` where the identity fails.  The identity is the load-bearing output and
it is exact algebra.

The band statistics are REPORTED, not gated, and the reason is a measured
finding.  At every `m` tested the active-band mean sits below `1/2`, at
`m = 80` and `m = 100` by more than two nominal standard deviations, and the
deviation survives tightening the reduction threshold from one wrap to `10^12`
wraps -- so it is not an artefact of the band boundary.  But the nominal
standard deviation assumes the terms are independent across `n`, and the moduli
are not independent: `a_(n+1) = (n+1) a_n + n`.  The correlation that recurrence
induces is not quantified here, and it may account for the whole deviation.
The probe therefore prints the statistic and refuses to convert it into a
significance claim.

If the downward bias is real it points the favourable way.  `A_m = 1 - {sum}`,
and the dangerous configuration is `A_m` small, i.e. the sum landing just below
an integer.  A systematic downward pull on the terms pushes the sum away from
that boundary.  Establishing or refuting the bias, with a null that respects the
modulus recurrence, is a live question this probe raises and does not settle.

Claim boundary
--------------
The identity is exact algebra.  The band statistics carry no significance claim,
for the reason given above, and Erdos #68 remains open.
"""

from __future__ import annotations

import argparse
import json
import math
import statistics
from fractions import Fraction
from math import factorial
from pathlib import Path

VERIFY_MAX = 90
PROFILE_M = (40, 60, 80, 100, 120)


def verify_identity(max_m: int) -> dict:
    failures = []
    for m in range(3, max_m + 1):
        fm = factorial(m)
        prefix = sum(Fraction(1, factorial(n) - 1) for n in range(2, m + 1))
        left = fm * prefix - (fm * prefix).__floor__()
        right = sum(Fraction(fm % (factorial(n) - 1), factorial(n) - 1) for n in range(2, m + 1))
        right = right - right.__floor__()
        if left != right:
            failures.append(m)
    congruence = all(
        (factorial(m) // factorial(n)) % (factorial(n) - 1) == factorial(m) % (factorial(n) - 1)
        for m in range(3, min(max_m, 70) + 1)
        for n in range(2, m + 1)
    )
    return {
        "range": f"m = 3..{max_m}",
        "identity_failures": failures,
        "identity_holds": not failures,
        "congruence_m_over_n_factorial_eq_m_factorial_mod_a_n": congruence,
        "multiplicative_recurrence_r_n(m+1)_eq_(m+1)r_n(m)_mod_a_n": all(
            factorial(m + 1) % (factorial(n) - 1)
            == ((m + 1) * (factorial(m) % (factorial(n) - 1))) % (factorial(n) - 1)
            for n in range(2, 60)
            for m in range(n, 120)
        ),
        "seed_r_n(n)_eq_1_for_n_ge_3": all(
            factorial(n) % (factorial(n) - 1) == 1 for n in range(3, 60)
        ),
        "seed_degenerate_at_n_eq_2": factorial(2) % (factorial(2) - 1) == 0,
    }


def profile(m: int) -> dict:
    fm = factorial(m)
    absorbed, active, unreduced = [], [], []
    for n in range(2, m + 1):
        a = factorial(n) - 1
        r = fm % a
        value = r / a
        if r == 0:
            absorbed.append(n)
        elif fm // factorial(n) < a:
            unreduced.append((n, value))
        else:
            active.append((n, value))
    values = [v for _, v in active]
    n_active = len(values)
    mean = statistics.mean(values) if values else float("nan")
    sd_null = math.sqrt(1 / 12 / n_active) if n_active else float("nan")
    z = (mean - 0.5) / sd_null if n_active else float("nan")
    ordered = sorted(values)
    ks = max(
        max(abs((i + 1) / n_active - v), abs(v - i / n_active)) for i, v in enumerate(ordered)
    ) if n_active else float("nan")
    ks_scaled = ks * math.sqrt(n_active) if n_active else float("nan")
    return {
        "m": m,
        "absorbed_r_n_eq_0": absorbed,
        "active_band_size": n_active,
        "active_band_range": [active[0][0], active[-1][0]] if active else None,
        "unreduced_tail_size": len(unreduced),
        "unreduced_starts_at_n": unreduced[0][0] if unreduced else None,
        "active_mean": round(mean, 4),
        "active_mean_z_vs_uniform": round(z, 2),
        "active_ks_sqrt_n": round(ks_scaled, 3),
        "ks_1pc_critical_under_independence": 1.63,
        "independence_null_is_not_justified": (
            "moduli satisfy a_(n+1) = (n+1) a_n + n, so terms are correlated "
            "across n and the nominal sd understates the true spread"
        ),
    }


def run(verify_max: int = VERIFY_MAX) -> dict:
    identity = verify_identity(verify_max)
    profiles = [profile(m) for m in PROFILE_M]
    return {
        "probe": "erdos68_residue_coupling",
        "identity": {
            "formula": "A_m = 1 - { sum_(n=2)^m (m! mod (n!-1)) / (n!-1) }",
            **identity,
        },
        "regime_profiles": profiles,
        "reading": (
            "This is the explicit form of the packet's requested Archimedean/"
            "profinite coupling. The scaled predecessor gap whose escape from a "
            "1/m window is equivalent to Erdos #68 is a weighted sum of factorial "
            "residues m! mod (n!-1), with an absorbed head (the Kempner "
            "condition), an active band of about m/2 terms carrying essentially "
            "all the fractional part, and a super-exponentially collapsing "
            "unreduced tail. The "
            "target becomes joint equidistribution of factorial residues -- the "
            "object of the Garaev-Luca-Shparlinski and Garaev-Garcia theorems "
            "the packet already source-verified for a different, now-closed route. "
            "The residues are dynamic: r_n(m+1) = (m+1) r_n(m) mod a_n, so every "
            "coordinate is driven by the same multiplier and the system is a "
            "simultaneous x -> kx map on a product of cyclic groups."
        ),
        "claim_boundary": (
            "The identity is exact algebra. The band statistics are reported "
            "without a significance claim, because the independence null they "
            "would be tested against is violated by the modulus recurrence "
            "a_(n+1) = (n+1) a_n + n. Erdos #68 remains open."
        ),
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--verify-max", type=int, default=VERIFY_MAX)
    parser.add_argument("--json-out", type=Path, default=None)
    args = parser.parse_args()

    result = run(args.verify_max)
    text = json.dumps(result, indent=2)
    print(text)
    if args.json_out:
        args.json_out.write_text(text + "\n", encoding="utf-8")

    checks = [
        result["identity"]["identity_holds"],
        result["identity"]["congruence_m_over_n_factorial_eq_m_factorial_mod_a_n"],
        result["identity"]["multiplicative_recurrence_r_n(m+1)_eq_(m+1)r_n(m)_mod_a_n"],
        result["identity"]["seed_r_n(n)_eq_1_for_n_ge_3"],
    ]
    return 0 if all(checks) else 1


if __name__ == "__main__":
    raise SystemExit(main())
