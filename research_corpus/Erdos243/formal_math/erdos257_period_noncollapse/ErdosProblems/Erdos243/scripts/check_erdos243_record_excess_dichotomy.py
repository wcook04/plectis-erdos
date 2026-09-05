#!/usr/bin/env python3
"""Exact replay of the record-excess dichotomy identities and its two witnesses.

Source note: ErdosProblems/Erdos243/EightReturnRigidityCriteria.md section 4
(return r04).  Exact integer and exact rational arithmetic throughout; the only
floating point is in the reported gap ratios of Part C, which are diagnostics
and carry no verdict.

Canonical orbit (Koizumi Lemma 15, dictionary (C, D, E) = (c, d, e)):

    E_n = centred residue of D_n mod C_n,   a_n = (D_n - E_n)/C_n + 1,
    C_{n+1} = C_n - E_n,                    D_{n+1} = a_n D_n.

Running maximum H_n = max_{j<=n} C_j, drawdown B_n = H_n - C_n, record
increment r_n = H_{n+1} - H_n.

Part A -- the drawdown ladder and the original-coordinate bridge.

    (13)  r_n = (-E_n - B_n)_+   and   B_{n+1} = (B_n + E_n)_+ .
    (31)  E_n + q Q_n = D_n ( 1/a_{n+1} - (a_n - 1) sum_{k >= n+2} 1/a_k ) -> 0,
          Q_n = (A_n/a_n)(a_n^2/a_{n+1} - 1),  A_n = D_n/q.
    (32)  r_n = ( q Q_n - B_n )_+ + o(1), checked in its exact 1-Lipschitz form
          | r_n - (q Q_n - B_n)_+ | <= | E_n + q Q_n | .

The tail sum in (31) is exact on the canonical orbit because
sum_{k >= n+2} 1/a_k = C_{n+2}/D_{n+2}.  Orbit helpers are imported from
formal_math/probes/erdos243_koizumi_state_probe.py, never copied.

Part B -- the pre-sieved CRT block of r04 section 6.  With B = 20, R = 6,
eligible offsets 1, 5, 7, 11, 13, 17, 19 and assigned moduli
23, 29, 31, 37, 41, 43, 47, the CRT solution in [P, 2P) is reconstructed and
compared against the integer 521026757646 printed in the return, and all twenty
positions x, ..., x+19 are checked to be excluded.  The accounting is then
repeated at several (R, B) to confirm that a block of length B costs only
phi(R)/R * B fresh moduli, which is the Euler amplification K_u >= R/phi(R).

Part C -- the Fermat witness for the sharp gap constant (r04 Proposition 8).
For m_j = 2^(2^j) + 1: prod_{j<J} m_j = 2^(2^J) - 1 exactly, so
sigma_J = prod_{j<J} (1 - 1/m_j) = 2^(2^J - 1)/(2^(2^J) - 1) -> 1/2 and the gap
constant sigma^{-1} is exactly 2; also m_{j+1} = m_j^2 - 2 m_j + 2, which is NOT
the Sylvester recurrence, so the family has the right lacunary scale without
satisfying the feedback system.  The avoiding set A is enumerated to a modest
bound and the maximal gap ratio (u_{n+1} - u_n)/ell(u_n) is reported against
sigma^{-1} = 2 (ell(x) = log2 log2 max(4, x); the ratio at u = 4 is an
ell(4) = 1 boundary artefact of an asymptotic statement and is excluded).

Run:
    ./repo-python .../scripts/check_erdos243_record_excess_dichotomy.py --quick
    ./repo-python .../scripts/check_erdos243_record_excess_dichotomy.py
"""

from __future__ import annotations

import argparse
import json
import sys
from fractions import Fraction
from math import gcd, log2
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[4] / "probes"))
from erdos243_koizumi_state_probe import orbit_exact  # noqa: E402


def ell(x: int) -> float:
    return log2(log2(max(4, x)))


def crt(residues, moduli):
    x, M = 0, 1
    for r, m in zip(residues, moduli):
        assert gcd(M, m) == 1
        k = ((r - x) * pow(M, -1, m)) % m
        x += M * k
        M *= m
    return x % M, M


# ---------------------------------------------------------------------------
# Part A
# ---------------------------------------------------------------------------


def identities(p: int, q: int, steps: int) -> dict:
    orb = orbit_exact(p, q, steps)
    C, D, E, a = orb["c"], orb["d"], orb["e"], orb["a"]
    n = len(C)
    H = [C[0]]
    for i in range(1, n):
        H.append(max(H[-1], C[i]))
    B = [H[i] - C[i] for i in range(n)]
    r = [H[i + 1] - H[i] for i in range(n - 1)]

    failures = []
    for i in range(n - 1):
        if r[i] != max(0, -E[i] - B[i]):
            failures.append(("identity_13_record_increment", i))
        if B[i + 1] != max(0, B[i] + E[i]):
            failures.append(("identity_13_drawdown", i))
        if C[i + 1] != C[i] - E[i]:
            failures.append(("tail_recurrence", i))

    worst_31 = Fraction(0)
    worst_32 = Fraction(0)
    lipschitz_ok = True
    tail_31 = []
    for i in range(n - 2):
        A_n = Fraction(D[i], q)
        Q = A_n / a[i] * (Fraction(a[i] * a[i], a[i + 1]) - 1)
        lhs = Fraction(E[i]) + q * Q
        tail = Fraction(C[i + 2], D[i + 2])
        rhs = Fraction(D[i]) * (Fraction(1, a[i + 1]) - (a[i] - 1) * tail)
        if lhs != rhs:
            failures.append(("identity_31", i))
        if abs(lhs) > worst_31:
            worst_31 = abs(lhs)
        pred = max(Fraction(0), q * Q - B[i])
        gap = abs(Fraction(r[i]) - pred)
        if gap > abs(lhs):
            lipschitz_ok = False
        if i >= 1 and gap > worst_32:
            worst_32 = gap
        tail_31.append(float(lhs))
    return {"rational": [p, q], "steps": n,
            "failures": failures[:6], "failure_count": len(failures),
            "max_abs_E_plus_qQ": float(worst_31),
            "max_abs_r_minus_prediction": float(worst_32),
            "identity_32_lipschitz_holds": lipschitz_ok,
            "tail_abs_E_plus_qQ": tail_31[-4:]}


# ---------------------------------------------------------------------------
# Part B
# ---------------------------------------------------------------------------


def presieved_block(R: int, B: int, new_moduli) -> dict:
    elig = [j for j in range(B) if gcd(j, R) == 1]
    used = list(new_moduli[:len(elig)])
    assert len(used) == len(elig), "not enough fresh moduli"
    for m in used:
        assert m > B and gcd(m, R) == 1
    y, P = crt([0] + [(-j) % m for j, m in zip(elig, used)], [R] + used)
    x = y % P + P
    phi_R = sum(1 for j in range(R) if gcd(j, R) == 1)
    return {
        "R": R, "B": B, "x": x, "P": P,
        "P_le_x_lt_2P": P <= x < 2 * P,
        "x_mod_R": x % R,
        "eligible_offsets": elig,
        "assigned_moduli": used,
        "assignment_holds": all((x + j) % m == 0 for j, m in zip(elig, used)),
        "all_positions_excluded": all(gcd(x + j, P) > 1 for j in range(B)),
        "positions_not_excluded": [j for j in range(B) if gcd(x + j, P) == 1],
        "k_B": len(elig),
        "phi_R_over_R_times_B": B * phi_R / R,
        "moduli_spent_over_B": len(elig) / B,
        "R_over_phi_R": R / phi_R,
        "ell_2P": ell(2 * P),
    }


def presieve(quick: bool) -> dict:
    quoted_x = 521026757646
    row = presieved_block(6, 20, [23, 29, 31, 37, 41, 43, 47])
    row["r04_quoted_x"] = quoted_x
    row["reconstructed_equals_quoted"] = row["x"] == quoted_x
    row["quoted_minus_reconstructed"] = quoted_x - row["x"]
    row["quoted_x_excludes_all_20"] = all(
        gcd(quoted_x + j, row["P"]) > 1 for j in range(20))
    primes = [n for n in range(2, 3000)
              if all(n % d for d in range(2, int(n ** 0.5) + 1))]
    sweep = []
    pairs = [(6, 20), (6, 60), (30, 60)] if quick else [
        (6, 20), (6, 60), (6, 120), (30, 60), (30, 120), (210, 120), (210, 300)]
    for R, B in pairs:
        cand = [m for m in primes if m > B and gcd(m, R) == 1]
        if len([j for j in range(B) if gcd(j, R) == 1]) > len(cand):
            continue
        s = presieved_block(R, B, cand)
        sweep.append({k: s[k] for k in
                      ("R", "B", "k_B", "phi_R_over_R_times_B", "R_over_phi_R",
                       "all_positions_excluded", "P_le_x_lt_2P",
                       "moduli_spent_over_B")})
    ok = (row["reconstructed_equals_quoted"] and row["all_positions_excluded"]
          and row["quoted_x_excludes_all_20"] and row["assignment_holds"]
          and row["P_le_x_lt_2P"]
          and all(s["all_positions_excluded"] and s["P_le_x_lt_2P"] for s in sweep))
    return {"r04_section6_B20_R6": row, "sweep": sweep, "all_blocks_ok": ok}


# ---------------------------------------------------------------------------
# Part C
# ---------------------------------------------------------------------------


def fermat(j: int) -> int:
    return (1 << (1 << j)) + 1


def fermat_gap(quick: bool) -> dict:
    jmax = 8 if quick else 12
    prod = 1
    sigma = Fraction(1)
    product_identity = True
    sigma_rows = []
    for j in range(jmax):
        m = fermat(j)
        prod *= m
        sigma *= Fraction(m - 1, m)
        if prod != (1 << (1 << (j + 1))) - 1:
            product_identity = False
        sigma_rows.append({"J": j + 1, "sigma_J": float(sigma),
                           "sigma_J_minus_half": float(sigma - Fraction(1, 2))})
    recurrence = all(fermat(j + 1) == fermat(j) ** 2 - 2 * fermat(j) + 2
                     for j in range(6))

    limit = 2_000_000 if quick else 20_000_000
    mods = [fermat(j) for j in range(5)]
    sieve = bytearray(b"\x01") * (limit + 1)
    sieve[0] = 0
    for m in mods:
        if m <= limit:
            sieve[m::m] = bytearray(len(sieve[m::m]))
    prev = None
    max_gap = (0, 0)
    max_ratio_tail = (0.0, 0)
    for u in range(1, limit + 1):
        if sieve[u]:
            if prev is not None:
                g = u - prev
                if g > max_gap[0]:
                    max_gap = (g, prev)
                if prev >= 1000:
                    rr = g / ell(prev)
                    if rr > max_ratio_tail[0]:
                        max_ratio_tail = (rr, prev)
            prev = u
    return {
        "moduli": mods,
        "product_identity_prod_m_eq_2_pow_2_pow_J_minus_1": product_identity,
        "recurrence_m_next_eq_m_squared_minus_2m_plus_2": recurrence,
        "sigma_rows_tail": sigma_rows[-3:],
        "sigma_limit": 0.5,
        "gap_constant_sigma_inverse": 2.0,
        "enumeration_limit": limit,
        "max_gap": max_gap[0], "max_gap_at_u": max_gap[1],
        "max_gap_over_ell_u_for_u_ge_1000": max_ratio_tail[0],
        "at_u": max_ratio_tail[1],
        "respects_sigma_inverse": max_ratio_tail[0] <= 2.0 + 1e-9,
        "boundary_artefact_note": "the ratio 3.0 at u = 4 reported elsewhere is "
                                  "the ell(4) = 1 artefact of an asymptotic "
                                  "statement, not a counterexample",
    }


# ---------------------------------------------------------------------------


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--quick", action="store_true")
    ap.add_argument("--json", action="store_true")
    args = ap.parse_args()

    cases = ([(11, 29), (1, 7), (5, 13), (37, 97)] if args.quick
             else [(11, 29), (1, 7), (5, 13), (37, 97), (101, 397), (2, 5),
                   (123, 1000), (355, 1130), (7, 9)])
    part_a = [identities(p, q, 11) for p, q in cases]
    part_b = presieve(args.quick)
    part_c = fermat_gap(args.quick)

    ok = (all(row["failure_count"] == 0 and row["identity_32_lipschitz_holds"]
              for row in part_a)
          and part_b["all_blocks_ok"]
          and part_c["product_identity_prod_m_eq_2_pow_2_pow_J_minus_1"]
          and part_c["recurrence_m_next_eq_m_squared_minus_2m_plus_2"]
          and part_c["respects_sigma_inverse"])

    report = {
        "check": "erdos243_record_excess_dichotomy",
        "status": "pass" if ok else "fail",
        "evidence_class": "exact_computation",
        "mode": "quick" if args.quick else "full",
        "identities": part_a,
        "presieved_crt_block": part_b,
        "fermat_gap_constant": part_c,
        "scope": "Finite exact replay of the (13)/(31)/(32) identities, the "
                 "B = 20 R = 6 pre-sieved block, and the Fermat witness for the "
                 "sharp gap constant 2.  The dichotomy K = 0 or K > 1 itself is "
                 "an ordinary proof over the Lean core and rests on an "
                 "asymptotic placement that no finite orbit witnesses; on every "
                 "computable orbit the numerator terminates and K = 0.  Nothing "
                 "here settles Erdos #243.",
    }
    if args.json:
        print(json.dumps(report, indent=2, sort_keys=True))
    else:
        print(json.dumps({
            "check": report["check"], "status": report["status"],
            "evidence_class": report["evidence_class"], "mode": report["mode"],
            "orbits": len(part_a),
            "identity_failures": sum(r["failure_count"] for r in part_a),
            "identity_32_lipschitz_all": all(r["identity_32_lipschitz_holds"]
                                             for r in part_a),
            "max_abs_E_plus_qQ": max(r["max_abs_E_plus_qQ"] for r in part_a),
            "crt_reconstructed_equals_quoted":
                part_b["r04_section6_B20_R6"]["reconstructed_equals_quoted"],
            "crt_all_positions_excluded":
                part_b["r04_section6_B20_R6"]["all_positions_excluded"],
            "crt_sweep_blocks": len(part_b["sweep"]),
            "fermat_product_identity":
                part_c["product_identity_prod_m_eq_2_pow_2_pow_J_minus_1"],
            "fermat_max_gap": part_c["max_gap"],
            "fermat_max_gap_ratio_u_ge_1000":
                part_c["max_gap_over_ell_u_for_u_ge_1000"],
            "fermat_respects_sigma_inverse_2": part_c["respects_sigma_inverse"],
        }, sort_keys=True))
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
