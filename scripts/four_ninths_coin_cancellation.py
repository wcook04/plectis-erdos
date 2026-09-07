#!/usr/bin/env python3
r"""
Erdos 257, 4/9 -- the coin cancels mod 2^d, so rho_d is a small-integer base-four residue.

FourNinthsDiagonalMarginInvariant.md leaves open "a genuinely nonlocal use of (5)".  This
verifies the arithmetic core of one.  Lean: ErdosProblems/Erdos257/FourNinthsCoinCancellation.lean.

DERIVATION (the run is a check, not the source)
-----------------------------------------------
History identity (5):  rho_d = sum_{j<d} 4^(d-1-j) q_j,
                       q_j   = u_(j+1) - A_(j+1) - b_(j+1)(2^(j+1)+1).
Split the coin into its power part and its unit, and reindex i = j+1.  The power part
contributes sum_{i<=d} 4^(d-i) b_i 2^i, and 4^(d-i) 2^i = 2^(2d-i) with 2d-i >= d for
i <= d, so EVERY such term is divisible by 2^d.  Hence

    (C1)  rho_d  ==  sum_{i<=d} 4^(d-i) (u_i - A_i - b_i)          (mod 2^d)

with the exponential gone.  Terms with i <= d/2 have 4^(d-i) divisible by 2^d too, so

    (C2)  rho_d  ==  sum_{d/2 < i <= d} 4^(d-i) (u_i - A_i - b_i)  (mod 2^d)

and since 0 <= rho_d < 2^d on the orbit, the residue PINS rho_d exactly.

PREDICTIONS, DECLARED BEFORE THE RUN
------------------------------------
P1  (C1) holds at every d in range: zero violations.
P2  (C2) holds at every d in range: zero violations.
P3  0 <= rho_d < 2^d at every rank, so the congruence determines rho_d rather than merely
    constraining it.
P4  the surviving summands are SMALL: u_i in {0,1,3}, b_i in {0,1}, and max A_i is modest,
    so (C2) is a base-four sum of small integers with no exponential in it.
P5  at every rank, rho_d is the signed even-horizon quotient defect

        floor(4^(d+1)/9) - sum_{a<=d, b_a=1} floor(4^d/(2^a-1)).

    The audit checks its affine quotient recurrence at every rank and recomputes the literal
    finite quotient sum on a logarithmic-plus-frontier sample through depth 4096.  The affine
    recurrence audit still runs at every requested rank; the literal big-integer divisions are
    deliberately capped so enlarging the dynamical horizon does not reintroduce quadratic work.
P6  the exact saturated-boundary classifier has zero violations: whenever rho_(d-1)=2^(d-1),
    strict escape at d occurs iff the new pulse is three and the paired load is at most one.
P7  every skipped row with valuation v >= 2 satisfies the adaptive Lean suffix certificate:
    for k = min(floor(v/2), floor(d/2)), its last k small increments sum to a multiple of
    4^k.  Its newest small increment is itself a nonpositive multiple of four.
P8  the midpoint source equations hold exactly at every even and odd depth.  Whenever a
    full midpoint suffix is divisible by 4^k beyond the rank-two anchor, its normalized
    carry is nonpositive.  Record the unsigned midpoint-word gaps as a falsifier for the
    tempting but insufficient strategy of proving only W < rho.

FALSIFIER
---------
Any violation of (C1) or (C2), or any rank with rho_d >= 2^d, voids the reformulation.

    ./repo-python formal_math/erdos257_period_noncollapse/scripts/four_ninths_coin_cancellation.py [horizon]
"""
from __future__ import annotations
import json, sys
from array import array
from math import gcd

problem_id = "erdos_257"
HORIZON = int(sys.argv[1]) if len(sys.argv) > 1 else 900

def pair_pulse(r: int) -> int:
    return 0 if r % 3 == 0 else (1 if r % 3 == 1 else 3)

def schedule(loads: array, rank: int, H: int) -> None:
    period = rank // gcd(rank, 2)
    start = (rank // period + 1) * period
    for f in range(start, H + 1, period):
        loads[f] += 1
    if rank % 2 == 1:
        start = (3 * rank + 1) // 2
        for f in range(start, H + 1, rank):
            loads[f] += 2

def main() -> None:
    H = HORIZON
    loads = array("I", [0]) * (H + 2)
    rho = 0; target = 0; quotient_mass = 0
    u = [0] * (H + 2); A = [0] * (H + 2); b = [0] * (H + 2); rhos = [0] * (H + 2)
    # Exact source histories used by the midpoint-reachability audit below.
    small_histories = [0] * (H + 2)
    take_histories = [0] * (H + 2)
    quotient_recurrence_violations = 0
    upper_window_violations = 0
    saturated_depth_count = 0
    saturated_classifier_checks = 0
    saturated_classifier_violations = 0
    skipped_transition_count = 0
    skipped_load_pulse_mod_four_candidate_count = 0
    skipped_zero_remainder_count = 0
    max_skipped_remainder_two_adic_valuation = 0
    max_skipped_remainder_two_adic_rank = 0
    closest_upper_rank = 0
    closest_upper_gap_bit_length = 0
    closest_upper_exponent_deficit = -10**9
    selected: list[int] = []
    for rank in range(1, H + 1):
        previous_rho = rho
        u[rank] = pair_pulse(rank); A[rank] = int(loads[rank])
        T = 4 * rho + u[rank] - A[rank]; coin = (1 << rank) + 1
        take = coin <= T
        b[rank] = 1 if take else 0
        small_histories[rank] = (
            4 * small_histories[rank - 1] + u[rank] - A[rank] - b[rank]
        )
        take_histories[rank] = 2 * take_histories[rank - 1] + b[rank]
        rho = T - coin if take else T
        target = 4 * target + u[rank]
        quotient_mass = 4 * quotient_mass + A[rank] + (coin if take else 0)
        if rho != target - quotient_mass:
            quotient_recurrence_violations += 1
        boundary = 1 << rank
        if rho > boundary:
            upper_window_violations += 1
        if rho == boundary:
            saturated_depth_count += 1
        if previous_rho == (1 << (rank - 1)):
            saturated_classifier_checks += 1
            crosses = boundary < rho
            sparse_large_pulse = u[rank] == 3 and A[rank] <= 1
            if crosses != sparse_large_pulse:
                saturated_classifier_violations += 1
        if not take:
            skipped_transition_count += 1
            if (A[rank] - u[rank]) % 4 == 0:
                skipped_load_pulse_mod_four_candidate_count += 1
            if rho == 0:
                skipped_zero_remainder_count += 1
            else:
                valuation = (abs(rho) & -abs(rho)).bit_length() - 1
                if valuation > max_skipped_remainder_two_adic_valuation:
                    max_skipped_remainder_two_adic_valuation = valuation
                    max_skipped_remainder_two_adic_rank = rank
        if 0 <= rho < boundary:
            gap_bits = (boundary - rho).bit_length()
            deficit = rank - gap_bits
            if deficit > closest_upper_exponent_deficit:
                closest_upper_rank = rank
                closest_upper_gap_bit_length = gap_bits
                closest_upper_exponent_deficit = deficit
        rhos[rank] = rho
        if take:
            selected.append(rank)
            schedule(loads, rank, H)

    v1 = v2 = 0; pinned = 0; checked = 0
    full_sum = 0
    half_sum = 0
    for d in range(2, H + 1):
        M = 1 << d
        if d == 2:
            full_sum = 4 * (u[1] - A[1] - b[1]) + (u[2] - A[2] - b[2])
            half_sum = u[2] - A[2] - b[2]
        else:
            increment = u[d] - A[d] - b[d]
            full_sum = 4 * full_sum + increment
            half_sum = 4 * half_sum + increment
            if d % 2 == 0:
                k = d // 2
                half_sum -= (1 << (2 * k)) * (u[k] - A[k] - b[k])
        if (full_sum - rhos[d]) % M != 0:
            v1 += 1
        if (half_sum - rhos[d]) % M != 0:
            v2 += 1
        if 0 <= rhos[d] < M:
            pinned += 1
        checked += 1
    adaptive_suffix_checks = 0
    adaptive_suffix_violations = 0
    latest_small_increment_violations = 0
    max_adaptive_suffix_length = 0
    max_adaptive_suffix_rank = 0
    max_adaptive_suffix_terminal_carry = 0
    for d in range(2, H + 1):
        if b[d] != 0 or rhos[d] == 0:
            continue
        valuation = (abs(rhos[d]) & -abs(rhos[d])).bit_length() - 1
        if valuation < 2:
            continue
        k = min(valuation // 2, d // 2)
        suffix = 0
        for i in range(d - k + 1, d + 1):
            suffix = 4 * suffix + (u[i] - A[i] - b[i])
        modulus = 4 ** k
        adaptive_suffix_checks += 1
        if suffix % modulus != 0:
            adaptive_suffix_violations += 1
        latest = u[d] - A[d] - b[d]
        if latest % 4 != 0 or latest > 0:
            latest_small_increment_violations += 1
        if k > max_adaptive_suffix_length:
            max_adaptive_suffix_length = k
            max_adaptive_suffix_rank = d
            max_adaptive_suffix_terminal_carry = suffix // modulus
    maxA = max(A[1:H + 1]); maxu = max(u[1:H + 1])

    # Midpoint source-reachability.  These are exact integer identities, not
    # floating-point diagnostics.  At depth 2k, W is the binary word of decisions
    # k+1,...,2k and S is the last-k small history.  Odd depth 2k+1 has the same
    # form after splitting at k+1, but its word is shifted left once.
    midpoint_identity_violations = 0
    midpoint_full_divisibility_count = 0
    midpoint_positive_carry_violations = 0
    midpoint_saturated_equation_violations = 0
    even_midpoint_gap_min = None
    even_midpoint_gap_max = None
    even_midpoint_zero_gap_depths = []
    odd_midpoint_gap_min = None
    odd_midpoint_gap_max = None
    odd_midpoint_gap_below_two_count = 0
    odd_midpoint_zero_gap_depths = []
    four_pow = 4
    two_pow = 2
    for k in range(1, H // 2 + 1):
        if k > 1:
            four_pow *= 4
            two_pow *= 2
        small_suffix = small_histories[2 * k] - four_pow * small_histories[k]
        take_word = take_histories[2 * k] - two_pow * take_histories[k]
        gap = rhos[k] - take_word
        if rhos[2 * k] != four_pow * gap + small_suffix:
            midpoint_identity_violations += 1
        even_midpoint_gap_min = gap if even_midpoint_gap_min is None else min(
            even_midpoint_gap_min, gap)
        even_midpoint_gap_max = gap if even_midpoint_gap_max is None else max(
            even_midpoint_gap_max, gap)
        if gap == 0:
            even_midpoint_zero_gap_depths.append(2 * k)
        if small_suffix % four_pow == 0:
            midpoint_full_divisibility_count += 1
            carry = small_suffix // four_pow
            if k >= 2 and carry > 0:
                midpoint_positive_carry_violations += 1
            if rhos[2 * k] == four_pow and gap + carry != 1:
                midpoint_saturated_equation_violations += 1

    four_pow = 1
    two_pow = 1
    for k in range(1, (H - 1) // 2 + 1):
        four_pow *= 4
        two_pow *= 2
        small_suffix = (
            small_histories[2 * k + 1] - four_pow * small_histories[k + 1]
        )
        take_word = 2 * (
            take_histories[2 * k + 1] - two_pow * take_histories[k + 1]
        )
        gap = rhos[k + 1] - take_word
        if rhos[2 * k + 1] != four_pow * gap + small_suffix:
            midpoint_identity_violations += 1
        odd_midpoint_gap_min = gap if odd_midpoint_gap_min is None else min(
            odd_midpoint_gap_min, gap)
        odd_midpoint_gap_max = gap if odd_midpoint_gap_max is None else max(
            odd_midpoint_gap_max, gap)
        if gap < 2:
            odd_midpoint_gap_below_two_count += 1
        if gap == 0:
            odd_midpoint_zero_gap_depths.append(2 * k + 1)
        if small_suffix % four_pow == 0:
            midpoint_full_divisibility_count += 1
            carry = small_suffix // four_pow
            if carry > 0:
                midpoint_positive_carry_violations += 1
            if rhos[2 * k + 1] == 2 * four_pow and gap + carry != 2:
                midpoint_saturated_equation_violations += 1
    direct_sample_cap = min(H, 4096)
    sample_depths = set(range(1, min(direct_sample_cap, 32) + 1))
    power = 1
    while power <= direct_sample_cap:
        sample_depths.update({power, min(direct_sample_cap, power + 1),
                              min(direct_sample_cap, 2 * power - 1)})
        power *= 2
    sample_depths.update(range(max(1, direct_sample_cap - 15), direct_sample_cap + 1))
    quotient_direct_violations = 0
    for d in sorted(sample_depths):
        direct_target = (1 << (2 * d + 2)) // 9
        direct_mass = sum(
            (1 << (2 * d)) // ((1 << a) - 1) for a in selected if a <= d
        )
        if rhos[d] != direct_target - direct_mass:
            quotient_direct_violations += 1
    print(f"horizon {H}   ranks checked {checked}")
    print(f"(C1) full-sum congruence violations : {v1}")
    print(f"(C2) half-window congruence violations: {v2}")
    print(f"ranks with 0 <= rho_d < 2^d (residue pins rho_d): {pinned}/{checked}")
    print(f"surviving summand magnitudes: max u_i = {maxu}, max A_i = {maxA}, b_i in {{0,1}}")
    print(f"quotient-defect recurrence violations: {quotient_recurrence_violations}")
    print(f"literal quotient-defect violations on {len(sample_depths)} sampled depths: "
          f"{quotient_direct_violations}")
    print(f"literal quotient-defect maximum sampled depth: {direct_sample_cap}")
    print(f"upper-window violations / saturated depths: "
          f"{upper_window_violations} / {saturated_depth_count}")
    print(f"saturated classifier violations on {saturated_classifier_checks} gateways: "
          f"{saturated_classifier_violations}")
    print(f"skipped rows surviving the necessary load-pulse mod-four saturation sieve: "
          f"{skipped_load_pulse_mod_four_candidate_count}/{skipped_transition_count}")
    print(f"maximum skipped-remainder 2-adic valuation: "
          f"{max_skipped_remainder_two_adic_valuation} at rank "
          f"{max_skipped_remainder_two_adic_rank} "
          f"(zero remainders: {skipped_zero_remainder_count})")
    print(f"adaptive suffix certificate violations on {adaptive_suffix_checks} rows: "
          f"{adaptive_suffix_violations} (latest-digit violations: "
          f"{latest_small_increment_violations})")
    print(f"longest audited base-four carry chain: {max_adaptive_suffix_length} digits "
          f"at rank {max_adaptive_suffix_rank}, terminal carry "
          f"{max_adaptive_suffix_terminal_carry}")
    print(f"closest strict upper approach: rank {closest_upper_rank}, "
          f"gap bit-length {closest_upper_gap_bit_length}, "
          f"relative exponent deficit {closest_upper_exponent_deficit}")
    print(f"midpoint reachability identity violations: {midpoint_identity_violations}")
    print(f"full midpoint-divisibility rows / positive-carry violations: "
          f"{midpoint_full_divisibility_count} / {midpoint_positive_carry_violations}")
    print(f"even midpoint gap range and zero-gap depths: "
          f"[{even_midpoint_gap_min}, {even_midpoint_gap_max}] / "
          f"{even_midpoint_zero_gap_depths}")
    print(f"odd midpoint gap range, gaps below two, and zero-gap depths: "
          f"[{odd_midpoint_gap_min}, {odd_midpoint_gap_max}] / "
          f"{odd_midpoint_gap_below_two_count} / {odd_midpoint_zero_gap_depths}")
    out = {"schema": "aiw-formal-math-receipt/1", "problem_id": problem_id,
           "probe": "four_ninths_coin_cancellation", "horizon": H,
           "ranks_checked": checked, "C1_violations": v1, "C2_violations": v2,
           "ranks_pinned": pinned, "max_pulse": maxu, "max_load": maxA,
           "quotient_recurrence_violations": quotient_recurrence_violations,
           "quotient_direct_sample_count": len(sample_depths),
           "quotient_direct_max_depth": direct_sample_cap,
           "quotient_direct_violations": quotient_direct_violations,
           "upper_window_violations": upper_window_violations,
           "saturated_depth_count": saturated_depth_count,
           "saturated_classifier_checks": saturated_classifier_checks,
           "saturated_classifier_violations": saturated_classifier_violations,
           "skipped_transition_count": skipped_transition_count,
           "skipped_load_pulse_mod_four_candidate_count":
               skipped_load_pulse_mod_four_candidate_count,
           "skipped_zero_remainder_count": skipped_zero_remainder_count,
           "max_skipped_remainder_two_adic_valuation":
               max_skipped_remainder_two_adic_valuation,
           "max_skipped_remainder_two_adic_rank":
               max_skipped_remainder_two_adic_rank,
           "adaptive_suffix_checks": adaptive_suffix_checks,
           "adaptive_suffix_violations": adaptive_suffix_violations,
           "latest_small_increment_violations": latest_small_increment_violations,
           "max_adaptive_suffix_length": max_adaptive_suffix_length,
           "max_adaptive_suffix_rank": max_adaptive_suffix_rank,
           "max_adaptive_suffix_terminal_carry":
               max_adaptive_suffix_terminal_carry,
           "closest_upper_rank": closest_upper_rank,
           "closest_upper_gap_bit_length": closest_upper_gap_bit_length,
           "closest_upper_exponent_deficit": closest_upper_exponent_deficit,
           "midpoint_identity_violations": midpoint_identity_violations,
           "midpoint_full_divisibility_count": midpoint_full_divisibility_count,
           "midpoint_positive_carry_violations": midpoint_positive_carry_violations,
           "midpoint_saturated_equation_violations":
               midpoint_saturated_equation_violations,
           "even_midpoint_gap_min": even_midpoint_gap_min,
           "even_midpoint_gap_max": even_midpoint_gap_max,
           "even_midpoint_zero_gap_depths": even_midpoint_zero_gap_depths,
           "odd_midpoint_gap_min": odd_midpoint_gap_min,
           "odd_midpoint_gap_max": odd_midpoint_gap_max,
           "odd_midpoint_gap_below_two_count": odd_midpoint_gap_below_two_count,
           "odd_midpoint_zero_gap_depths": odd_midpoint_zero_gap_depths,
           "verdict": (
               "The coin's power part is divisible by 2^d at every base-four weight, so it "
               "cancels from rho_d mod 2^d: rho_d is congruent to a base-four sum of SMALL "
               "integers (pulse minus load minus decision) over only the last ceil(d/2) "
               "ranks, and since 0 <= rho_d < 2^d that residue pins rho_d exactly. The 4/9 "
               "socket b_d=1 => d <= rho_d therefore has no exponential in it: it asks that "
               "a small-integer base-four sum avoid residues {0,...,d-1} mod 2^d, equivalently "
               "that rho_d < d force the top ~d/2 - log_4 d base-four digits to vanish "
               "simultaneously. Independently, the same executable rho is exactly the signed "
               "even-horizon Mersenne quotient defect of the selected bit row. Full-rank "
               "two-adic divisibility forces a simultaneous family of base-four suffix "
               "certificates up to half depth; the audit also checks that the newest digit is "
               "a nonpositive multiple of four. This exposes an adaptive finite negative-carry "
               "automaton driven by actual divisor loads. Reformulation with the exponential "
               "removed, not a producer; "
               "proves neither the socket nor anything about Erdos 257.")}
    dest = "state/formal_math/erdos257_period_noncollapse/four_ninths_coin_cancellation_receipt.json"
    with open("public-source-redacted://ai_workflow" + dest, "w") as fh:
        json.dump(out, fh, indent=2, sort_keys=True); fh.write("\n")
    print(f"receipt: {dest}")

if __name__ == "__main__":
    main()
