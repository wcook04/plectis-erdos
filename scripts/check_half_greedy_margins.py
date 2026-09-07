#!/usr/bin/env python3
"""check_half_greedy_margins.py

Exact safety-margin certification for the FULL half-greedy Mersenne orbit,
in the sharp tail coordinate, using certified (scaled-integer) interval
arithmetic. stdlib only.

Companion measurement layer for
docs/formal_math/erdos257_reset_crossing_unification_2026_07_24.md
(Theorem C / section 8). Authored by a verification subagent fleet on
2026-07-24 and promoted after review; the original depth-3000 run receipts
live in that document's section 8.

MODEL
-----
weights   x_n = 1/(2^n - 1),   n = 2, 3, 4, ...
target    rho_0 = 1/2
greedy    at rank k: TAKE iff rho >= x_k  (then rho -= x_k), else SKIP.

EXACT STATE
-----------
rho is carried as an UNREDUCED fraction (num, den), starting (1, 2).
  take test:    num*(2**k - 1) >= den
  take update:  num = num*(2**k - 1) - den ;  den = den*(2**k - 1)
The state is NEVER gcd-reduced (den = 2 * prod of (2^d-1) over takes; a gcd
on a number with potentially millions of bits at depth ~3000 is not needed
for correctness of the greedy process and would dominate runtime).

SAFETY CERTIFICATION AT EACH SKIP
----------------------------------
At a skip rank k we certify rho <= T_{k+1} = sum_{j>k} x_j with
scaled-integer lower/upper bounds on T_{k+1} at precision P = k + offset
(base offset=260), using m explicit terms (base m=120) plus a rigorous tail
correction, escalating precision up to 3 times if the initial bound is
inconclusive. A certified violation (rho > T_hi at max escalation) is a
FATAL certificate: the greedy has died, hence 1/2 is not in the Mersenne
achievement set. No fatal has ever been observed.

Usage:
    check_half_greedy_margins.py [DEPTH] [TIME_BUDGET_S] [OUT_DIR]
DEPTH defaults to 3000; OUT_DIR defaults to "." and receives
half_greedy_margins_result.json.
"""

problem_id = "erdos_257"

import math
import sys
import time
import json

TARGET_DEPTH = 3000
FALLBACK_DEPTHS = (2000, 1200)
TIME_BUDGET_SECONDS = 300.0
PROGRESS_EVERY = 100
BASE_M = 120
BASE_OFFSET = 260
MAX_ESCALATIONS = 3
NEAR_TIE_THRESHOLD = 6.0

OUT_DIR = "."


# ----------------------------------------------------------------------
# exact-friendly float log2 of arbitrarily large python ints
# ----------------------------------------------------------------------

def log2_bigint(n: int) -> float:
    """Accurate float log2 of a positive python int of any size."""
    if n <= 0:
        return float('-inf')
    b = n.bit_length()
    if b <= 1000:
        return math.log2(n)
    shift = b - 64
    top = n >> shift
    return math.log2(top) + shift


def pow2_nonneg(exp: int) -> int:
    """2**exp for exp >= 0, exact integer. For exp < 0 the true value is a
    positive fraction strictly below the scaled resolution we work at, so as
    an exact-integer contribution to a scaled running sum it is 0 -- see
    certify_skip docstring."""
    return (1 << exp) if exp >= 0 else 0


# ----------------------------------------------------------------------
# skip-rank safety certification
# ----------------------------------------------------------------------

def certify_skip(num: int, den: int, k: int):
    """
    Certify rho = num/den <= T_{k+1} = sum_{j>k} 1/(2^j-1) via scaled-integer
    bounds, escalating precision up to MAX_ESCALATIONS times if inconclusive.

    Returns (status, gap_margin, info):
      status 'safe'       -> gap_margin is a float (see formula below)
      status 'fatal'      -> num*2**P > den*T_hi_scaled even at max escalation
      status 'unresolved' -> exhausted escalations without a decisive bound

    Bound formulas (P = k+offset, m terms, j = k+1..k+m):
      T_lo_scaled = sum_j floor(2**P/(2**j-1))              + 2**(P-(k+m))
      T_hi_scaled = sum_j (floor(2**P/(2**j-1)) + 1)         + 2**(P-(k+m))
                                                              + 2**(P-2*(k+m)+1)
      safe iff  num*2**P <= den*T_lo_scaled
      A = den*T_lo_scaled - num*2**P  (exact positive int on a 'safe' verdict)
      gap_margin = log2(A) - log2(den) - P + 2*k

    NOTE on T_hi_scaled's last term: its exponent (offset - 2m + 1) - k is
    negative for essentially the whole run; evaluating 2**(negative) yields a
    float, and folding that into the exact big-int running sum would silently
    break exactness. It is instead floored to its exact integer value 0 via
    pow2_nonneg() -- provably conservative (can only shrink T_hi_scaled, i.e.
    only ever cause an unnecessary escalation, never a false 'safe'), and the
    final safety certificate is always the exact T_lo_scaled test anyway.
    """
    m = BASE_M
    offset = BASE_OFFSET
    last_info = None
    for attempt in range(MAX_ESCALATIONS + 1):
        P = k + offset
        two_P = 1 << P
        kmax = k + m
        T_lo = 0
        T_hi_terms = 0
        for j in range(k + 1, kmax + 1):
            Mj = (1 << j) - 1
            q = two_P // Mj
            T_lo += q
            T_hi_terms += q + 1
        tail_lo = pow2_nonneg(P - kmax)
        extra_hi = pow2_nonneg(P - 2 * kmax + 1)
        T_lo_scaled = T_lo + tail_lo
        T_hi_scaled = T_hi_terms + tail_lo + extra_hi

        lhs = num << P
        rhs_lo = den * T_lo_scaled
        last_info = dict(m=m, offset=offset, P=P, attempt=attempt)

        if lhs <= rhs_lo:
            A = rhs_lo - lhs
            gap_margin = log2_bigint(A) - log2_bigint(den) - P + 2 * k
            last_info["A_bits"] = A.bit_length()
            return 'safe', gap_margin, last_info

        rhs_hi = den * T_hi_scaled
        if lhs <= rhs_hi:
            m *= 2
            offset *= 2
            continue

        def preview_int(x, head=40, tail=20):
            s = str(x)
            if len(s) <= head + tail + 3:
                return s
            return s[:head] + "..." + s[-tail:] + f"  [{len(s)} digits]"

        last_info.update(
            num_bits=num.bit_length(), den_bits=den.bit_length(),
            T_lo_scaled_bits=T_lo_scaled.bit_length(), T_hi_scaled_bits=T_hi_scaled.bit_length(),
            num_preview=preview_int(num), den_preview=preview_int(den),
        )
        return 'fatal', None, last_info

    return 'unresolved', None, last_info


# ----------------------------------------------------------------------
# mandatory anchor checks (exact, via gcd -- only ever called on small
# numbers at ranks 3, 6, 7, 20, so gcd cost is irrelevant here)
# ----------------------------------------------------------------------

def _reduced(num, den):
    g = math.gcd(num, den)
    return num // g, den // g


def verify_early_anchors(takes, snapshots):
    """Checks the take-set {2,3,6,7} (skips 4,5) and the exact rho values
    1/42 (after {2,3}), 1/126 (after 6), 1/16002 (after 7), plus the
    near-tie take test at 7 using the reduced rho(before 7)=1/126."""
    msgs = []
    ok = True

    takes_2_7 = [t for t in takes if 2 <= t <= 7]
    if takes_2_7 != [2, 3, 6, 7]:
        ok = False
        msgs.append(f"ANCHOR FAIL: takes in [2,7] = {takes_2_7}, expected [2,3,6,7]")
    else:
        msgs.append("anchor OK: takes in ranks 2..7 == {2,3,6,7} (skips 4,5)")

    if 3 in snapshots:
        r = _reduced(*snapshots[3])
        if r != (1, 42):
            ok = False
            msgs.append(f"ANCHOR FAIL: rho after taking {{2,3}} reduces to {r}, expected (1,42)")
        else:
            msgs.append("anchor OK: rho after taking {2,3} == 1/42")
    else:
        ok = False
        msgs.append("ANCHOR FAIL: no snapshot captured at rank 3 (was it not a take?)")

    if 6 in snapshots:
        r6 = _reduced(*snapshots[6])
        if r6 != (1, 126):
            ok = False
            msgs.append(f"ANCHOR FAIL: rho after taking 6 reduces to {r6}, expected (1,126)")
        else:
            msgs.append("anchor OK: rho after taking 6 == 1/126")
            num6, den6 = r6
            lhs7 = num6 * 127
            if lhs7 < den6:
                ok = False
                msgs.append(f"ANCHOR FAIL: take test at 7 on reduced rho(before7)=1/126 failed: {lhs7} < {den6}")
            else:
                msgs.append(f"anchor OK: take test at 7 is the near-tie 1/126 >= 1/127 "
                             f"(127*1={lhs7} >= 126*1={den6}, integer margin {lhs7-den6})")
    else:
        ok = False
        msgs.append("ANCHOR FAIL: no snapshot captured at rank 6 (was it not a take?)")

    if 7 in snapshots:
        r7 = _reduced(*snapshots[7])
        if r7 != (1, 16002):
            ok = False
            msgs.append(f"ANCHOR FAIL: rho after taking 7 reduces to {r7}, expected (1,16002)")
        else:
            msgs.append("anchor OK: rho after 7 == 1/16002")
    else:
        ok = False
        msgs.append("ANCHOR FAIL: no snapshot captured at rank 7 (was it not a take?)")

    return ok, msgs


def verify_take_head_anchor(takes):
    head6 = takes[:6]
    expected = [2, 3, 6, 7, 14, 20]
    if head6 != expected:
        return False, [f"ANCHOR FAIL: take-set head(6) = {head6}, expected {expected}"]
    return True, [f"anchor OK: take-set head == {expected}"]


# ----------------------------------------------------------------------
# main run
# ----------------------------------------------------------------------

def run(depth, time_budget):
    t0 = time.time()
    num, den = 1, 2
    pow2 = 4  # 2^2

    takes = []
    n_skips = 0
    n_takes = 0

    min_gap_margin = None
    min_gap_margin_rank = None
    near_ties = []

    min_take_margin = None
    min_take_margin_rank = None

    fatal_found = False
    fatal_detail = None
    unresolved_ranks = []

    anchors_ok = None
    anchor_msgs = []
    snapshots = {}

    reached_depth = 0
    timed_out = False

    for k in range(2, depth + 1):
        elapsed = time.time() - t0
        if elapsed > time_budget:
            timed_out = True
            break

        Mk = pow2 - 1
        lhs_take = num * Mk
        if lhs_take >= den:
            new_num = lhs_take - den
            new_den = den * Mk
            num, den = new_num, new_den
            takes.append(k)
            n_takes += 1
            if k in (3, 6, 7):
                snapshots[k] = (num, den)
            if num == 0:
                tm = float('-inf')
            else:
                tm = log2_bigint(num) - log2_bigint(den) + 2 * k
            if (min_take_margin is None) or (tm < min_take_margin):
                min_take_margin = tm
                min_take_margin_rank = k
        else:
            n_skips += 1
            status, gap_margin, info = certify_skip(num, den, k)
            if status == 'fatal':
                fatal_found = True
                fatal_detail = dict(rank=k, **info)
                reached_depth = k
                print(f"\n!!! FATAL FOUND at rank {k} !!!  {fatal_detail}\n", flush=True)
                break
            elif status == 'unresolved':
                unresolved_ranks.append((k, info))
                print(f"  [unresolved] skip rank {k}: {info}", flush=True)
            else:
                if (min_gap_margin is None) or (gap_margin < min_gap_margin):
                    min_gap_margin = gap_margin
                    min_gap_margin_rank = k
                if gap_margin < NEAR_TIE_THRESHOLD:
                    near_ties.append((k, gap_margin))

        reached_depth = k

        if k == 7 and not fatal_found:
            ok7, msgs7 = verify_early_anchors(takes, snapshots)
            anchors_ok = ok7
            anchor_msgs = list(msgs7)
            for msg in msgs7:
                print("  " + msg, flush=True)
            if not ok7:
                print("ANCHOR MISMATCH at rank 7 -- STOPPING per mandatory-anchor protocol.", flush=True)
                break

        if k == 20 and not fatal_found and anchors_ok is not False:
            ok20, msgs20 = verify_take_head_anchor(takes)
            anchor_msgs += msgs20
            for msg in msgs20:
                print("  " + msg, flush=True)
            anchors_ok = bool(anchors_ok) and ok20
            if not ok20:
                print("ANCHOR MISMATCH at rank 20 (take-set head) -- STOPPING per mandatory-anchor protocol.", flush=True)
                break

        if k % PROGRESS_EVERY == 0:
            print(f"[progress] k={k} elapsed={elapsed:.1f}s takes={n_takes} skips={n_skips} "
                  f"den_bits={den.bit_length()} num_bits={num.bit_length()} "
                  f"min_gap_margin={min_gap_margin} @rank={min_gap_margin_rank}", flush=True)

        pow2 *= 2

    total_elapsed = time.time() - t0
    return dict(
        depth_requested=depth,
        reached_depth=reached_depth,
        timed_out=timed_out,
        elapsed=total_elapsed,
        num_bits=num.bit_length(),
        den_bits=den.bit_length(),
        takes=takes,
        n_takes=n_takes,
        n_skips=n_skips,
        min_gap_margin=min_gap_margin,
        min_gap_margin_rank=min_gap_margin_rank,
        near_ties=near_ties,
        min_take_margin=min_take_margin,
        min_take_margin_rank=min_take_margin_rank,
        fatal_found=fatal_found,
        fatal_detail=fatal_detail,
        unresolved_ranks=unresolved_ranks,
        anchors_ok=anchors_ok,
        anchor_msgs=anchor_msgs,
    )


def main(target_depth=TARGET_DEPTH, time_budget=TIME_BUDGET_SECONDS):
    print("=== half-greedy Mersenne orbit margin certification ===")
    print(f"target depth = {target_depth}, time budget = {time_budget}s\n")

    result = run(target_depth, time_budget)

    final_depth = result['reached_depth']
    clean_full = (not result['timed_out'] and not result['fatal_found']
                  and result['anchors_ok'] is not False
                  and final_depth == target_depth)

    print("\n=== run summary ===")
    print(f"requested depth: {target_depth}")
    print(f"reached depth:   {final_depth}  ({'completed in full' if clean_full else 'did NOT complete full target'})")
    print(f"timed_out:       {result['timed_out']}")
    print(f"elapsed:         {result['elapsed']:.2f}s")
    print(f"anchors_ok:      {result['anchors_ok']}")
    print(f"fatal_found:     {result['fatal_found']}")
    print(f"n_takes:         {result['n_takes']}")
    print(f"n_skips:         {result['n_skips']}")
    print(f"den bit-length:  {result['den_bits']}")
    print(f"num bit-length:  {result['num_bits']}")
    print(f"min_gap_margin:  {result['min_gap_margin']}  @ rank {result['min_gap_margin_rank']}")
    print(f"min_take_margin: {result['min_take_margin']} @ rank {result['min_take_margin_rank']}")
    print(f"near_ties (<{NEAR_TIE_THRESHOLD}): {result['near_ties']}")
    print(f"unresolved skip ranks: {result['unresolved_ranks']}")
    if result['fatal_found']:
        print(f"FATAL DETAIL: {result['fatal_detail']}")
    print(f"take_head(60): {result['takes'][:60]}")

    if final_depth < target_depth and not result['fatal_found'] and result['anchors_ok'] is not False:
        for tier in FALLBACK_DEPTHS:
            note = "reached" if final_depth >= tier else "NOT reached"
            print(f"fallback tier {tier}: {note}")

    out_path = OUT_DIR + "/half_greedy_margins_result.json"
    with open(out_path, "w") as f:
        json.dump(result, f, indent=2, default=str)
    print(f"\nfull result JSON written to {out_path}")

    return result


if __name__ == "__main__":
    depth_arg = TARGET_DEPTH
    budget_arg = TIME_BUDGET_SECONDS
    if len(sys.argv) > 1:
        try:
            depth_arg = int(sys.argv[1])
        except ValueError:
            pass
    if len(sys.argv) > 2:
        try:
            budget_arg = float(sys.argv[2])
        except ValueError:
            pass
    if len(sys.argv) > 3:
        OUT_DIR = sys.argv[3]
    res = main(depth_arg, budget_arg)
    bad = res['fatal_found'] or (res['anchors_ok'] is False)
    sys.exit(1 if bad else 0)
