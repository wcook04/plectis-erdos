#!/usr/bin/env python3
"""check_seam_reset_crossing.py

Exact-integer certificate run for the seam integer-greedy orbit: reset
deviations against the sqrt-scale threshold 2^((r+5)/2), the completed-reset
return-time band 2^r <= |dev_r|*2^L < 2^(r+1), the crossing-cell socket test,
and the affine right-run pullback verification.

Companion measurement layer for
docs/formal_math/erdos257_reset_crossing_unification_2026_07_24.md
(Theorems A/B). Authored by a verification subagent fleet on 2026-07-24 and
promoted after review; the original 2500-row run receipts live in that
document's section 8.

Pure stdlib, exact big-integer arithmetic throughout. The only places floats
appear are log2(|dev|) reporting and the final margin_widths ratio; every
comparison and decision is made on exact Python ints first.

EXACT MODEL (row s >= 6), matching the Lean development
(HalfCylinderIntegerGreedy.lean: truncatedMersenneWeight / seamSubsetTarget):
    w(s,d)   = (4**s) // (2**d - 1)      for d in 2..s-1
    target(s)= 2**(2*s-1) - 2**s
    greedy: acc=0; for d ascending 2..s-1: take d iff acc+w(s,d) <= target(s)
    rem(s)   = target(s) - acc

largest_false(s): scan d from s-1 downward; first d NOT taken.
late(s): 2*s < 3*largest_false(s)

Anchors (run refuses to proceed if any fails): rem(14)=392, rem(15)=34333,
{2,3,6,7} taken and {4,5} absent for every s in 14..40.

Usage:
    check_seam_reset_crossing.py [MAX_ROW] [OUT_DIR]
MAX_ROW defaults to 2500; OUT_DIR defaults to "." and receives
seam_run.jsonl (per-reset and per-crossing ledger rows) and
seam_run_summary.json.
"""
problem_id = "erdos_257"

import json
import math
import sys
import time

TARGET_MAX_ROW = 2500
OUT_DIR = "."
# Hard wall-clock safety net on the main O(row^2) sweep itself (leaves buffer
# for anchor checks + classification + ledger passes + JSONL write).
SWEEP_TIME_BUDGET_SECONDS = 240.0


def safe_log2_abs(n):
    """log2(|n|) for a Python int of any size, without float overflow."""
    n = abs(n)
    if n == 0:
        return None
    try:
        return math.log2(n)
    except OverflowError:
        bl = n.bit_length()
        shift = max(0, bl - 53)
        top = n >> shift
        return math.log2(top) + shift


def build_pow2(n_index):
    """pow2[i] = 2**i for i in 0..n_index (inclusive), built by doubling."""
    pow2 = [1] * (n_index + 1)
    for i in range(1, n_index + 1):
        pow2[i] = pow2[i - 1] * 2
    return pow2


def compute_row_full(s, pow2, denom):
    """Ground-truth row-local greedy at row s (>=6). Returns (rem, taken_set).
    Used only for the mandatory-anchor checks (small s), where we need the
    full taken-set, not just largest_false."""
    pow4s = pow2[2 * s]
    t = pow2[2 * s - 1] - pow2[s]
    acc = 0
    taken = set()
    for d in range(2, s):
        w = pow4s // denom[d]
        if acc + w <= t:
            acc += w
            taken.add(d)
    rem = t - acc
    return rem, taken


def compute_row_fast(s, pow2, denom):
    """Ground-truth row-local greedy at row s (>=6), returning only
    (rem, largest_false) -- tracks the largest not-taken d inline during the
    single ascending pass, avoiding the need to materialize a taken-set."""
    pow4s = pow2[2 * s]
    t = pow2[2 * s - 1] - pow2[s]
    acc = 0
    lf = None
    for d in range(2, s):
        w = pow4s // denom[d]
        if acc + w <= t:
            acc += w
        else:
            lf = d  # d ascends, so the last such assignment is the largest not-taken d
    rem = t - acc
    return rem, lf


def run_anchors(pow2, denom):
    """MANDATORY ANCHORS. Returns (ok: bool, report: dict)."""
    report = {}
    ok = True

    rem14, taken14 = compute_row_full(14, pow2, denom)
    rem15, taken15 = compute_row_full(15, pow2, denom)
    report['rem14'] = rem14
    report['rem15'] = rem15
    report['rem14_expected'] = 392
    report['rem15_expected'] = 34333
    if rem14 != 392:
        ok = False
    if rem15 != 34333:
        ok = False

    pattern_fail_rows = []
    for s in range(14, 41):
        rem_s, taken_s = compute_row_full(s, pow2, denom)
        for must_take in (2, 3, 6, 7):
            if must_take not in taken_s:
                ok = False
                pattern_fail_rows.append((s, 'missing_required', must_take))
        for must_not in (4, 5):
            if must_not in taken_s:
                ok = False
                pattern_fail_rows.append((s, 'unexpectedly_taken', must_not))
    report['pattern_fail_rows'] = pattern_fail_rows
    return ok, report


def main():
    t_wall0 = time.time()
    jsonl_path = OUT_DIR + "/seam_run.jsonl"

    max_row = TARGET_MAX_ROW
    N_INDEX = 2 * max_row + 10
    pow2 = build_pow2(N_INDEX)
    denom = [None] * (max_row + 2)  # denom[d] = 2**d - 1, valid d=2..max_row
    for d in range(2, max_row + 1):
        denom[d] = pow2[d] - 1

    # ---------------- MANDATORY ANCHORS ----------------
    anchors_ok, anchor_report = run_anchors(pow2, denom)
    if not anchors_ok:
        sys.stderr.write("MANDATORY ANCHOR FAILURE -- STOPPING.\n")
        sys.stderr.write(json.dumps(anchor_report, indent=2) + "\n")
        print(json.dumps({"anchors_ok": False, "anchor_report": anchor_report}))
        sys.exit(1)

    print(f"[anchors] OK: rem(14)={anchor_report['rem14']} rem(15)={anchor_report['rem15']} "
          f"pattern {{2,3,6,7}}/{{4,5}} holds for s=14..40", flush=True)

    # ---------------- MAIN SWEEP: rem(s), largest_false(s), late(s) ----------------
    rem_arr = [None] * (max_row + 2)
    lf_arr = [None] * (max_row + 2)
    late_arr = [None] * (max_row + 2)

    t_sweep0 = time.time()
    actual_max_row = max_row
    CHECK_EVERY = 20
    for s in range(6, max_row + 1):
        rem_s, lf_s = compute_row_fast(s, pow2, denom)
        rem_arr[s] = rem_s
        lf_arr[s] = lf_s
        late_arr[s] = (2 * s < 3 * lf_s) if lf_s is not None else None

        if s % CHECK_EVERY == 0:
            elapsed = time.time() - t_sweep0
            if elapsed > SWEEP_TIME_BUDGET_SECONDS:
                actual_max_row = s
                print(f"[sweep] time budget hit at row {s} ({elapsed:.1f}s elapsed); truncating.", flush=True)
                break
    else:
        actual_max_row = max_row

    t_sweep1 = time.time()
    print(f"[sweep] rows 6..{actual_max_row} computed in {t_sweep1 - t_sweep0:.2f}s", flush=True)

    # ---------------- BRANCH CLASSIFICATION for every step s -> s+1 ----------------
    transitions = {}
    n_classification_anomalies = 0
    anomaly_log = []

    for s in range(6, actual_max_row):
        rem_s = rem_arr[s]
        rem_s1 = rem_arr[s + 1]
        lf_s = lf_arr[s]
        lf_s1 = lf_arr[s + 1]
        late_s = late_arr[s]

        rec = {'s': s, 'lf_s': lf_s, 'lf_s1': lf_s1}

        if lf_s is None or lf_s1 is None:
            rec['branch'] = 'ANOMALY_NO_LARGEST_FALSE'
            rec['is_reset'] = False
            n_classification_anomalies += 1
            anomaly_log.append({'s': s, 'reason': 'lf_s or lf_s1 is None', 'lf_s': lf_s, 'lf_s1': lf_s1})
            transitions[s] = rec
            continue

        if lf_s1 == s:
            # RESET
            Delta = rem_s1 - 4 * rem_s - pow2[s + 1]
            rec['Delta'] = Delta
            if -2 * (s + 1) <= Delta <= 0:
                rec['branch'] = 'M'
                rec['belowPulse'] = -Delta
            else:
                E = pow2[s + 1] - rem_s1
                rec['branch'] = 'U'
                rec['E'] = E
                if E <= 0:
                    n_classification_anomalies += 1
                    rec['E_not_positive_anomaly'] = True
                    anomaly_log.append({'s': s, 'reason': 'U-type E<=0', 'E': E})
                if late_s:
                    d = lf_s
                    G3 = 3 * pow2[s + 1] + 2 * pow2[2 * (s - d)] + 4
                    if G3 % 3 != 0:
                        n_classification_anomalies += 1
                        rec['g3_mod3_anomaly'] = True
                        anomaly_log.append({'s': s, 'reason': 'G3 % 3 != 0', 'G3': G3})
                    else:
                        G = G3 // 3
                        overshoot = G - rem_s
                        ap = E - 4 * overshoot
                        rec['G'] = G
                        rec['overshoot'] = overshoot
                        rec['ap'] = ap
                        lo, hi = 0, 2 * (s - 1)
                        if not (lo <= ap <= hi):
                            n_classification_anomalies += 1
                            rec['ap_out_of_range'] = True
                            anomaly_log.append({'s': s, 'reason': 'ap out of [0,2(s-1)]', 'ap': ap, 'hi': hi})
            rec['is_reset'] = True
        elif lf_s1 == lf_s:
            p = 4 * rem_s - pow2[s + 1] - 4 - rem_s1
            rec['branch'] = 'R'
            rec['p'] = p
            rec['is_reset'] = False
            lo, hi = 0, 2 * (s - 1)
            if not (lo <= p <= hi):
                n_classification_anomalies += 1
                rec['r_sanity_anomaly'] = True
                anomaly_log.append({'s': s, 'reason': 'R-sanity p out of [0,2(s-1)]', 'p': p, 'hi': hi})
        else:
            rec['branch'] = 'ANOMALY'
            rec['is_reset'] = False
            n_classification_anomalies += 1
            anomaly_log.append({'s': s, 'reason': 'lf_s1 neither s nor lf_s',
                                 'lf_s': lf_s, 'lf_s1': lf_s1, 'rem_s': rem_s, 'rem_s1': rem_s1})

        transitions[s] = rec

    print(f"[classify] {len(transitions)} transitions classified; "
          f"{n_classification_anomalies} anomalies", flush=True)

    # ---------------- LEDGER 1: RESETS ----------------
    resets = []
    for s in range(6, actual_max_row):
        rec = transitions[s]
        if not rec.get('is_reset'):
            continue
        r = s
        dev = rem_arr[r + 1] - pow2[r + 1]
        log2dev = safe_log2_abs(dev)
        threshold = (r + 5) / 2.0
        margin = (log2dev - threshold) if log2dev is not None else None

        run_len = 0
        j = r + 1
        while j < actual_max_row and transitions.get(j, {}).get('branch') == 'R':
            run_len += 1
            j += 1
        run_end_row = r + 1 + run_len
        # A reset at the final computed transition is also censored even when
        # its observed R-run currently has length zero: row `actual_max_row`
        # has no classified outgoing branch, so the run's true endpoint is
        # unknown.
        run_truncated_by_max_row = (j >= actual_max_row)

        reached_crossing = False
        crossing_row_found = None
        for rr in range(r + 1, min(run_end_row, actual_max_row) + 1):
            dd = lf_arr[rr]
            if dd is None:
                continue
            if late_arr[rr] and (3 * dd in (2 * rr + 1, 2 * rr + 2)):
                reached_crossing = True
                crossing_row_found = rr
                break

        entry = {
            'kind': 'reset',
            'row': r,
            'type': rec['branch'],
            'd_new': r,
            'rem_r': rem_arr[r],
            'rem_r1': rem_arr[r + 1],
            'dev': dev,
            'log2_abs_dev': log2dev,
            'threshold': threshold,
            'margin': margin,
            'run_len': run_len,
            'run_rows_span': run_len + 1,
            'run_truncated_by_max_row': run_truncated_by_max_row,
            'reached_crossing': reached_crossing,
            'crossing_row': crossing_row_found,
        }
        if not run_truncated_by_max_row:
            scaled_abs_dev = abs(dev) * pow2[run_len]
            right_run_charge = 0
            for step in range(run_len):
                right_row = r + 1 + step
                right_run_charge = 4 * right_run_charge + transitions[right_row]['p'] + 4
            terminal_reset_row = r + run_len + 1
            terminal_packet = rem_arr[terminal_reset_row] + right_run_charge
            entry['return_time_scaled_abs_dev'] = scaled_abs_dev
            entry['return_time_band_lower_holds'] = (pow2[r] <= scaled_abs_dev)
            entry['return_time_band_strict_lower_holds'] = (pow2[r] < scaled_abs_dev)
            entry['return_time_band_upper_holds'] = (scaled_abs_dev < pow2[r + 1])
            entry['return_time_band_holds'] = (
                entry['return_time_band_lower_holds']
                and entry['return_time_band_upper_holds']
            )
            entry['floor_log2_abs_dev'] = abs(dev).bit_length() - 1 if dev != 0 else None
            entry['floor_log2_abs_dev_eq_row_sub_run_len'] = (
                dev != 0 and entry['floor_log2_abs_dev'] == r - run_len
            )
            entry['right_run_charge'] = right_run_charge
            entry['terminal_reset_row'] = terminal_reset_row
            entry['terminal_reset_type'] = transitions[terminal_reset_row]['branch']
            entry['terminal_packet'] = terminal_packet
            entry['terminal_packet_half_boundary'] = pow2[r + run_len]
            entry['terminal_packet_lt_half'] = (terminal_packet < pow2[r + run_len])
            entry['terminal_packet_half_margin'] = pow2[r + run_len] - terminal_packet
            if rec['branch'] == 'U':
                # Exact lower envelope selected by
                # FatalCriticalDangerEndpointReduction.lean.  A fatal borrow
                # emits an actual last-upper/right-run block with the strict
                # reverse inequality, so an all-depth proof of this predicate
                # for the relevant blocks would close that fatal socket.
                linear_envelope = (4 ** run_len) * (2 * (r + run_len))
                entry['terminal_packet_linear_envelope'] = linear_envelope
                entry['terminal_packet_ge_linear_envelope'] = (
                    linear_envelope <= terminal_packet
                )
                entry['terminal_packet_linear_envelope_slack'] = (
                    terminal_packet - linear_envelope
                )
                prefix_charge = 0
                prefix_rows = []
                for prefix_len in range(run_len + 1):
                    prefix_packet = rem_arr[r + prefix_len + 1] + prefix_charge
                    prefix_envelope = (
                        (4 ** prefix_len) * (2 * (r + prefix_len))
                    )
                    scaled_gap = (4 ** prefix_len) * (
                        pow2[r - prefix_len + 1] - rec['E']
                    )
                    prefix_rows.append({
                        'run_prefix_len': prefix_len,
                        'packet': prefix_packet,
                        'linear_envelope': prefix_envelope,
                        'slack': prefix_packet - prefix_envelope,
                        'exact_scaled_gap_identity_holds': (
                            prefix_packet == scaled_gap
                        ),
                    })
                    if prefix_len < run_len:
                        right_row = r + prefix_len + 1
                        prefix_charge = (
                            4 * prefix_charge + transitions[right_row]['p'] + 4
                        )
                minimum_prefix = min(prefix_rows, key=lambda row: row['slack'])
                entry['upper_right_prefix_count'] = len(prefix_rows)
                entry['upper_right_prefix_linear_envelope_violation_count'] = sum(
                    row['slack'] < 0 for row in prefix_rows
                )
                entry['upper_right_prefix_linear_envelope_equality_count'] = sum(
                    row['slack'] == 0 for row in prefix_rows
                )
                entry['upper_right_prefix_scaled_gap_identity_failure_count'] = sum(
                    not row['exact_scaled_gap_identity_holds'] for row in prefix_rows
                )
                entry['minimum_upper_right_prefix_linear_envelope_slack'] = (
                    minimum_prefix['slack']
                )
                entry['minimum_upper_right_prefix_linear_envelope_run_len'] = (
                    minimum_prefix['run_prefix_len']
                )
        if rec['branch'] == 'U':
            entry['E'] = rec['E']
            entry['dev_eq_negE'] = (dev == -rec['E'])
        else:
            entry['belowPulse'] = rec['belowPulse']
        resets.append(entry)

    resets_r_ge_14 = [e for e in resets if e['row'] >= 14 and e['margin'] is not None]
    if resets_r_ge_14:
        min_margin_entry = min(resets_r_ge_14, key=lambda e: e['margin'])
        min_reset_margin_log2 = min_margin_entry['margin']
        min_reset_margin_row = min_margin_entry['row']
    else:
        min_reset_margin_log2 = None
        min_reset_margin_row = None

    print(f"[resets] {len(resets)} resets found "
          f"(U={sum(1 for e in resets if e['type']=='U')}, "
          f"M={sum(1 for e in resets if e['type']=='M')})", flush=True)

    # A completed reset is one whose following R-run terminates before the
    # finite horizon.  The row-7 startup reset is retained in the ledger but
    # excluded from the mature-band statistic: the exact band begins at the
    # next completed reset, row 13, in the audited orbit.
    completed_resets = [e for e in resets if not e['run_truncated_by_max_row']]
    mature_completed_resets = [e for e in completed_resets if e['row'] >= 13]
    return_time_band_violations = [
        e for e in mature_completed_resets if not e['return_time_band_holds']
    ]
    return_time_floor_identity_violations = [
        e for e in mature_completed_resets
        if not e['floor_log2_abs_dev_eq_row_sub_run_len']
    ]
    return_time_strict_band_violations = [
        e for e in mature_completed_resets
        if not (e['return_time_band_strict_lower_holds']
                and e['return_time_band_upper_holds'])
    ]
    upper_reset_critical_index_violations = [
        e for e in mature_completed_resets
        if e['type'] == 'U'
        and not (e['run_len'] <= e['row']
                 and pow2[e['row'] - e['run_len']] < abs(e['dev'])
                 and abs(e['dev']) <= pow2[e['row'] - e['run_len'] + 1])
    ]
    upper_reset_endpoint_packet_violations = [
        e for e in mature_completed_resets
        if e['type'] == 'U' and not e['terminal_packet_lt_half']
    ]
    completed_upper_resets = [
        e for e in mature_completed_resets if e['type'] == 'U'
    ]
    upper_reset_linear_envelope_violations = [
        e for e in completed_upper_resets
        if not e['terminal_packet_ge_linear_envelope']
    ]
    upper_reset_linear_envelope_equalities = [
        e for e in completed_upper_resets
        if e['terminal_packet_linear_envelope_slack'] == 0
    ]
    if completed_upper_resets:
        minimum_linear_envelope_entry = min(
            completed_upper_resets,
            key=lambda e: e['terminal_packet_linear_envelope_slack'],
        )
        minimum_linear_envelope_slack = (
            minimum_linear_envelope_entry['terminal_packet_linear_envelope_slack']
        )
        minimum_linear_envelope_row = minimum_linear_envelope_entry['row']
        minimum_linear_envelope_run_len = minimum_linear_envelope_entry['run_len']
    else:
        minimum_linear_envelope_slack = None
        minimum_linear_envelope_row = None
        minimum_linear_envelope_run_len = None
    upper_right_prefix_count = sum(
        e['upper_right_prefix_count'] for e in completed_upper_resets
    )
    upper_right_prefix_linear_envelope_violation_count = sum(
        e['upper_right_prefix_linear_envelope_violation_count']
        for e in completed_upper_resets
    )
    upper_right_prefix_linear_envelope_equality_count = sum(
        e['upper_right_prefix_linear_envelope_equality_count']
        for e in completed_upper_resets
    )
    upper_right_prefix_scaled_gap_identity_failure_count = sum(
        e['upper_right_prefix_scaled_gap_identity_failure_count']
        for e in completed_upper_resets
    )
    if completed_upper_resets:
        minimum_prefix_entry = min(
            completed_upper_resets,
            key=lambda e: e['minimum_upper_right_prefix_linear_envelope_slack'],
        )
        minimum_prefix_linear_envelope_slack = (
            minimum_prefix_entry['minimum_upper_right_prefix_linear_envelope_slack']
        )
        minimum_prefix_linear_envelope_row = minimum_prefix_entry['row']
        minimum_prefix_linear_envelope_run_len = (
            minimum_prefix_entry['minimum_upper_right_prefix_linear_envelope_run_len']
        )
    else:
        minimum_prefix_linear_envelope_slack = None
        minimum_prefix_linear_envelope_row = None
        minimum_prefix_linear_envelope_run_len = None
    reset_type_alternation_failures = []
    for previous, current in zip(resets, resets[1:]):
        if previous['type'] == current['type']:
            reset_type_alternation_failures.append((previous['row'], current['row'], current['type']))
    reset_sign_type_failures = [
        e for e in resets
        if not ((e['type'] == 'U' and e['dev'] < 0)
                or (e['type'] == 'M' and e['dev'] > 0))
    ]
    longest_completed_runs = sorted(
        completed_resets, key=lambda e: (-e['run_len'], e['row'])
    )[:8]

    print(f"[return-time] mature completed resets={len(mature_completed_resets)}; "
          f"band violations={len(return_time_band_violations)}; "
          f"strict-band violations={len(return_time_strict_band_violations)}; "
          f"floor-identity violations={len(return_time_floor_identity_violations)}; "
          f"upper critical-index violations={len(upper_reset_critical_index_violations)}; "
          f"upper endpoint-packet violations={len(upper_reset_endpoint_packet_violations)}; "
          f"upper linear-envelope violations={len(upper_reset_linear_envelope_violations)}; "
          f"upper prefix linear-envelope violations="
          f"{upper_right_prefix_linear_envelope_violation_count}; "
          f"alternation failures={len(reset_type_alternation_failures)}; "
          f"sign/type failures={len(reset_sign_type_failures)}", flush=True)

    # ---------------- LEDGER 2/3/4: CROSSINGS ----------------
    crossings = []
    socket_violations = 0
    affine_iterate_verified = True
    min_pullback_margin_widths = None

    for s in range(6, actual_max_row):
        d = lf_arr[s]
        if d is None or not late_arr[s]:
            continue
        threeD = 3 * d
        if threeD not in (2 * s + 1, 2 * s + 2):
            continue

        parity = 'odd' if threeD == 2 * s + 1 else 'even'
        branch_at_s = transitions[s]['branch']
        socket_violation = (branch_at_s == 'R')
        if socket_violation:
            socket_violations += 1
            sys.stderr.write(f"*** SOCKET VIOLATION at s={s}, d={d}: branch=R at a crossing cell! "
                              f"rem(s)={rem_arr[s]}\n")

        rem_s = rem_arr[s]

        # ---- Ledger 3: R-WINDOW (exact integer test, original rem form) ----
        cond_i = (pow2[s + 1] + 4 <= 4 * rem_s)
        RHS = 4 * (3 * pow2[s + 1] + 2 * pow2[2 * (s - d)] + 4) + 6 * (s - 2)
        LHS = 12 * rem_s + 3 * pow2[s + 1]
        cond_ii = (LHS < RHS)
        in_window = cond_i and cond_ii

        entry = {
            'kind': 'crossing',
            'row': s,
            's': s,
            'd': d,
            'parity': parity,
            'branch_at_s': branch_at_s,
            'socket_violation': socket_violation,
            'rem_s': rem_s,
            'r_window_cond_i': cond_i,
            'r_window_cond_ii': cond_ii,
            'in_window': in_window,
        }

        # ---- Ledger 4: AFFINE PULLBACK CHECK ----
        L = s - d - 1
        C = 0
        run_all_R = True
        for j in range(d + 1, s):
            rem_j = rem_arr[j]
            rem_j1 = rem_arr[j + 1]
            p_j = 4 * rem_j - pow2[j + 1] - 4 - rem_j1
            C = 4 * C + p_j + 4
            tj = transitions.get(j)
            if tj is None or tj.get('branch') != 'R':
                run_all_R = False

        w_d1 = rem_arr[d + 1] - pow2[d + 1]
        w_s = rem_s - pow2[s]
        X = (4 ** L) * w_d1 - C
        affine_ok = (X == w_s)
        if not affine_ok:
            affine_iterate_verified = False

        entry['L'] = L
        entry['C'] = C
        entry['run_all_R'] = run_all_R
        entry['w_d1'] = w_d1
        entry['w_s'] = w_s
        entry['affine_identity_holds'] = affine_ok

        # pullback window for w(d+1): [(lo_s+C)/4^L, (hi_s+C)/4^L]
        lo_s = -(-(pow2[s + 1] + 4) // 4) - pow2[s]
        Y = RHS - 3 * pow2[s + 1]
        hi_s_rem = (Y - 1) // 12
        hi_s = hi_s_rem - pow2[s]

        w_bounds_in_window = (lo_s <= w_s <= hi_s)
        entry['lo_s'] = lo_s
        entry['hi_s'] = hi_s
        entry['w_bounds_matches_in_window'] = (w_bounds_in_window == in_window)

        if X < lo_s:
            dist_scaled = lo_s - X
        elif X > hi_s:
            dist_scaled = X - hi_s
        else:
            dist_scaled = 0
        width_scaled = hi_s - lo_s
        if width_scaled != 0:
            margin_widths = dist_scaled / width_scaled
        else:
            margin_widths = float('inf') if dist_scaled > 0 else 0.0

        entry['dist_scaled'] = dist_scaled
        entry['width_scaled'] = width_scaled
        entry['margin_widths'] = margin_widths

        if min_pullback_margin_widths is None or margin_widths < min_pullback_margin_widths:
            min_pullback_margin_widths = margin_widths

        crossings.append(entry)

    print(f"[crossings] {len(crossings)} crossings found; "
          f"socket_violations={socket_violations}; "
          f"affine_iterate_verified={affine_iterate_verified}", flush=True)

    # ---------------- WRITE LEDGER JSONL (row-order merged) ----------------
    combined = resets + crossings
    combined.sort(key=lambda e: (e['row'], 0 if e['kind'] == 'reset' else 1))
    with open(jsonl_path, 'w') as f:
        for e in combined:
            f.write(json.dumps(e) + "\n")

    # ---------------- crossing_sample string ----------------
    def fmt_row(e):
        return f"{e['s']:>6} {e['d']:>6}  {e['parity']:<5} {e['branch_at_s']:<3}"

    header = f"{'s':>6} {'d':>6}  {'par':<5} {'br':<3}"
    lines = [header]
    if len(crossings) <= 18:
        for e in crossings:
            lines.append(fmt_row(e))
    else:
        for e in crossings[:12]:
            lines.append(fmt_row(e))
        lines.append("   ...   ...   ...   ...")
        for e in crossings[-6:]:
            lines.append(fmt_row(e))
    crossing_sample = "\n".join(lines)

    # ---------------- notes ----------------
    n_resets = len(resets)
    n_u = sum(1 for e in resets if e['type'] == 'U')
    n_m = sum(1 for e in resets if e['type'] == 'M')
    dev_signs = {'neg': sum(1 for e in resets if e['dev'] < 0),
                 'pos': sum(1 for e in resets if e['dev'] > 0),
                 'zero': sum(1 for e in resets if e['dev'] == 0)}
    small_dev_resets = sorted(resets, key=lambda e: abs(e['dev']))[:5]
    reached_crossing_count = sum(1 for e in resets if e['reached_crossing'])

    in_window_at_crossing_count = sum(1 for e in crossings if e['in_window'])
    min_in_window_margin = None
    not_in_window = [e for e in crossings if not e['in_window']]
    if not_in_window:
        closest = min(not_in_window, key=lambda e: e['margin_widths'])
        min_in_window_margin = closest['margin_widths']

    crossing_gaps = [crossings[i + 1]['s'] - crossings[i]['s'] for i in range(len(crossings) - 1)]
    gap_summary = {}
    if crossing_gaps:
        from collections import Counter
        gap_counts = Counter(crossing_gaps)
        gap_summary = dict(sorted(gap_counts.items(), key=lambda kv: -kv[1])[:8])

    total_wall = time.time() - t_wall0

    notes_parts = []
    notes_parts.append(f"anchors verified (rem14=392, rem15=34333, {{2,3,6,7}} taken / {{4,5}} absent s=14..40).")
    notes_parts.append(f"rows computed: 6..{actual_max_row} (target was {TARGET_MAX_ROW}); "
                        f"total wall time {total_wall:.1f}s.")
    notes_parts.append(f"resets: {n_resets} total ({n_u} type U, {n_m} type M). "
                        f"dev sign split: {dev_signs['neg']} negative, {dev_signs['pos']} positive, "
                        f"{dev_signs['zero']} zero.")
    notes_parts.append(
        f"completed-reset return-time band: {len(mature_completed_resets)} mature resets (r>=13), "
        f"{len(return_time_band_violations)} violations of "
        f"2^r<=|dev_r|*2^L<2^(r+1), and "
        f"{len(return_time_floor_identity_violations)} violations of "
        f"floor(log2|dev_r|)=r-L."
    )
    notes_parts.append(
        f"strict completed-reset band violations={len(return_time_strict_band_violations)}; "
        f"upper-reset critical-index violations={len(upper_reset_critical_index_violations)}; "
        f"upper-reset endpoint-packet violations={len(upper_reset_endpoint_packet_violations)}; "
        f"upper-reset linear-envelope violations={len(upper_reset_linear_envelope_violations)}; "
        f"equalities={len(upper_reset_linear_envelope_equalities)}; "
        f"all-prefix violations={upper_right_prefix_linear_envelope_violation_count} "
        f"and equalities={upper_right_prefix_linear_envelope_equality_count} "
        f"across {upper_right_prefix_count} prefixes; "
        f"scaled-gap identity failures="
        f"{upper_right_prefix_scaled_gap_identity_failure_count}."
    )
    if minimum_linear_envelope_slack is not None:
        notes_parts.append(
            f"minimum exact upper-reset linear-envelope slack="
            f"{minimum_linear_envelope_slack} at row {minimum_linear_envelope_row} "
            f"with run length {minimum_linear_envelope_run_len}."
        )
    if minimum_prefix_linear_envelope_slack is not None:
        notes_parts.append(
            f"minimum exact all-prefix upper/right linear-envelope slack="
            f"{minimum_prefix_linear_envelope_slack} at source row "
            f"{minimum_prefix_linear_envelope_row} and prefix length "
            f"{minimum_prefix_linear_envelope_run_len}."
        )
    notes_parts.append(
        f"reset alternation failures={len(reset_type_alternation_failures)}; "
        f"reset sign/type failures={len(reset_sign_type_failures)}."
    )
    if longest_completed_runs:
        longest = ", ".join(
            f"r={e['row']}({e['type']},L={e['run_len']})"
            for e in longest_completed_runs
        )
        notes_parts.append(f"longest completed following R-runs: {longest}.")
    if small_dev_resets:
        sd = ", ".join(f"row={e['row']}({e['type']}, dev={e['dev']})" for e in small_dev_resets)
        notes_parts.append(f"smallest |dev| resets: {sd}.")
    if min_reset_margin_row is not None:
        notes_parts.append(f"min reset margin (log2 scale, r>=14): {min_reset_margin_log2:.4f} "
                            f"at row {min_reset_margin_row} "
                            f"(type={next(e['type'] for e in resets if e['row']==min_reset_margin_row)}).")
    notes_parts.append(f"crossings: n_crossings={len(crossings)}; "
                        f"of which {reached_crossing_count} resets' following R-run reached a crossing cell; "
                        f"{in_window_at_crossing_count}/{len(crossings)} crossings had rem(s) inside the R-window.")
    if min_in_window_margin is not None:
        notes_parts.append(f"closest a NOT-in-window crossing came to the R-window boundary: "
                            f"{min_in_window_margin:.6f} interval-widths.")
    notes_parts.append(f"socket violations (branch==R at a crossing): {socket_violations}.")
    notes_parts.append(f"affine_iterate_verified={affine_iterate_verified} across all {len(crossings)} crossings.")
    if min_pullback_margin_widths is not None:
        notes_parts.append(f"min pullback margin_widths across crossings: {min_pullback_margin_widths:.6f}.")
    if gap_summary:
        notes_parts.append(f"crossing-row gap histogram (top): {gap_summary}.")
    if n_classification_anomalies:
        notes_parts.append(f"*** {n_classification_anomalies} classification anomalies logged -- inspect before "
                            f"trusting downstream structure. ***")
        for a in anomaly_log[:10]:
            notes_parts.append(f"  anomaly: {a}")
    else:
        notes_parts.append("zero classification anomalies over the full sweep.")

    notes = " ".join(notes_parts)

    summary = {
        'max_row': actual_max_row,
        'anchors_ok': anchors_ok,
        'n_resets': n_resets,
        'n_crossings': len(crossings),
        'socket_violations': socket_violations,
        'affine_iterate_verified': affine_iterate_verified,
        'min_reset_margin_log2': min_reset_margin_log2,
        'min_reset_margin_row': min_reset_margin_row,
        'min_crossing_pullback_margin_widths': min_pullback_margin_widths,
        'n_classification_anomalies': n_classification_anomalies,
        'n_mature_completed_resets': len(mature_completed_resets),
        'return_time_band_violation_count': len(return_time_band_violations),
        'return_time_strict_band_violation_count': len(return_time_strict_band_violations),
        'return_time_floor_identity_violation_count': len(return_time_floor_identity_violations),
        'upper_reset_critical_index_violation_count': len(upper_reset_critical_index_violations),
        'upper_reset_endpoint_packet_violation_count': len(upper_reset_endpoint_packet_violations),
        'n_mature_completed_upper_resets': len(completed_upper_resets),
        'upper_reset_linear_envelope_violation_count': len(upper_reset_linear_envelope_violations),
        'upper_reset_linear_envelope_equality_count': len(upper_reset_linear_envelope_equalities),
        'minimum_upper_reset_linear_envelope_slack': minimum_linear_envelope_slack,
        'minimum_upper_reset_linear_envelope_row': minimum_linear_envelope_row,
        'minimum_upper_reset_linear_envelope_run_len': minimum_linear_envelope_run_len,
        'upper_right_prefix_count': upper_right_prefix_count,
        'upper_right_prefix_linear_envelope_violation_count': upper_right_prefix_linear_envelope_violation_count,
        'upper_right_prefix_linear_envelope_equality_count': upper_right_prefix_linear_envelope_equality_count,
        'upper_right_prefix_scaled_gap_identity_failure_count': upper_right_prefix_scaled_gap_identity_failure_count,
        'minimum_upper_right_prefix_linear_envelope_slack': minimum_prefix_linear_envelope_slack,
        'minimum_upper_right_prefix_linear_envelope_row': minimum_prefix_linear_envelope_row,
        'minimum_upper_right_prefix_linear_envelope_run_len': minimum_prefix_linear_envelope_run_len,
        'reset_type_alternation_failure_count': len(reset_type_alternation_failures),
        'reset_sign_type_failure_count': len(reset_sign_type_failures),
        'longest_completed_runs': [
            {'row': e['row'], 'type': e['type'], 'run_len': e['run_len']}
            for e in longest_completed_runs
        ],
        'crossing_sample': crossing_sample,
        'jsonl_path': jsonl_path,
        'script_path': __file__,
        'notes': notes,
        'wall_time_seconds': total_wall,
    }

    with open(OUT_DIR + "/seam_run_summary.json", 'w') as f:
        json.dump(summary, f, indent=2)

    print("\n=== SUMMARY ===")
    print(json.dumps({k: v for k, v in summary.items() if k not in ('notes', 'crossing_sample')}, indent=2))
    print("\ncrossing_sample:\n" + crossing_sample)
    print("\nnotes:\n" + notes)

    return summary


if __name__ == "__main__":
    if len(sys.argv) > 1:
        TARGET_MAX_ROW = int(sys.argv[1])
    if len(sys.argv) > 2:
        OUT_DIR = sys.argv[2]
    main()
