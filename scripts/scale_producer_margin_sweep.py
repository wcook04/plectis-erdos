"""Exact margin sweep for the two reset scale producers.

Middle producer at middle resets s >= 10:
    3*2^((s+5)/2) + 2*(s-2) <= 4*R_s            (dev_s = 4*R_s - pulse_s)
Upper producer at upper resets d >= 10:
    3*2^((d+5)/2) <= E_d = 2^(d+1) - R_(d+1)    (dev_d = -E_d)

Also verifies the derived branch algebra: right <=> 4*R >= 2^(s+1)+pulse+4
among non-carry rows, i.e. every classified middle reset lies strictly below
that boundary.
"""
import json, sys

N = int(sys.argv[1]) if len(sys.argv) > 1 else 12000

remainders = [0] * (N + 2)
branches = ["base"] * (N + 2)
pulses = [0] * (N + 2)
prev = None
for s in range(3, N + 1):
    scale = 1 << (2 * s)
    target = (1 << (2 * s - 1)) - (1 << s)
    rem = target
    bits = bytearray(s + 1)
    for e in range(2, s):
        coin = scale // ((1 << e) - 1)
        if coin <= rem:
            bits[e] = 1
            rem -= coin
    support = {e for e in range(2, s) if bits[e]}
    nscale = 1 << (2 * s + 2)
    pulse = sum(
        nscale // ((1 << e) - 1) - 4 * (scale // ((1 << e) - 1))
        for e in support
    )
    remainders[s] = rem
    pulses[s] = pulse
    if prev is not None:
        if support == prev | {s - 1}:
            branches[s] = "right"
        elif support == prev:
            branches[s] = "middle"
        else:
            branches[s] = "upper"
    prev = support

fails = []
worst = {"middle": None, "upper": None}
algebra_bad = 0
checked = 0
for s in range(10, N):
    b = branches[s + 1]
    thr = 3 * (1 << ((s + 5) // 2))
    right_cond = 4 * remainders[s] >= (1 << (s + 1)) + pulses[s] + 4
    if b != "upper":
        checked += 1
        if b == "middle" and right_cond:
            algebra_bad += 1
        if b == "right" and not right_cond:
            algebra_bad += 1
    if b == "middle":
        lhs = 4 * remainders[s]
        rhs = thr + 2 * (s - 2)
        rec = {"row": s, "slack": lhs - rhs, "lhs": lhs, "rhs": rhs}
        if lhs < rhs:
            fails.append(rec)
        if worst["middle"] is None or rec["slack"] < worst["middle"]["slack"]:
            worst["middle"] = rec
    elif b == "upper":
        E = (1 << (s + 1)) - remainders[s + 1]
        rec = {"row": s, "slack": E - thr, "E": E, "threshold": thr}
        if E < thr:
            fails.append(rec)
        if worst["upper"] is None or rec["slack"] < worst["upper"]["slack"]:
            worst["upper"] = rec

print(json.dumps({
    "schema": "erdos257_scale_producer_margin_v0",
    "rows_checked": N,
    "non_upper_rows_algebra_checked": checked,
    "branch_algebra_mismatches": algebra_bad,
    "producer_failure_count": len(fails),
    "first_failures": fails[:8],
    "worst_slack_by_type_from_row_10": worst,
}, indent=1))
