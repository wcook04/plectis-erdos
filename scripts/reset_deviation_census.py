"""Reset deviation census: how far do actual resets stay from the zero-deviation window?

For every row s (3..N) compute the seam-greedy state:
    R_s   = T_s - sum_{e in S_s} floor(2^(2s)/(2^e - 1)),  T_s = 2^(2s-1) - 2^s
    X_s   = R_s - 2^s
    branch into s+1: right (take s), middle (keep support), upper (support jump)

Danger windows (from HalfCylinderResetSqrtEscape obligations):
    upper reset at s: dev_s = X_{s+1} = -E must satisfy E > 2^((s+5)/2)
    middle reset at s: dev_s = 4 X_s + 2^(s+1) - pulse_s must satisfy |dev_s| > 2^((s+5)/2)
Small |dev_s| at a middle reset forces X_s ~= -2^(s-1), i.e. R_s ~= 2^(s-1).
We measure the exact margin of every reset against its window and the record-close approaches.
"""

import json
import sys
import time

N = int(sys.argv[1]) if len(sys.argv) > 1 else 12000

t0 = time.time()
remainders = [0] * (N + 2)
excesses = [0] * (N + 2)          # X_s
branches = ["base"] * (N + 2)     # branch taken entering row s+1
pulses = [0] * (N + 2)            # belowPulse_s = sum of rowPulse(s, e) over support
cards = [0] * (N + 2)

prev_support = None
support = set()
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
    # belowPulse_s = sum_e rowPulse(s, e); rowPulse(s,e) = w_{s+1}(e) - 4*w_s(e)
    ns = s + 1
    nscale = 1 << (2 * ns)
    pulse = 0
    for e in support:
        w_s = nscale // ((1 << e) - 1) // 4  # careful: compute exactly below
    # compute pulse exactly: w_{s+1}(e) - 4 w_s(e)
    pulse = 0
    for e in support:
        w_s = scale // ((1 << e) - 1)
        w_s1 = nscale // ((1 << e) - 1)
        pulse += w_s1 - 4 * w_s
    remainders[s] = rem
    excesses[s] = rem - (1 << s)
    pulses[s] = pulse
    cards[s] = len(support)
    if prev_support is not None:
        if support == prev_support | {s - 1}:
            branches[s] = "right"
        elif support == prev_support:
            branches[s] = "middle"
        else:
            branches[s] = "upper"
    prev_support = support

# classify reset rows: s is a reset row iff branch entering s+1 is middle/upper
resets = []
for s in range(3, N):
    b = branches[s + 1]
    if b == "right":
        continue
    X_s = excesses[s]
    X_next = remainders[s + 1] - (1 << (s + 1))
    dev = X_next
    typ = b
    half = (s + 5) // 2
    threshold = 1 << half
    absdev = abs(dev)
    margin_bits = absdev.bit_length() - 1 - half  # floor(log2|dev|) - (s+5)//2
    resets.append(
        {
            "row": s,
            "type": typ,
            "X_s": X_s,
            "dev_s": dev,
            "pulse": pulses[s],
            "floor_log_dev": absdev.bit_length() - 1,
            "margin_over_sqrt": margin_bits,
            "danger_dist_middle": (
                abs(X_s + (1 << (s - 1))) if typ == "middle" else None
            ),
        }
    )

# summary
n_upper = sum(1 for r in resets if r["type"] == "upper")
n_middle = sum(1 for r in resets if r["type"] == "middle")
worst_margin = {}
for typ in ("upper", "middle"):
    rows = [r for r in resets if r["type"] == typ and r["row"] >= 14]
    if rows:
        wm = min(rows, key=lambda r: (r["margin_over_sqrt"], r["row"]))
        worst_margin[typ] = wm

# middle-danger distances: how close R_s gets to 2^(s-1) at middle resets
mid_rows = [r for r in resets if r["type"] == "middle" and r["row"] >= 14]
closest_danger = None
if mid_rows:
    closest_danger = min(
        mid_rows, key=lambda r: (r["danger_dist_middle"], r["row"])
    )

# empirical law hunt: floor(log2|dev|) vs row
law_counts = {}
for r in resets:
    if r["row"] < 14:
        continue
    gap = r["row"] - r["floor_log_dev"]
    law_counts[gap] = law_counts.get(gap, 0) + 1

out = {
    "schema": "erdos257_reset_deviation_census_v0",
    "rows_checked": N,
    "elapsed_seconds": round(time.time() - t0, 1),
    "reset_count": len(resets),
    "upper_count": n_upper,
    "middle_count": n_middle,
    "worst_margin_by_type_from_row_14": worst_margin,
    "closest_middle_danger_approach_from_row_14": closest_danger,
    "floor_log_dev_gap_histogram": dict(
        sorted(law_counts.items())[:40]
    ),
    "first_resets": resets[:24],
}
print(json.dumps(out, indent=1))
