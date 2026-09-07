"""Wave-8 decisive scan: A*(r) = min{A : C_{p_r}(A) odd} along CF(log_2 3).

Refutes the wave-7 inference that the odd witness sits at a constant level.
Everything is exact: certified rational brackets + integer floor sums.
"""
import collections, json, sys
import exact

NCONV = int(sys.argv[1]) if len(sys.argv) > 1 else 1200
AMAX = 40

conv = exact.convergents(exact.ALPHA_LO, exact.ALPHA_HI, NCONV)
rows, uncert = [], 0
for r, (n, p) in enumerate(conv):
    astar = None
    for A in range(0, AMAX):
        v = exact.C_p(p, A, n)
        if v is None:
            uncert += 1
            break
        if v % 2 == 1:
            astar = A
            break
    rows.append((r, astar))

star = [a for _, a in rows if a is not None]
cnt = collections.Counter(star)
N = len(star)
# chi^2 only over cells whose expected count is large enough to be meaningful
CELLS = [k for k in range(0, 40) if N * 2.0 ** -(k + 1) >= 4]
chi = sum((cnt.get(k, 0) - N * 2.0 ** -(k + 1)) ** 2 / (N * 2.0 ** -(k + 1))
          for k in CELLS)
w7 = [a for r, a in rows[:86] if a is not None]

out = {
    "certified_convergents": len(conv),
    "uncertified": uncert,
    "astar_histogram": dict(sorted(cnt.items())),
    "astar_max": max(star),
    "astar_gt5_indices": [(r, a) for r, a in rows if a is not None and a > 5],
    "geometric_half_chi2": round(chi, 3),
    "geometric_half_chi2_cells": len(CELLS),
    "wave7_horizon_r_le_85": {
        "max": max(w7), "mean": round(sum(w7) / len(w7), 3),
        "le2_count": sum(1 for a in w7 if a <= 2), "n": len(w7),
    },
}
print(json.dumps(out, indent=2))
json.dump(rows, open("astar_rows.json", "w"))
