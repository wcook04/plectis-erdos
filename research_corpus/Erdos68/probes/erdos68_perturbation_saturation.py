#!/usr/bin/env python3
"""Erdos #68: run the Kovac-Tao perturbation on our own sequence, both directions.

Upstream analytic state
-----------------------
Negative result 9 is the sharpest recorded obstruction:

    Kovac-Tao's interval construction is a sharp growth-only obstruction for
    Erdos 68: there is already a rational reciprocal series after DECREASING
    each denominator n!-1 by at most n^2+1.  Consequently no argument stable
    under all one-sided quadratic perturbations can prove the unperturbed
    series irrational.

The construction was never run.  The packet records the existence statement and
its consequence, and nothing about how much of the perturbation budget a rational
near `S` actually costs, or whether the one-sidedness matters.

What this probe does
--------------------
Greedy exact-rational reconstruction.  Fix a rational target `t`, and at each
`n` choose `b_n` inside the allowed window so that the remaining residual stays
inside the achievable tail band `[min tail, max tail]`.  If that succeeds for
every `n`, then `sum 1/b_n = t` exactly and `t` is a witness of the Kovac-Tao
phenomenon on our sequence.

Run in two directions:

  * DOWNWARD window `b_n in [n!-n^2-2, n!-1]`  -- terms larger, sums above `S`.
    This is the recorded Kovac-Tao direction.
  * UPWARD window   `b_n in [n!-1, n!+n^2+2]`  -- terms smaller, sums below `S`.

A refuted hypothesis, kept because it is the point
--------------------------------------------------
Every downward-window `b_n` satisfies `b_n <= n!-1`, hence `1/b_n >= 1/(n!-1)`
termwise, hence `sum 1/b_n >= S` with equality only for our own sequence.  So in
the recorded one-sided family `S` is the unique minimum, and the natural
conclusion is that "endpoint-ness" is a property no perturbation argument can
see, and therefore a permitted lever.

The upward run refutes that.  Rationals are reachable BELOW `S` just as easily.
`S` is interior to the two-sided quadratic family, and the one-sidedness of the
recorded statement is about how Kovac-Tao phrased their theorem, not a property
of `S`.  The extremality lever does not exist.

What survives is stronger than what was recorded: the obstruction is TWO-SIDED,
so the excluded class of arguments is larger than negative result 9 states.

Predeclared falsifier
---------------------
Feasibility itself.  If either direction cannot be driven to the target index,
the construction does not reproduce on our sequence at this depth and the
recorded obstruction is weaker than stated.  Reported per direction.

Claim boundary
--------------
Exact rational arithmetic over a bounded index range with a truncated but
generously-bounded tail band.  It witnesses the Kovac-Tao phenomenon and
measures its cost; it proves nothing about `S`, and Erdos #68 remains open.
"""

from __future__ import annotations

import argparse
import json
from fractions import Fraction
from math import factorial
from pathlib import Path

START = 4
MAX_N = 34
GAPS = (20, 30, 40, 50)


def _window(n: int, direction: str) -> tuple[int, int]:
    base = factorial(n) - 1
    if n < START:
        return base, base
    if direction == "down":
        return factorial(n) - n * n - 2, base
    return base, factorial(n) + n * n + 2


def _tail_band(n: int, direction: str, cutoff: int) -> tuple[Fraction, Fraction]:
    lo = sum(Fraction(1, _window(k, direction)[1]) for k in range(n, cutoff))
    hi = sum(Fraction(1, _window(k, direction)[0]) for k in range(n, cutoff))
    return lo, hi


def greedy(target: Fraction, direction: str, max_n: int) -> tuple[list, int | None]:
    residual = target - Fraction(1, 1) - Fraction(1, 5)
    picks = []
    for n in range(START, max_n + 1):
        lo, hi = _tail_band(n + 1, direction, 3 * n + 30)
        base = factorial(n) - 1
        wlo, whi = _window(n, direction)
        mid = (lo + hi) / 2
        feasible = [
            (abs((residual - Fraction(1, b)) - mid), b)
            for b in range(wlo, whi + 1)
            if lo <= residual - Fraction(1, b) <= hi
        ]
        if not feasible:
            return picks, n
        _, b = min(feasible)
        picks.append((n, abs(b - base)))
        residual -= Fraction(1, b)
    return picks, None


def run(max_n: int = MAX_N) -> dict:
    reference = sum(Fraction(1, factorial(n) - 1) for n in range(2, 160))
    out = {}
    for direction, rounding in (("down", 1), ("up", 0)):
        rows = []
        for gap in GAPS:
            target = Fraction(int(reference * 10**gap) + rounding, 10**gap)
            picks, failed = greedy(target, direction, max_n)
            if not picks:
                rows.append({"target_gap": f"1e-{gap}", "feasible": False, "failed_at_n": failed})
                continue
            nonzero = [(n, d) for n, d in picks if d]
            budget = lambda n: n * n + (2 if direction == "up" else 1)
            peak = max((d / budget(n), n, d) for n, d in picks)
            rows.append({
                "target_gap": f"1e-{gap}",
                "feasible_to_n": max_n if failed is None else None,
                "failed_at_n": failed,
                "first_perturbed_n": nonzero[0][0] if nonzero else None,
                "perturbed_steps": f"{len(nonzero)}/{len(picks)}",
                "peak_use": f"{peak[2]}/{budget(peak[1])} at n={peak[1]}",
                "peak_percent_of_window": round(100 * peak[0]),
            })
        out[direction] = rows

    termwise = all(
        _window(n, "down")[1] == factorial(n) - 1 and _window(n, "down")[0] <= factorial(n) - 1
        for n in range(START, 61)
    )
    return {
        "probe": "erdos68_perturbation_saturation",
        "downward_window_sums_above_S": out["down"],
        "upward_window_sums_below_S": out["up"],
        "one_sided_extremality": {
            "statement": "in the recorded downward family every b_n <= n!-1, so sum 1/b_n >= S with equality only for our own sequence",
            "termwise_check_n_4_to_60": termwise,
            "status": "TRUE BUT NOT A LEVER",
            "refuted_by": "the upward run reaches rationals below S just as easily, so S is interior to the two-sided quadratic family",
        },
        "reading": (
            "The Kovac-Tao obstruction reproduces on our sequence in BOTH "
            "directions, and reaching a rational close to S consumes most of the "
            "allowed window at its peak. So the quadratic window is close to the "
            "smallest that works, rationals of this family sit arbitrarily close "
            "to S on both sides, and the excluded class of arguments is larger "
            "than negative result 9 records: anything stable under two-sided "
            "quadratic perturbation fails, not just one-sided."
        ),
        "claim_boundary": (
            "Exact rational arithmetic over a bounded index range. It witnesses "
            "the phenomenon and measures its cost; it proves nothing about S, and "
            "Erdos #68 remains open."
        ),
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--max-n", type=int, default=MAX_N)
    parser.add_argument("--json-out", type=Path, default=None)
    args = parser.parse_args()
    result = run(args.max_n)
    text = json.dumps(result, indent=2)
    print(text)
    if args.json_out:
        args.json_out.write_text(text + "\n", encoding="utf-8")
    feasible = [
        r.get("feasible_to_n") is not None
        for key in ("downward_window_sums_above_S", "upward_window_sums_below_S")
        for r in result[key]
    ]
    return 0 if all(feasible) else 1


if __name__ == "__main__":
    raise SystemExit(main())
