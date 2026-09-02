#!/usr/bin/env python3
"""What does the Erdos #249 residue-gap supply actually cost, off the dyadic axis?

Upstream analytic state
-----------------------
`CyclotomicAnchoredKill.lean` proves Erdos #249 *equivalent* to

    FullMersenneCanonicalBasepointResidueGapSupply :=
      for all c, for all odd v > 0, there is H > 0 with phi(v) | H,
      M = (2^H - 1)/v, and  B < (-totientBlock H c) mod M < M - B,
      where B = c + H + 1 and
      totientBlock H N = sum_(j<H) phi(N+1+j) 2^(H-1-j).

So the residue must *avoid* a band of radius `B` around zero -- the easy
direction, satisfied by a proportion `1 - 2B/M` of residues. The producer is
therefore not about finding a rare event; it is about bounding how long one
must wait. The packet measures that wait on one axis only: `v = 1`, the
pure-dyadic case, where the maximum post-clear delay over `c <= C` grows like
`log2 C`, refuting every uniform cap. Every #249 receipt in the corpus is named
`pure_dyadic`. The `v > 1` axis -- the rest of the quantifier -- is unmeasured.

Probe
-----
Two questions.

1. **The v-axis.** Define the *clearing height* `H0(c,v)` as the least positive
   multiple of `phi(v)` with `M > 2B`, below which the admissible arc is empty
   for arithmetic reasons alone, and the *delay* as `(H_min - H0)/phi(v)` in
   admissible steps. Measure `max_(c<=C) delay(c,v)` against `phi(v)`.

2. **The translation.** From the Lean block identity
   `2^H R_c = totientBlock(H,c) + R_(c+H)` with the binary totient tail
   `R_c = sum_(j>=1) phi(c+j) 2^(-j)`, failure at height `H` is
   `dist(totientBlock(H,c), M Z) <= B`, which is
   `|| v * totientBlock(H,c)/(2^H-1) || <= vB/(2^H-1)`, and the block quotient
   is `R_c` up to `O(vc/2^H)` -- the same order as the threshold. So failure at
   `H` should be, up to bounded factors, `||v R_c|| <~ v c 2^(-H)`, giving

       H_min(c,v) = phi(v) * ceil( L(c,v) / phi(v) ) + O(phi(v)),
       L(c,v) = log2( v c / ||v R_c|| ).

   Test that against the exact Lean predicate, then measure `||v R_c||`
   directly. `A_c = sum_(j<=J) phi(c+j) 2^(J-j)` satisfies
   `A_(c+1) = 2 A_c + phi(c+J+1) (mod 2^J)`, so the whole distance sequence is
   one multiply-add per index, and the truncation error `(c+J+2) 2^(-J)` is far
   below any measured distance at `J = 220`.

Predeclared falsifiers
----------------------
* **A `(c,v)` with no admissible `H` below the cap.** The producer is
  Lean-*equivalent* to #249, so a genuine gap would make the series rational.
  This is the outcome that would settle the problem, in the negative.
* **A max-delay law that does not scale as `log2(C)/phi(v)`.** Then the
  Euler-multiple constraint is not the mechanism and the `v` axis carries its
  own obstruction.
* **`H_min` not tracking `phi(v) ceil(L/phi(v))` within one admissible step.**
  Then the Diophantine translation is wrong and the producer does not reduce to
  an irrationality-measure statement for `R_c`.

Validation
----------
On the pure-dyadic axis this must reproduce the packet's own landed witness --
maximum delay 19 at `c = 490794` -- from an implementation written against the
Lean definitions rather than against the earlier scan.

Claim boundary
--------------
Finite computation over a stated range. It does not prove the supply, and a
measured growth law is evidence about what an analytic bound must look like,
not a bound.
"""

from __future__ import annotations

import argparse
import json
import math

TAIL_BITS = 220


def totient_sieve(limit: int) -> list[int]:
    phi = list(range(limit + 1))
    for p in range(2, limit + 1):
        if phi[p] == p:                       # p is prime
            for k in range(p, limit + 1, p):
                phi[k] -= phi[k] // p
    return phi


def euler_phi(n: int) -> int:
    result, m, p = n, n, 2
    while p * p <= m:
        if m % p == 0:
            while m % p == 0:
                m //= p
            result -= result // p
        p += 1
    if m > 1:
        result -= result // m
    return result


def totient_block(phi: list[int], H: int, N: int, modulus: int) -> int:
    """`totientBlock H N` reduced mod `modulus`, by Horner."""
    value = 0
    for j in range(H):
        value = (2 * value + phi[N + 1 + j]) % modulus
    return value


def admissible(phi: list[int], H: int, c: int, v: int) -> bool | None:
    """Lean's `FullMersenneCenteredResidueGap H c M`; None if the arc is empty."""
    mersenne = (1 << H) - 1
    if mersenne % v:
        return None
    modulus = mersenne // v
    band = c + H + 1
    if modulus <= 2 * band:
        return None
    residue = (-totient_block(phi, H, c, modulus)) % modulus
    return band < residue < modulus - band


def least_height(phi: list[int], c: int, v: int, step: int,
                 cap: int) -> tuple[int | None, int | None]:
    """`(H_min, H0)`: least admissible height and least geometrically possible one."""
    clearing = None
    H = step
    while H <= cap:
        verdict = admissible(phi, H, c, v)
        if verdict is not None:
            if clearing is None:
                clearing = H
            if verdict:
                return H, clearing
        H += step
    return None, clearing


def block_identity_check(phi: list[int], H: int, N: int) -> dict:
    """`2^H R_N = totientBlock(H,N) + R_(N+H)` at truncation depth `J`."""
    def tail(c: int) -> int:                  # floor(2^J R_c) exactly
        acc = 0
        for j in range(1, TAIL_BITS + 1):
            acc = 2 * acc + phi[c + j]
        return acc
    block = totient_block(phi, H, N, 1 << (TAIL_BITS + 64))
    left = (1 << H) * tail(N)
    right = (block << TAIL_BITS) + tail(N + H)
    # both sides are floor-truncated at 2^-J, so they agree up to the dropped
    # digits of the block's own tail
    return {"H": H, "N": N, "abs_difference_bits": max(0, (left - right)).bit_length(),
            "truncation_bits": TAIL_BITS,
            "identity_holds_to_truncation": abs(left - right) < (1 << (H + 40))}


def run(max_c: int = 60000, moduli: tuple[int, ...] = (1, 3, 5, 7, 9, 11, 15, 31),
        distance_max_c: int = 200000, cap: int = 400) -> dict:
    limit = max(max_c, distance_max_c) + TAIL_BITS + cap + 16
    phi = totient_sieve(limit)

    identity = [block_identity_check(phi, H, N) for H, N in ((5, 0), (11, 37), (17, 900))]
    if not all(row["identity_holds_to_truncation"] for row in identity):
        raise AssertionError("totientBlock does not satisfy the Lean block identity")

    delay_rows = []
    for v in moduli:
        step = euler_phi(v)
        worst = (-1, None)
        tallest = 0
        for c in range(max_c + 1):
            H, clearing = least_height(phi, c, v, step, cap)
            if H is None:
                return {"status": "producer_gap_found", "c": c, "v": v, "cap": cap,
                        "note": "no admissible height below the cap; this would make "
                                "the series rational and settle Erdos 249 negatively"}
            tallest = max(tallest, H)
            steps = (H - clearing) // step
            if steps > worst[0]:
                worst = (steps, c)
        delay_rows.append({
            "v": v, "phi_v": step, "max_c": max_c,
            "max_delay_steps": worst[0], "argmax_c": worst[1],
            "log2_C_over_phi": math.log2(max_c) / step,
            "max_height": tallest,
        })

    # ||v R_c|| by the incremental recurrence, over a longer range.
    mask = (1 << TAIL_BITS) - 1
    acc = 0
    for j in range(1, TAIL_BITS + 1):
        acc = ((acc << 1) + phi[j]) & mask
    closest = {v: (1 << TAIL_BITS, None) for v in moduli}
    for c in range(distance_max_c + 1):
        for v in moduli:
            x = (v * acc) & mask
            d = min(x, (1 << TAIL_BITS) - x)
            if d < closest[v][0]:
                closest[v] = (d, c)
        acc = ((acc << 1) + phi[c + TAIL_BITS + 1]) & mask

    distance_rows = []
    for v in moduli:
        d, c = closest[v]
        distance_rows.append({
            "v": v, "phi_v": euler_phi(v),
            "neg_log2_min_distance": TAIL_BITS - math.log2(d),
            "argmin_c": c,
            "C_times_min_distance": distance_max_c * d / (1 << TAIL_BITS),
        })

    # Does H_min track phi(v) * ceil(L / phi(v))?
    translation = []
    for v in moduli:
        step = euler_phi(v)
        for c in (5, 50, 500, 5000, min(50000, max_c)):
            H, _ = least_height(phi, c, v, step, cap)
            tail_c = 0
            for j in range(1, TAIL_BITS + 1):
                tail_c = ((tail_c << 1) + phi[c + j]) & mask
            x = (v * tail_c) & mask
            d = min(x, (1 << TAIL_BITS) - x)
            L = math.log2(max(v * c, 1)) + TAIL_BITS - math.log2(d)
            predicted = step * math.ceil(L / step)
            translation.append({
                "v": v, "c": c, "H_min": H, "L": L, "predicted": predicted,
                "steps_off": (H - predicted) / step,
            })
    off = [abs(row["steps_off"]) for row in translation]

    return {
        "status": "supply_present_throughout_range",
        "block_identity_check": identity,
        "delay_law": delay_rows,
        "distance_law": distance_rows,
        "translation": {
            "rows": translation,
            "max_abs_steps_off": max(off),
            "within_one_admissible_step": max(off) <= 1.0,
        },
        "parameters": {"max_c": max_c, "distance_max_c": distance_max_c,
                       "cap": cap, "tail_bits": TAIL_BITS, "moduli": list(moduli)},
    }


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--max-c", type=int, default=60000)
    ap.add_argument("--distance-max-c", type=int, default=200000)
    ap.add_argument("--moduli", default="1,3,5,7,9,11,15,31")
    args = ap.parse_args()
    moduli = tuple(int(x) for x in args.moduli.split(","))
    print(json.dumps(run(args.max_c, moduli, args.distance_max_c),
                     indent=2, default=str))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
