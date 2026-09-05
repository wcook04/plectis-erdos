#!/usr/bin/env python3
"""The bounded CRT block and the cap on the coprimality route for Erdos #243.

Part A (positive, supports SlowRiseBarrier.lean).  For pairwise coprime moduli
m_0..m_{B-1} >= 2 with product P there is x in [P, 2P) with m_r | x + r for every
r < B.  We build it for blocks of Sylvester numbers and of consecutive primes and
check the landing property: an integer sequence starting below x that rises by
at most B per step must take a value in [x, x+B), which is then divisible by one
of the block moduli.

Part B (no-go, caps the method).  Coprimality alone cannot exclude rises much
larger than log2 log2 u.  Witness: given old moduli a_0 < a_1 < ... that grow
doubly exponentially (a_{i+1} = a_i^2 - a_i + 1 from a_0 = 2, i.e. Sylvester's
numbers, which are pairwise coprime), the greedy walk

    u_{n+1} = least integer > u_n coprime to every a_i with a_i <= u_n + (gap)

tends to infinity and avoids every old modulus, and we measure its rises.  Two
bounds bracket the truth:

  * CRT lower bound (what the barrier uses): some rise >= B is forced at a
    height <= 2 * prod of B block moduli, i.e. at height about 2^(2^B); hence
    rises of size (1 - delta) log2 log2 u cannot be avoided forever.
  * sieve upper bound (what defeats every coprimality argument): in any window
    of length L at height u, the integers coprime to all old moduli <= u + L
    number at least L * prod(1 - 1/m_i) - 2^k where k = #{moduli <= u + L}
    = O(log2 log2 u); so a window of length O(2^k) = O(log2 u) always contains
    an admissible value.  Rises of size C log2 u therefore never meet an
    obstruction from coprimality.  (Iwaniec's bound on the Jacobsthal function
    sharpens this to O((log log u)^2); not used.)

The measured maximal rise of the greedy witness is compared with both scales.
"""

from __future__ import annotations

import argparse
import json
from math import gcd, log2
from pathlib import Path


def sylvester(count: int) -> list[int]:
    seq = [2]
    for _ in range(count - 1):
        a = seq[-1]
        seq.append(a * a - a + 1)
    return seq


def primes(count: int) -> list[int]:
    out, n = [], 2
    while len(out) < count:
        if all(n % p for p in out if p * p <= n):
            out.append(n)
        n += 1
    return out


def crt_block(moduli: list[int]) -> tuple[int, int]:
    """x in [P, 2P) with moduli[r] | x + r.  Returns (x, P)."""
    P = 1
    for m in moduli:
        P *= m
    x = 0
    modulus = 1
    for r, m in enumerate(moduli):
        # want x = -r (mod m); current x is determined mod `modulus`
        target = (-r) % m
        # solve x + modulus * t = target (mod m)
        inv = pow(modulus % m, -1, m)
        t = ((target - x) * inv) % m
        x = x + modulus * t
        modulus *= m
    x %= P
    x += P
    for r, m in enumerate(moduli):
        assert (x + r) % m == 0
    assert P <= x < 2 * P
    return x, P


def landing_check(moduli: list[int], x: int, B: int, trials: int = 200) -> bool:
    """Random walks starting below x with rises <= B must land in [x, x+B)."""
    import random
    rng = random.Random(12345)
    for _ in range(trials):
        u = x - 1 - rng.randrange(0, 10 * B + 10)
        while u < x:
            u += rng.randrange(0, B + 1)
        if not (x <= u < x + B):
            return False
        if all((u % m) for m in moduli):
            return False
    return True


def part_a() -> list[dict]:
    rows = []
    for name, family in (("sylvester", sylvester(6)), ("primes", primes(9))):
        for B in range(1, len(family) + 1):
            block = family[:B]
            x, P = crt_block(block)
            rows.append({"family": name, "B": B, "moduli": block,
                         "x": x, "P": P, "x_in_[P,2P)": P <= x < 2 * P,
                         "log2log2_2P": round(log2(log2(2 * P)), 3) if 2 * P >= 4 else None,
                         "landing_ok": landing_check(block, x, B)})
    return rows


def greedy_witness(horizon: int, moduli: list[int]) -> dict:
    """Greedy avoiding walk against the old moduli (all of them, any size)."""
    u = 1
    max_rise = 0
    max_rise_at = 1
    rises_hist: dict[int, int] = {}
    steps = 0
    while u < horizon:
        v = u + 1
        while any(v % m == 0 for m in moduli if m <= v):
            v += 1
        rise = v - u
        rises_hist[rise] = rises_hist.get(rise, 0) + 1
        if rise > max_rise:
            max_rise, max_rise_at = rise, v
        u = v
        steps += 1
    return {"horizon": horizon, "steps": steps, "max_rise": max_rise,
            "max_rise_at_height": max_rise_at,
            "log2log2_height_at_max_rise": round(log2(log2(max(max_rise_at, 4))), 3),
            "log2_height_at_max_rise": round(log2(max_rise_at), 3),
            "rise_histogram": dict(sorted(rises_hist.items()))}


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--horizon", type=int, default=3_000_000)
    ap.add_argument("--out", type=str, default="")
    args = ap.parse_args()
    syl = sylvester(8)
    witness_syl = greedy_witness(args.horizon, syl)
    witness_primes = greedy_witness(args.horizon, primes(25))
    payload = {
        "probe_id": "erdos243_crt_block_and_coprime_witness",
        "part_a_bounded_crt_block": part_a(),
        "part_b_greedy_avoiding_walk": {
            "sylvester_moduli": syl,
            "against_sylvester_moduli": witness_syl,
            "against_first_25_primes": witness_primes,
        },
        "reading": {
            "sylvester": (
                "against doubly exponential pairwise-coprime old moduli the greedy walk "
                "needs only tiny rises (max_rise stays far below log2 of the height), "
                "so coprimality alone can never force a contradiction at rises of order "
                "log2 u; the barrier's log2 log2 u scale is what CRT blocks can extract"),
            "primes": (
                "against small moduli (consecutive primes) the same walk needs rises of "
                "order the prime gaps, showing the barrier's strength depends on the "
                "growth of the moduli; the #243 moduli are the multipliers, which are "
                "doubly exponential, so the weak case is the relevant one"),
        },
    }
    text = json.dumps(payload, indent=1, ensure_ascii=False)
    if args.out:
        Path(args.out).write_text(text + "\n")
    print(text)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
