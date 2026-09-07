#!/usr/bin/env python3
"""Erdos 257: structure of the greedy SUPPORT WORD, not of the carry.

Central object.  For a rational target ``x = p/q`` the Mersenne achievement
set

    C = { sum_{a in A} 1/(2^a - 1) : A subset of N }

is a Cantor set because the strict tail domination

    1/(2^n - 1) > sum_{k>n} 1/(2^k - 1)

holds at every rank.  Hence every ``x`` in ``C`` has EXACTLY ONE support
``A``, and the greedy scan is forced rather than merely convenient.  The
membership question therefore has a single dynamical answer per target, and
the object that carries it is the Boolean word ``1_A``.

Two independent engines are run.

``carry`` engine
    The integer relaxation used by the rest of this directory:
    ``Q_n = 2 Q_{n-1} + t_n - f_A(n)`` with ``f_A(n) = #{d | n, d in A}``,
    ``b_n = 1`` iff the resulting ``Q_n`` stays nonnegative.  This is the
    lexicographic maximiser of the TRUNCATED sum ``sum_{m<=n} f_A(m) 2^-m``
    subject to staying below the truncated target.  It is sound for
    membership (an infinite survivor with ``Q_n = o(2^n)`` really is a
    representation) but it is a relaxation: it may bank a digit whose own
    future pulses already overspend.

``certified`` engine
    The true forced greedy on the real remainder ``r_n = x - sum_{a<=n, a in A}
    1/(2^a-1)``, decided by exact dyadic enclosures at ``2N + pad`` bits.
    ``b_n = 1`` iff ``r_{n-1} >= 1/(2^n-1)``.  Death is the exact event
    ``T_n < r_{n-1} < 1/(2^n-1)``, i.e. the orbit falls in the rank-``n``
    Cantor gap, whose width is

        gamma_n = 1/(2^n-1) - sum_{k>n} 1/(2^k-1)
                = sum_{j>=2} 2^{-jn} (2^j - 2)/(2^j - 1)
                = (2/3) 4^-n (1 + O(2^-n)).

    The lab reports the SAFETY RATIO  S_n = (z_n - r_{n-1}) / gamma_n  at
    every skip: survival at rank ``n`` is exactly ``S_n >= 1``.

Cross-checking the two engines is itself a result: they are provably
different algorithms (see the module docstring test ``x = 3/2``), so an
observed agreement over a certified range is evidence, not a tautology.

Companion analysis: ErdosProblems/Erdos257/SupportWordStructureLab.md
Receipt: state/formal_math/erdos257_period_noncollapse/support_word_structure_receipt.json
"""

from __future__ import annotations

import argparse
import hashlib
import json
import math
from fractions import Fraction
from typing import Any


# ----------------------------------------------------------------- helpers


def canonical_sha256(payload: Any) -> str:
    blob = json.dumps(payload, separators=(",", ":"), sort_keys=True)
    return hashlib.sha256(blob.encode("utf-8")).hexdigest()


def target_bits(p: int, q: int, ranks: int) -> tuple[bytearray, int]:
    """Binary digits t_1..t_ranks of the fractional part of p/q, plus floor."""
    whole, rho = divmod(p, q)
    bits = bytearray(ranks + 1)
    for n in range(1, ranks + 1):
        rho *= 2
        if rho >= q:
            bits[n] = 1
            rho -= q
    return bits, whole


# --------------------------------------------------------- engine: carry


def carry_engine(p: int, q: int, ranks: int) -> dict[str, Any]:
    """Integer relaxation Q_n >= 0.  Returns word, defects, failure rank."""
    tbits, whole = target_bits(p, q, ranks)
    load = bytearray(ranks + 2)          # f_A(n) accumulated from d < n
    word = bytearray(ranks + 1)
    defects = [0] * (ranks + 1)
    defects[0] = whole
    failure_rank = None
    max_defect = 0
    max_defect_rank = 0
    for n in range(1, ranks + 1):
        avail = 2 * defects[n - 1] + tbits[n] - load[n]
        if avail < 0:
            failure_rank = n
            break
        bit = 1 if avail >= 1 else 0
        word[n] = bit
        defects[n] = avail - bit
        if defects[n] > max_defect:
            max_defect = defects[n]
            max_defect_rank = n
        if bit:
            for m in range(2 * n, ranks + 2, n):
                load[m] += 1
    return {
        "word": word,
        "defects": defects,
        "failure_rank": failure_rank,
        "max_defect": max_defect,
        "max_defect_rank": max_defect_rank,
        "target_bits": tbits,
    }


# ----------------------------------------------------- engine: certified


def certified_engine(
    p: int, q: int, ranks: int, pad: int = 160, safety_from: int = 8
) -> dict[str, Any]:
    """Exact forced greedy on the real remainder, dyadic enclosures.

    ``lo <= 2^P r_n <= hi`` is a certified enclosure at ``P = 2*ranks + pad``
    bits; every branch is taken only when the enclosure decides it.  The
    rank-``n`` Cantor gap width

        gamma_n = z_n - T_n = sum_{j>=2} 2^{-jn} (2^j - 2)/(2^j - 1)

    is evaluated to relative precision far below its own size, so the
    reported safety ratio  S_n = (z_n - r_{n-1}) / gamma_n  is certified.
    Survival at a skip is exactly ``S_n >= 1``.
    """
    P = 2 * ranks + pad
    scale = 1 << P
    lo = (scale * p) // q
    hi = lo + 1

    nbytes = (P + 8) // 8 + 1
    pat = bytearray(nbytes)

    def pattern(n: int) -> int:
        """floor(2^P / (2^n - 1)) exactly: bits set at P - k n for k >= 1."""
        positions = []
        pos = P - n
        while pos >= 0:
            positions.append(pos)
            pos -= n
        for pos in positions:
            pat[nbytes - 1 - (pos >> 3)] |= 1 << (pos & 7)
        value = int.from_bytes(bytes(pat), "big")
        for pos in positions:
            pat[nbytes - 1 - (pos >> 3)] = 0
        return value

    word = bytearray(ranks + 1)
    failure_rank = None
    undecided_rank = None
    min_safety = None
    min_relative = None
    margin_hist: dict[int, int] = {}
    safety_ranks: list[list[int]] = []
    safety_min_by_decade: dict[str, list[float | int]] = {}
    skip_count = 0
    checked = 0

    for n in range(1, ranks + 1):
        zn = pattern(n)                    # 2^P z_n in [zn, zn+1]
        if lo >= zn + 1:
            word[n] = 1
            lo -= zn + 1
            hi -= zn
            continue
        if hi > zn:
            undecided_rank = n
            break
        skip_count += 1
        if n < safety_from or 3 * n > P:
            continue
        jmax = min(P // n, 12)
        gamma = 0
        for j in range(2, jmax + 1):
            gamma += ((1 << (P - j * n)) * ((1 << j) - 2)) // ((1 << j) - 1)
        trunc_err = 1 << max(P - (jmax + 1) * n + 2, 0)
        short_lo = zn - hi
        short_hi = zn + 1 - lo
        if short_lo > gamma + trunc_err:
            safe = True
        elif short_hi < gamma - trunc_err:
            safe = False
        else:
            undecided_rank = n
            break
        if not safe:
            failure_rank = n
            break
        checked += 1
        # Certified bit margin: how many binary orders of magnitude the
        # shortfall z_n - r_{n-1} clears the rank-n Cantor gap gamma_n.
        # Death is exactly margin < 0.  Typical margin is ~n.
        margin = short_lo.bit_length() - gamma.bit_length()
        margin_hist[margin] = margin_hist.get(margin, 0) + 1
        if min_safety is None or margin < min_safety[0]:
            min_safety = (margin, n)
        decade = str(len(str(n)))
        cur = safety_min_by_decade.get(decade)
        if cur is None or margin < cur[0]:
            safety_min_by_decade[decade] = [margin, n]
        # Relative approach: margin minus n is the scale-free closeness.
        rel = margin - n
        if min_relative is None or rel < min_relative[0]:
            min_relative = (rel, n, margin)
        if margin <= 12 and len(safety_ranks) < 512:
            safety_ranks.append([n, margin])

    return {
        "word": word,
        "failure_rank": failure_rank,
        "undecided_rank": undecided_rank,
        "min_margin_bits": None if min_safety is None else min_safety[0],
        "min_margin_rank": None if min_safety is None else min_safety[1],
        "min_relative_margin": None if min_relative is None else min_relative[0],
        "min_relative_margin_rank": None if min_relative is None else min_relative[1],
        "min_relative_margin_bits": None if min_relative is None else min_relative[2],
        "margin_bits_histogram": {str(k): v for k, v in sorted(margin_hist.items())[:40]},
        "safety_checks": checked,
        "skip_count": skip_count,
        "safety_min_by_decade": safety_min_by_decade,
        "tight_safety_ranks": safety_ranks,
        "precision_bits": P,
        "safety_from": safety_from,
    }


# ------------------------------------------------------------ recognizers


def smallest_period(word: bytearray, start: int, end: int, cap: int) -> int | None:
    for M in range(1, cap + 1):
        ok = True
        for n in range(start, end + 1 - M):
            if word[n] != word[n + M]:
                ok = False
                break
        if ok:
            return M
    return None


def residue_class_union(word: bytearray, start: int, end: int, cap: int) -> int | None:
    """Smallest M such that 1_A(n) depends only on n mod M on [start, end]."""
    for M in range(1, cap + 1):
        seen: dict[int, int] = {}
        ok = True
        for n in range(start, end + 1):
            r = n % M
            v = word[n]
            if r in seen:
                if seen[r] != v:
                    ok = False
                    break
            else:
                seen[r] = v
        if ok:
            return M
    return None


def kernel_size(word: bytearray, ranks: int, base: int, depth: int, sample: int) -> int:
    """Number of distinct base-`base` kernel subsequences up to `depth`."""
    seen: set[tuple[int, ...]] = set()
    frontier = [(1, 0)]                      # (stride, offset): n = stride*m + offset
    for _ in range(depth):
        nxt = []
        for stride, offset in frontier:
            sig = []
            m = 0
            while len(sig) < sample:
                n = stride * m + offset
                if n > ranks:
                    break
                if n >= 1:
                    sig.append(word[n])
                m += 1
            if len(sig) < sample // 2:
                continue
            key = tuple(sig)
            if key not in seen:
                seen.add(key)
                for r in range(base):
                    nxt.append((stride * base, offset + stride * r))
        frontier = nxt
        if not frontier:
            break
    return len(seen)


def divisor_stats(word: bytearray, ranks: int) -> dict[str, Any]:
    load = [0] * (ranks + 1)
    for d in range(1, ranks + 1):
        if word[d]:
            for m in range(d, ranks + 1, d):
                load[m] += 1
    hist: dict[int, int] = {}
    for n in range(1, ranks + 1):
        hist[load[n]] = hist.get(load[n], 0) + 1
    lo_half = ranks // 2
    non_primitive = sum(
        1 for a in range(1, ranks + 1) if word[a] and load[a] >= 2
    )
    selected = sum(word[1 : ranks + 1])
    return {
        "selected": selected,
        "density": selected / ranks,
        "harmonic_sum": sum(1.0 / a for a in range(1, ranks + 1) if word[a]),
        "load_histogram": {str(k): v for k, v in sorted(hist.items())},
        "max_load": max(hist),
        "non_primitive_selected": non_primitive,
        "primitive_fraction": 1.0 - non_primitive / max(selected, 1),
        "tail_density": sum(word[lo_half : ranks + 1]) / (ranks - lo_half + 1),
    }


def closure_stats(word: bytearray, ranks: int) -> dict[str, Any]:
    sel = [a for a in range(2, ranks // 2 + 1) if word[a]]
    if not sel:
        return {}
    out: dict[str, Any] = {}
    for k in (2, 3, 4, 5, 6):
        tot = [a for a in sel if k * a <= ranks]
        if tot:
            out[f"P(ka in A | a in A), k={k}"] = sum(word[k * a] for a in tot) / len(tot)
    base = [a for a in range(2, ranks + 1) if word[a]]
    out["P(a in A) overall"] = len(base) / ranks
    return out


def modular_profile(word: bytearray, ranks: int, M: int, start: int) -> dict[str, float]:
    counts = [0] * M
    totals = [0] * M
    for n in range(start, ranks + 1):
        counts[n % M] += word[n]
        totals[n % M] += 1
    return {str(r): counts[r] / totals[r] for r in range(M) if totals[r]}


def run_stats(word: bytearray, ranks: int) -> dict[str, Any]:
    """Maximal runs of consecutive selected / skipped ranks.

    Exact criterion (proved in SupportWordStructureLab.md): if the greedy
    skips at rank m with survival margin delta_m = T_m - r_{m-1} >= 0, then
    the ranks m+1, ..., m+L are all selected and m+L+1 is skipped, where

        L = max{ i >= 0 : T_{m+i} >= delta_m },   i.e.  delta_m ~ 2^-(m+L).

    Hence x is NOT in C exactly when the greedy word ends in an infinite run
    of 1s, and the maximal take-run before rank N is a single integer that
    records the closest the orbit ever came to death.
    """
    best_take = (0, 0)
    best_skip = (0, 0)
    cur = word[1]
    length = 1
    start = 1
    takes: list[list[int]] = []
    for n in range(2, ranks + 1):
        if word[n] == cur:
            length += 1
            continue
        if cur == 1:
            if length > best_take[0]:
                best_take = (length, start)
            if length >= 6:
                takes.append([start - 1, length])
        else:
            if length > best_skip[0]:
                best_skip = (length, start)
        cur = word[n]
        length = 1
        start = n
    if cur == 1 and length > best_take[0]:
        best_take = (length, start)
    if cur == 0 and length > best_skip[0]:
        best_skip = (length, start)
    return {
        "max_take_run": best_take[0],
        "max_take_run_start": best_take[1],
        "max_take_run_over_log2_start": (
            best_take[0] / (best_take[1].bit_length()) if best_take[1] else None
        ),
        "death_threshold_at_that_rank": best_take[1],
        "max_skip_run": best_skip[0],
        "max_skip_run_start": best_skip[1],
        "long_take_runs_ge6": takes[:64],
    }


def gap_stats(word: bytearray, ranks: int, start: int) -> dict[str, Any]:
    positions = [n for n in range(start, ranks + 1) if word[n]]
    if len(positions) < 3:
        return {"count": len(positions)}
    gaps = [b - a for a, b in zip(positions, positions[1:])]
    hist: dict[int, int] = {}
    for g in gaps:
        hist[g] = hist.get(g, 0) + 1
    return {
        "count": len(positions),
        "max_gap": max(gaps),
        "max_gap_at": positions[gaps.index(max(gaps))],
        "mean_gap": sum(gaps) / len(gaps),
        "gap_histogram": {str(k): v for k, v in sorted(hist.items())[:24]},
        "distinct_gaps": len(hist),
    }


# ------------------------------------------------------------------- main


def analyse_target(
    p: int, q: int, ranks: int, relax_ranks: int, period_cap: int
) -> dict[str, Any]:
    """Certified forced greedy is authority; the carry relaxation is a control."""
    cert = certified_engine(p, q, ranks)
    word = cert["word"]
    horizon = ranks
    for cut in (cert["failure_rank"], cert["undecided_rank"]):
        if cut is not None:
            horizon = min(horizon, cut - 1)

    row: dict[str, Any] = {
        "target": f"{p}/{q}",
        "ranks": ranks,
        "certified_horizon": horizon,
        "certified_failure_rank": cert["failure_rank"],
        "certified_undecided_rank": cert["undecided_rank"],
        "min_margin_bits": cert["min_margin_bits"],
        "min_margin_rank": cert["min_margin_rank"],
        "min_relative_margin": cert["min_relative_margin"],
        "min_relative_margin_rank": cert["min_relative_margin_rank"],
        "min_relative_margin_bits": cert["min_relative_margin_bits"],
        "margin_bits_histogram": cert["margin_bits_histogram"],
        "safety_checks": cert["safety_checks"],
        "skip_count": cert["skip_count"],
        "margin_min_by_decade": cert["safety_min_by_decade"],
        "tight_margin_ranks": cert["tight_safety_ranks"],
        "precision_bits": cert["precision_bits"],
    }

    if relax_ranks > 0:
        relax = carry_engine(p, q, min(relax_ranks, ranks))
        rw = relax["word"]
        limit = min(
            horizon, min(relax_ranks, ranks), (relax["failure_rank"] or 10**9) - 1
        )
        first_div = None
        for n in range(1, limit + 1):
            if rw[n] != word[n]:
                first_div = n
                break
        row["carry_relaxation_control"] = {
            "ranks": min(relax_ranks, ranks),
            "failure_rank": relax["failure_rank"],
            "first_divergence_from_forced_greedy": first_div,
            "compared_through": limit,
        }

    if horizon >= 200:
        start = max(2, horizon // 2)
        row["structure"] = {
            "eventual_period_le_cap": smallest_period(word, start, horizon, period_cap),
            "residue_class_union_le_cap": residue_class_union(
                word, start, horizon, period_cap
            ),
            "kernel2_size": kernel_size(word, horizon, 2, 5, 64),
            "kernel3_size": kernel_size(word, horizon, 3, 4, 64),
            "divisor": divisor_stats(word, horizon),
            "closure": closure_stats(word, horizon),
            "gaps": gap_stats(word, horizon, start),
            "runs": run_stats(word, horizon),
            "mod6_profile": modular_profile(word, horizon, 6, start),
            "mod12_profile": modular_profile(word, horizon, 12, start),
        }
        row["prefix_word"] = "".join(str(word[n]) for n in range(1, min(horizon, 240) + 1))
        if horizon > 5240:
            row["window_word_5000"] = "".join(
                str(word[n]) for n in range(5001, 5241)
            )
    return row


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--ranks", type=int, default=20000)
    ap.add_argument("--relax-ranks", type=int, default=4000)
    ap.add_argument("--period-cap", type=int, default=720)
    ap.add_argument(
        "--targets",
        type=str,
        default="1/21,4/9,1/5,2/21,1/465,90/511,1/2,3/11,8/21,1/3",
    )
    ap.add_argument("--write", type=str, default=None)
    args = ap.parse_args()

    targets = []
    for tok in args.targets.split(","):
        tok = tok.strip()
        if not tok:
            continue
        a, b = tok.split("/")
        targets.append((int(a), int(b)))

    rows = [
        analyse_target(p, q, args.ranks, args.relax_ranks, args.period_cap)
        for p, q in targets
    ]
    payload: dict[str, Any] = {
        "schema": "erdos257_support_word_structure_v1",
        "parameters": {
            "ranks": args.ranks,
            "relax_ranks": args.relax_ranks,
            "period_cap": args.period_cap,
            "targets": args.targets,
        },
        "source": {
            "script": "formal_math/erdos257_period_noncollapse/scripts/"
            "support_word_structure_lab.py",
            "analysis": "formal_math/erdos257_period_noncollapse/ErdosProblems/"
            "Erdos257/SupportWordStructureLab.md",
        },
        "rows": rows,
    }
    payload["payload_sha256"] = canonical_sha256(payload)
    text = json.dumps(payload, indent=2, sort_keys=True)
    if args.write:
        with open(args.write, "w", encoding="utf-8") as handle:
            handle.write(text + "\n")
        print(f"wrote {args.write} sha256={payload['payload_sha256']}")
    else:
        print(text)


if __name__ == "__main__":
    main()
