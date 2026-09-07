#!/usr/bin/env python3
"""Erdos 257: adversarial structure tests on the greedy support word.

Everything measured so far -- density, margins, maximal runs, death ranks --
is consistent with the greedy word of a rational target being
Bernoulli(1/2).  That is a *negative* claim, and negative claims of this kind
are only as strong as the sharpest test that failed to break them.  This
battery is that test.

A single hidden periodicity, a single arithmetic correlation, a single
biased block would be the structure the whole programme has been looking
for: by the run law of SupportWordStructureLab.md section 3 the target dies
exactly when the word ends in an infinite run of selected ranks, so any
mechanism that biases the word towards long selected runs is a mechanism for
Erdos 257, and any that biases it away is a mechanism against.

Tests, all on the certified forced-greedy word:

  spectral      full DFT; max_{k != 0} |sum_n b_n e(nk/N)|.  A word with a
                hidden period M shows a spike at k = N/M.  Null bound for a
                Bernoulli word is O(sqrt(N log N)).
  autocorrelation   lags 1..L, normalised; null is 1/4 with sd 1/(2 sqrt N).
  arithmetic    correlation of (2 b_n - 1) with mu(n), the Liouville
                function, the parity of Omega(n), the parity of d(n), the
                2-adic valuation parity, and the prime and squarefree
                indicators.
  blocks        frequency of every k-block for k <= 12 against 2^-k, chi^2.
  multiplicative  P(b_{kn} = 1 | b_n = 1) for k <= 24; null 1/2.
  target        P(b_n = 1 | n mod ell_0), against the binary digits of x.

Companion analysis: ErdosProblems/Erdos257/SupportWordStructureLab.md
"""

from __future__ import annotations

import argparse
import hashlib
import json
import math
from typing import Any

import numpy as np


def canonical_sha256(payload: Any) -> str:
    return hashlib.sha256(
        json.dumps(payload, separators=(",", ":"), sort_keys=True).encode()
    ).hexdigest()


def build_z(P: int, ranks: int = 0) -> list[int]:
    nbytes = (P + 8) // 8 + 1
    pat = bytearray(nbytes)
    Z = [0] * (P + 2)
    for n in range(1, P + 1):
        pos = P - n
        positions = []
        while pos >= 0:
            positions.append(pos)
            pos -= n
        for u in positions:
            pat[nbytes - 1 - (u >> 3)] |= 1 << (u & 7)
        Z[n] = int.from_bytes(bytes(pat), "big")
        for u in positions:
            pat[nbytes - 1 - (u >> 3)] = 0
    if not ranks:
        return Z
    TT = [0] * (ranks + 2)
    acc = 0
    for k in range(P, ranks, -1):
        acc += Z[k]
    for n in range(ranks, -1, -1):
        TT[n] = acc
        if n >= 1:
            acc += Z[n]
    return Z, TT


def greedy_word(
    p: int, q: int, ranks: int, Z: list[int], TT: list[int], P: int
) -> np.ndarray:
    """Forced greedy word, with the certified death test r_n > T_n.

    Without the death test a dead target silently returns an all-ones word
    (death is exactly an infinite run of takes, section 3), and every
    statistic below then measures a constant sequence rather than a support
    word.  That is how 29/31 and 13/17 first entered this battery reporting
    a 4-block chi^2/dof of 9998 and a spectral ratio of 0.003.
    """
    lo = ((1 << P) * p) // q
    hi = lo + 1
    w = np.zeros(ranks + 1, dtype=np.int8)
    for n in range(1, ranks + 1):
        zn = Z[n]
        if lo >= zn + 1:
            lo -= zn + 1
            hi -= zn
            w[n] = 1
        elif hi > zn:
            raise RuntimeError(f"undecided at rank {n}")
        tn = TT[n]
        if lo > tn + P:
            raise ValueError(f"target {p}/{q} is DEAD at rank {n}")
        if hi > tn:
            raise RuntimeError(f"death test undecided at rank {n}")
    return w


def arithmetic_tables(N: int) -> dict[str, np.ndarray]:
    mu = np.ones(N + 1, dtype=np.int8)
    omega = np.zeros(N + 1, dtype=np.int16)
    Omega = np.zeros(N + 1, dtype=np.int16)
    dv = np.ones(N + 1, dtype=np.int32)
    sq = np.ones(N + 1, dtype=np.int8)
    v2 = np.zeros(N + 1, dtype=np.int16)
    is_comp = np.zeros(N + 1, dtype=bool)
    for i in range(2, N + 1):
        if not is_comp[i]:
            for m in range(i, N + 1, i):
                is_comp[m] = m != i
                omega[m] += 1
                e = 0
                mm = m
                while mm % i == 0:
                    mm //= i
                    e += 1
                Omega[m] += e
                dv[m] *= e + 1
                if e >= 2:
                    sq[m] = 0
                    mu[m] = 0
                elif mu[m] != 0:
                    mu[m] = -mu[m]
                if i == 2:
                    v2[m] = e
    primes = np.zeros(N + 1, dtype=np.int8)
    primes[2:] = (~is_comp[2:]).astype(np.int8)
    return {
        "mu": mu,
        "liouville": np.where(Omega % 2 == 0, 1, -1).astype(np.int8),
        "omega_parity": (omega % 2).astype(np.int8),
        "tau_parity": (dv % 2).astype(np.int8),
        "v2_parity": (v2 % 2).astype(np.int8),
        "prime": primes,
        "squarefree": sq,
    }


def analyse(p: int, q: int, ranks: int, pad: int, lags: int) -> dict[str, Any]:
    P = 2 * ranks + pad
    Z, TT = build_z(P, ranks)
    w = greedy_word(p, q, ranks, Z, TT, P)
    b = w[1 : ranks + 1].astype(np.float64)
    N = b.size
    centred = 2.0 * b - 1.0

    spec = np.abs(np.fft.rfft(centred))
    spec[0] = 0.0
    kmax = int(np.argmax(spec))
    null_spectral = math.sqrt(N * math.log(N))

    ac = []
    for lag in range(1, min(lags, N // 4) + 1):
        ac.append(float(np.dot(centred[:-lag], centred[lag:]) / (N - lag)))
    ac_arr = np.array(ac)
    ac_sd = 1.0 / math.sqrt(N)

    tabs = arithmetic_tables(ranks)
    idx = np.arange(1, ranks + 1)
    arith: dict[str, Any] = {}
    for name, tab in tabs.items():
        v = tab[idx].astype(np.float64)
        v = v - v.mean()
        denom = math.sqrt(float(np.dot(v, v)) * float(np.dot(centred, centred)))
        corr = float(np.dot(centred, v)) / denom if denom > 0 else 0.0
        arith[name] = {"corr": corr, "z": corr * math.sqrt(N)}

    # Non-overlapping blocks: overlapping windows are dependent and drive the
    # chi^2 statistic below its own degrees of freedom, which reads as a false
    # "too uniform" signal.
    blocks: dict[str, Any] = {}
    for k in (4, 8, 12):
        nb = N // k
        arr = b[: nb * k].astype(np.int64).reshape(nb, k)
        vals = np.zeros(nb, dtype=np.int64)
        for i in range(k):
            vals = (vals << 1) | arr[:, i]
        counts = np.bincount(vals, minlength=1 << k)
        expected = nb / (1 << k)
        chi2 = float(((counts - expected) ** 2 / expected).sum())
        dof = (1 << k) - 1
        blocks[str(k)] = {
            "chi2": chi2,
            "dof": dof,
            "blocks_used": nb,
            "chi2_over_dof": chi2 / dof,
            "z": (chi2 - dof) / math.sqrt(2 * dof),
            "empty_blocks": int((counts == 0).sum()),
        }

    mult: dict[str, float] = {}
    for k in range(2, 25):
        sel = np.nonzero(w[1 : ranks // k + 1])[0] + 1
        if sel.size < 50:
            continue
        mult[str(k)] = float(w[sel * k].mean())

    ell0 = None
    m = q
    while m % 2 == 0:
        m //= 2
    if m > 1:
        r, kk = 2 % m, 1
        while r != 1 and kk <= 4 * m:
            r = (2 * r) % m
            kk += 1
        ell0 = kk if r == 1 else None
    modprof = None
    if ell0 and ell0 <= 64:
        modprof = {
            str(rr): float(b[rr::ell0].mean()) for rr in range(min(ell0, 12))
        }

    return {
        "target": f"{p}/{q}",
        "ranks": ranks,
        "density": float(b.mean()),
        "density_z": (float(b.mean()) - 0.5) * 2 * math.sqrt(N),
        "spectral": {
            "max_abs": float(spec[kmax]),
            "at_frequency_index": kmax,
            "implied_period": (N / kmax) if kmax else None,
            "null_sqrt_N_logN": null_spectral,
            "ratio_to_null": float(spec[kmax]) / null_spectral,
        },
        "autocorrelation": {
            "lags_tested": len(ac),
            "max_abs": float(np.abs(ac_arr).max()),
            "max_abs_lag": int(np.abs(ac_arr).argmax()) + 1,
            "max_abs_z": float(np.abs(ac_arr).max()) / ac_sd,
            "expected_max_z_for_sample": math.sqrt(2 * math.log(max(len(ac), 2))),
        },
        "arithmetic_correlations": arith,
        "block_frequencies": blocks,
        "multiplicative_conditional_density": mult,
        "binary_period_ell0": ell0,
        "density_by_residue_mod_ell0": modprof,
    }


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--ranks", type=int, default=60000)
    ap.add_argument("--pad", type=int, default=128)
    ap.add_argument("--lags", type=int, default=4000)
    ap.add_argument("--targets", type=str, default="1/21,4/9,3/11,1/465")
    ap.add_argument("--write", type=str, default=None)
    args = ap.parse_args()

    rows = []
    for tok in args.targets.split(","):
        tok = tok.strip()
        if not tok:
            continue
        a, bq = tok.split("/")
        try:
            rows.append(analyse(int(a), int(bq), args.ranks, args.pad, args.lags))
        except ValueError as exc:
            rows.append({"target": tok, "status": "dead", "detail": str(exc)})

    payload = {
        "schema": "erdos257_support_word_pseudorandomness_v1",
        "parameters": vars(args),
        "source": {
            "script": "formal_math/erdos257_period_noncollapse/scripts/"
            "support_word_pseudorandomness_battery.py",
            "analysis": "formal_math/erdos257_period_noncollapse/ErdosProblems/"
            "Erdos257/SupportWordStructureLab.md",
        },
        "rows": rows,
    }
    payload["payload_sha256"] = canonical_sha256(payload)
    text = json.dumps(payload, indent=2, sort_keys=True, default=str)
    if args.write:
        with open(args.write, "w", encoding="utf-8") as h:
            h.write(text + "\n")
        print(f"wrote {args.write} sha256={payload['payload_sha256']}")
    else:
        print(text)


if __name__ == "__main__":
    main()
