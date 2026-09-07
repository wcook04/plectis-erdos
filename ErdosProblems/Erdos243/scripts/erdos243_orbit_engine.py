#!/usr/bin/env python3
"""Shared hybrid exact/modular engine for the Koizumi pseudo-greedy orbit (Erdos #243).

Canonical unreduced coordinates.  Seed (C_0, D_0) = (p, q) for x_0 = p/q, and

    E_n = centred residue of D_n mod C_n,
    a_n = (D_n - E_n)/C_n + 1 = (D_n + C_{n+1})/C_n,
    C_{n+1} = C_n - E_n,
    D_{n+1} = D_n * a_n.

`E_n = 0` is absorbing (D_n = 0 mod C_n forces D_{n+1} = 0 mod C_{n+1} = C_n),
and reaching it is exactly the Sylvester tail a_{n+1} = a_n^2 - a_n + 1.  This
module calls that TERMINATION.  Erdos #243 (Koizumi form) is the statement that
a rational orbit with E_n/C_n -> 0 must terminate; the STRONG form tested by
the survey scripts drops the rate hypothesis entirely.

Tie rule
--------
`tie="low"`  : E_n in [-C_n/2, C_n/2)   (Koizumi's normalisation; probe default)
`tie="high"` : E_n in (-C_n/2, C_n/2]
They differ only when C_n is even and D_n = C_n/2 (mod C_n).  `low` rounds the
quotient D_n/C_n UP at a tie, `high` rounds it DOWN.

Modulus method (why no doubly-exponential D_n is ever materialised)
-------------------------------------------------------------------
log D_n roughly doubles at every step, so exact D_n is hopeless past ~12 steps.
But D_n is only ever needed

    (a) mod C_n            -> E_n,
    (b) mod C_{n+1}        -> r_n := D_n mod C_{n+1},
    (c) mod `extra`        -> optional side data (small-prime valuations).

Because C_k | D_k - E_k exactly, knowing D_k mod (C_k * M) determines
a_k = (D_k - E_k)/C_k + 1 modulo M.  Hence the SHRINKING SUFFIX PRODUCT

    S_k = (prod_{j=k}^{n} C_j) * extra ,      S_{n+1} = extra

transports D_0 mod S_0 forward to D_n mod (C_n * extra) with one exact division
by C_k per step and no loss.  This is Koizumi's Remark 18 algorithm.  Note the
modulus is a product of the ACTUAL heights, so its bit-length is
sum_j log2 C_j <= N log2 H, NOT ~1.44*H*N as it would be for lcm(1..H)^{N+1};
for H = 10^3, N = 60 that is ~600 bits instead of ~10^5 bits.

The suffix product depends on C_{n+1}, which is only discovered after step n,
so the forward pass is redone once per step: O(L^2) bigint ops for an orbit of
length L, on numbers of ~L*log2 H bits.  Since almost every orbit is short, the
engine first runs EXACT integer arithmetic (O(L) ops) until bit_length(D)
exceeds `exact_bits`, then hands the exact state (C_m, D_m) to the modular
phase.  The dynamics is Markov in (C, D), so the handover is lossless.

Auxiliary exact facts used and re-verified by the scripts:
  * gcd(C_n, D_n) = gcd(C_n, D_n mod M) whenever C_n | M.
  * C_n * E_{n+1} = r_n^2  (mod C_{n+1})   and, since C_n = E_n (mod C_{n+1}),
    E_n * E_{n+1} = r_n^2  (mod C_{n+1}).   [no coprimality needed]
"""

from __future__ import annotations

import sys
from math import gcd
from pathlib import Path

_REPO_ROOT = Path(__file__).resolve().parents[5]
_PROBE_DIR = _REPO_ROOT / "formal_math" / "probes"
if str(_PROBE_DIR) not in sys.path:
    sys.path.insert(0, str(_PROBE_DIR))

# Imported, not copied: the canonical centred residue and the reference orbits.
from erdos243_koizumi_state_probe import (  # noqa: E402
    centred_residue,
    orbit_exact,
    orbit_modular,
)

__all__ = [
    "centred_residue",
    "orbit_exact",
    "orbit_modular",
    "centre",
    "run_orbit",
    "TERMINATED",
    "HEIGHT_CAP",
    "STEP_CAP",
]

TERMINATED = "terminated"
HEIGHT_CAP = "height_cap"
STEP_CAP = "step_cap"


def centre(d: int, c: int, tie: str = "low") -> int:
    """Centred residue of d modulo c under the named tie rule."""
    if tie == "low":
        return centred_residue(d, c)
    e = d % c
    if 2 * e > c:
        e -= c
    return e


def run_orbit(
    C0: int,
    D0: int,
    *,
    height_cap: int = 10 ** 12,
    step_cap: int = 400,
    exact_bits: int = 6000,
    extra: int = 1,
    tie: str = "low",
    lean: bool = True,
):
    """Run the pseudo-greedy orbit from the seed (C_0, D_0) = (C0, D0).

    Returns a dict with keys
        C       : [C_0, ..., C_T]           heights actually visited
        E       : [E_0, ..., E_T]           centred residues (E_T = 0 iff terminated)
        status  : terminated | height_cap | step_cap
        steps   : T (index of the last recorded E)
        exact_steps : how many steps ran in the exact phase
    and, when lean=False, also
        G       : [gcd(C_n, D_n)]
        R       : [r_n = D_n mod C_{n+1}]   (None where not yet determined)
        Dmod    : [D_n mod extra]           (only when extra > 1)
        Dexact  : [D_n or None]             (exact values while in exact phase)
    """
    Cs: list[int] = [C0]
    Es: list[int] = []
    Gs: list[int] = [] if not lean else []
    Rs: list = [] if not lean else []
    Dmods: list = [] if not lean else []
    Dexact: list = [] if not lean else []

    status = None
    C = C0
    D = D0
    n = 0

    # ---------------- exact phase ----------------
    while True:
        if C > height_cap:
            status = HEIGHT_CAP
            break
        if n >= step_cap:
            status = STEP_CAP
            break
        if D.bit_length() > exact_bits:
            break  # hand over to the modular phase with the exact state (C, D)
        e = centre(D % C, C, tie)
        Cn1 = C - e
        Es.append(e)
        if not lean:
            Gs.append(gcd(C, D))
            Rs.append(D % Cn1)
            Dmods.append(D % extra if extra > 1 else None)
            Dexact.append(D)
        if e == 0:
            status = TERMINATED
            break
        a = (D - e) // C + 1
        D = D * a
        C = Cn1
        Cs.append(C)
        n += 1

    exact_steps = len(Es)

    # ---------------- modular phase ----------------
    if status is None:
        seedD = D
        base = n  # global index of the modular seed
        mCs = [C]
        mEs: list[int] = []
        mRs: list = []
        mGs: list = []
        mDmods: list = []
        while True:
            k_local = len(mEs)
            Cn = mCs[k_local]
            if Cn > height_cap:
                status = HEIGHT_CAP
                break
            if base + k_local >= step_cap:
                status = STEP_CAP
                break
            # suffix moduli S[j] = prod_{i=j..k_local} mCs[i] * extra
            S = [0] * (k_local + 2)
            S[k_local + 1] = extra
            for j in range(k_local, -1, -1):
                S[j] = mCs[j] * S[j + 1]
            d = seedD % S[0]
            for j in range(k_local):
                mod_next = S[j + 1]
                if not lean:
                    # r_j = D_j mod C_{j+1}: C_{j+1} divides S[j] for j < k_local
                    if j < len(mRs):
                        mRs[j] = d % mCs[j + 1]
                    else:
                        mRs.append(d % mCs[j + 1])
                a = ((d - mEs[j]) // mCs[j] + 1) % mod_next
                d = (d % mod_next) * a % mod_next
            # d == D_{k_local} mod (Cn * extra)
            e = centre(d % Cn, Cn, tie)
            mEs.append(e)
            if not lean:
                mGs.append(gcd(Cn, d % Cn))
                mDmods.append(d % extra if extra > 1 else None)
                if len(mRs) <= k_local:
                    mRs.append(None)
            if e == 0:
                status = TERMINATED
                break
            mCs.append(Cn - e)
        # splice
        Es.extend(mEs)
        Cs.extend(mCs[1:])
        if not lean:
            Gs.extend(mGs)
            Dmods.extend(mDmods)
            while len(mRs) < len(mEs):
                mRs.append(None)
            Rs.extend(mRs[: len(mEs)])
            Dexact.extend([None] * len(mEs))

    out = {
        "C": Cs,
        "E": Es,
        "status": status,
        "steps": len(Es) - 1 if Es else 0,
        "exact_steps": exact_steps,
    }
    if not lean:
        out["G"] = Gs
        out["R"] = Rs
        out["Dmod"] = Dmods
        out["Dexact"] = Dexact
    return out
