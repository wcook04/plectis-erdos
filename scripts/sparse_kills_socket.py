r"""Sparse E KILLS the socket -- the sparse/dense dichotomy runs the other way.

WHY THIS EXISTS (the analysis it is bound to)
---------------------------------------------
Section 66 proved the socket criterion: for `A = N \ E`, `Odd_A = Sq XOR Odd_E`, so the
socket mechanism kills `A` iff `Odd_E` is SYNDETIC.  The obvious next question is whether
the OPEN class (aperiodic AND not base-adapted) can be reached through the escape door --
an `E` whose `Odd_E` has unbounded gaps.

The intuition going in was: SPARSE `E` makes `tau_E(m) = 0` for almost every `m`, so
`Odd_E` is thin, so the socket SURVIVES.  **That intuition is exactly backwards**, and one
line of algebra says so before any computation.

THE ALGEBRA (derived first; this run is a CHECK)
------------------------------------------------
    Odd_E  =  {m : tau_E(m) odd}  CONTAINS  {m : tau_E(m) = 1}.

Let `e1 = min E`.  If `m` is a multiple of `e1` divisible by NO other element of `E`, then
`tau_E(m) = 1` exactly -- **ODD** -- so `m in Odd_E`.  Sparsity does not make `tau_E` even;
it makes `tau_E` equal to ONE, which is the worst possible parity.  The sparser `E` is, the
larger the fraction of `e1 N` on which `tau_E = 1`, and `e1 N` is syndetic with gap `e1`.

Contrast `E = 4N`, which is NOT sparse: every multiple of 4 lies in `E`, so
`tau_{4N}(m) = d(m/4)`, typically LARGE and EVEN, odd only at `m = 4k^2` (section 66).
**Density in a progression, not sparsity, is what makes `tau_E` even.**

Consequently socket SURVIVAL demands that almost every multiple of `min E` carry a SECOND
divisor in `E` -- a strong covering demand on `E`, and exactly the demand that makes
`N \ E` periodic.

PREDICTIONS, RECORDED BEFORE THE RUN
------------------------------------
P1  Every sparse family (`{2^i}`, `{2^(2^i)}`, `{k!}`, `{k^2}`) has `Odd_E` SYNDETIC with
    gap comparable to `min E` -- socket KILLS.  This refutes the sparse-survives intuition.
P2  `4N` and `6N` have NON-syndetic `Odd_E` (gaps growing like `sqrt(M)`), so the socket
    survives -- but `N \ 4N` and `N \ 6N` are eventually PERIODIC, hence already settled by
    solved class (i).  Surviving one mechanism is not surviving the problem (T45b).
P3  Perturbing a survivor by a sparse `S` RESTORES death: by `F_2`-linearity
    `Odd_{P XOR S} = Odd_P XOR Odd_S`, and a syndetic `Odd_S` dominates a sparse `Odd_P`.

FALSIFIER, stated before the run: any tested `E` with GROWING `maxgap(Odd_E)` whose
`N \ E` is aperiodic.  That would inhabit the gap and open the lane.  If none appears, the
honest verdict is a NARROWING, not a proof of emptiness.

PARAMETER BOX: `M = 120000`, gaps measured to `m <= 60000`.  The sparse families are
INFINITE as families but only their truncations below `M` are exercised here; a finite
truncation of an aperiodic family is eventually periodic, so aperiodicity is a property of
the family, not of what this run sees.

Bound directions, per the standing infrastructure rule:
  analysis -> here : CertificateSocketCollapse.md section 66 (the socket criterion),
                     cross-index T30 (F_2 linearity), T45b (necessary not sufficient)
  here -> analysis : CertificateSocketCollapse.md section 67, receipt under state/
"""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path

REPO = Path(__file__).resolve().parents[3]


def tau_of(E, M):
    t = [0] * (M + 1)
    for a in E:
        if 1 <= a <= M:
            for m in range(a, M + 1, a):
                t[m] += 1
    return t


def maxgap_odd(t, hi):
    last, g = None, 0
    for m in range(2, hi + 1):
        if t[m] & 1:
            if last is not None:
                g = max(g, m - last)
            last = m
    return g


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--M", type=int, default=120000)
    ap.add_argument("--hi", type=int, default=60000)
    ap.add_argument("--out", default=None)
    args = ap.parse_args()
    M, HI = args.M, args.hi

    sieve = [True] * (M + 1)
    sieve[0] = sieve[1] = False
    for p in range(2, int(M ** 0.5) + 1):
        if sieve[p]:
            for x in range(p * p, M + 1, p):
                sieve[x] = False
    primes = [p for p in range(2, M + 1) if sieve[p]]

    fact, f, k = [], 1, 1
    while f <= M:
        fact.append(f)
        k += 1
        f *= k
    fact = [x for x in fact if x >= 2]
    dbl = [2 ** (2 ** i) for i in range(0, 6) if 2 ** (2 ** i) <= M]
    fourN, sixN = list(range(4, M + 1, 4)), list(range(6, M + 1, 6))

    fams = {
        "sparse_pow2":      ([2 ** i for i in range(1, 18) if 2 ** i <= M], "sparse", False),
        "sparse_dbl_exp":   (dbl, "sparse", False),
        "sparse_factorial": (fact, "sparse", False),
        "sparse_squares":   ([j * j for j in range(2, int(M ** 0.5) + 1)], "sparse", False),
        "primes":           (primes, "sparse", False),
        "dense_4N":         (fourN, "dense_in_progression", True),
        "dense_6N":         (sixN, "dense_in_progression", True),
        "4N_xor_sparse":    (sorted(set(fourN) ^ set(x for x in dbl if x >= 4)), "perturbed", False),
        "6N_xor_factorial": (sorted(set(sixN) ^ set(fact)), "perturbed", False),
    }

    report = {"M": M, "hi": HI, "families": {}}
    for name, (E, kind, periodic) in fams.items():
        t = tau_of(E, M)
        g = maxgap_odd(t, HI)
        dens = sum(1 for m in range(2, HI + 1) if t[m] & 1) / HI
        one = sum(1 for m in range(2, HI + 1) if t[m] == 1) / HI
        report["families"][name] = {
            "kind": kind, "min_E": min(E), "maxgap_Odd_E": g,
            "density_Odd_E": round(dens, 4), "density_tau_eq_1": round(one, 4),
            "socket": "KILLS" if 0 < g <= 64 else "survives_in_range",
            "complement_eventually_periodic": periodic,
        }

    F = report["families"]
    report["P1_sparse_kills"] = all(
        F[n]["socket"] == "KILLS" for n in F if F[n]["kind"] == "sparse")
    report["P2_dense_survives_but_periodic"] = all(
        F[n]["socket"] == "survives_in_range" and F[n]["complement_eventually_periodic"]
        for n in F if F[n]["kind"] == "dense_in_progression")
    report["P3_perturbation_restores_death"] = all(
        F[n]["socket"] == "KILLS" for n in F if F[n]["kind"] == "perturbed")
    report["gap_inhabited"] = any(
        F[n]["socket"] == "survives_in_range" and not F[n]["complement_eventually_periodic"]
        for n in F)
    report["falsifier_survived"] = not report["gap_inhabited"]

    out = args.out or str(
        REPO / "state/formal_math/erdos257_period_noncollapse/sparse_kills_socket_receipt.json")
    Path(out).parent.mkdir(parents=True, exist_ok=True)
    blob = json.dumps(report, indent=2, sort_keys=True)
    Path(out).write_text(blob)

    print(f"M={M} gaps to m<={HI}")
    print(f"{'family':<18} {'kind':<21} {'minE':>5} {'gap':>6} {'dens':>7} {'tau=1':>7}  socket")
    for n, c in report["families"].items():
        print(f"{n:<18} {c['kind']:<21} {c['min_E']:>5} {c['maxgap_Odd_E']:>6} "
              f"{c['density_Odd_E']:>7} {c['density_tau_eq_1']:>7}  {c['socket']}")
    for k_ in ("P1_sparse_kills", "P2_dense_survives_but_periodic",
               "P3_perturbation_restores_death", "gap_inhabited"):
        print(f"{k_:<34} = {report[k_]}")
    print(f"wrote {out} sha256={hashlib.sha256(blob.encode()).hexdigest()}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
