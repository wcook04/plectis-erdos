#!/usr/bin/env python3
"""Erdos 1041: Newton-flow transport of a non-admissible connector.

THE MECHANISM.  Let ``f`` be monic with all roots in the open unit disk.  Take
ANY curve ``G`` joining two roots -- it need not lie in ``{|f| < 1}`` -- and let
``M = max_G |f|``.  The Newton flow

    N_t(z) = continuation of z along the value ray  s -> e^{-s} f(z)

satisfies ``f(N_t z) = e^{-t} f(z)``, fixes every root, and therefore carries
``G`` to a curve joining the SAME two roots with ``max |f| = e^{-t} M``.
Choosing ``e^{-T} = (1 - eps)/M`` lands the transported curve strictly inside
``{|f| < 1}``.

So containment is free, and the entire obligation becomes one length:

    Lambda(G) = len(N_T G) = int_G  (|f'(z)| / (M |f'(N_T z)|)) |dz|.

The starting curve carries the budget.  Two are canonical:

  * the CHORD ``[a,b]``, of length ``|a - b| < 2``;
  * the ORIGIN broken line ``[a,0] u [0,b]``, of length ``|a| + |b| < 2``.  On
    the extremal family ``z^n - r^n`` this needs no transport at all
    (``M = r^n < 1``) and has length exactly ``2r``, so the mechanism is exact
    on the family that makes the constant 2 sharp.  It is the concrete
    realisation of TrueGeodesicLab.md's Form A -- a path OF that length by
    another route.

The pointwise contraction criterion is exact and elementary:

    d/dt log|N_t'(z)| = -Re (f/f')'(z),     (f/f')' = 1 - f f'' / (f')^2,

so the flow shortens where ``Re(1 - f f''/f'^2) >= 0``.  That criterion FAILS on
the extremal family (measured below), so the mechanism does not rest on
pointwise contraction; only the transported length matters.

A transported curve is a genuine path only when the flow does not pinch on a
critical point of modulus above the stopping level.  This probe certifies
continuity by refining until the polyline gap collapses, and reports any
transport whose gap refuses to close.

Replay:

    ./repo-python formal_math/probes/erdos1041_newton_flow_transport.py
    ./repo-python formal_math/probes/erdos1041_newton_flow_transport.py --search
    ./repo-python formal_math/probes/erdos1041_newton_flow_transport.py --json
"""

from __future__ import annotations

import argparse
import cmath
import json
import math
import random
from dataclasses import dataclass
from typing import Iterable, Sequence


# --------------------------------------------------------------------------
# polynomial in root-product form (float64; --dps switches to mpmath)
# --------------------------------------------------------------------------

_MP = None


def use_mpmath(dps: int) -> None:
    global _MP
    from mpmath import mp

    mp.dps = dps
    _MP = mp


def _one():
    return _MP.mpc(1) if _MP else 1.0 + 0j


def _zero():
    return _MP.mpc(0) if _MP else 0.0 + 0j


def fval(roots: Sequence, z):
    out = _one()
    for r in roots:
        out = out * (z - r)
    return out


def fprime(roots: Sequence, z):
    total = _zero()
    for i in range(len(roots)):
        term = _one()
        for j, r in enumerate(roots):
            if j == i:
                continue
            term = term * (z - r)
        total = total + term
    return total


def fsecond(roots: Sequence, z):
    n = len(roots)
    total = _zero()
    for i in range(n):
        for j in range(n):
            if j == i:
                continue
            term = _one()
            for k, r in enumerate(roots):
                if k == i or k == j:
                    continue
                term = term * (z - r)
            total = total + term
    return total


def contraction_rate(roots: Sequence, z) -> float:
    """Re (f/f')'(z) = Re(1 - f f''/(f')^2).  Positive => the flow shortens."""
    fp = fprime(roots, z)
    if abs(fp) == 0:
        return float("-inf")
    val = 1 - fval(roots, z) * fsecond(roots, z) / (fp * fp)
    return float(val.real if not _MP else _MP.re(val))


# --------------------------------------------------------------------------
# the Newton flow, by continuation along the value ray
# --------------------------------------------------------------------------


def flow_point(roots, z0, lam, steps: int, tol: float):
    """Continue z0 along  s -> s f(z0),  s: 1 -> lam.  Returns N_T(z0)."""
    f0 = fval(roots, z0)
    if abs(f0) == 0:
        return z0  # roots are fixed points of the flow
    z = z0
    for k in range(1, steps + 1):
        s = 1 + (lam - 1) * (k / steps)
        target = f0 * s
        for _ in range(40):
            fp = fprime(roots, z)
            if abs(fp) == 0:
                break
            dz = (fval(roots, z) - target) / fp
            z = z - dz
            if abs(dz) <= tol * max(1.0, abs(z)):
                break
    return z


def _flow_steps_for(lam: float) -> int:
    if lam >= 1.0:
        return 1
    return max(6, min(96, int(8 * math.log(1.0 / lam) + 8)))


@dataclass
class Transport:
    length: float  # integral form  int lam |f'(z)|/|f'(Nz)| |dz|
    polyline: float  # polyline through the flowed samples
    max_gap: float
    continuous: bool
    source_max: float  # M = max_G |f|
    level_max: float  # max |f| on the transported curve
    lam: float
    samples: int
    min_rate: float  # min of Re(f/f')' along the transported curve, clamped
    rate_neg_fraction: float  # share of samples where the flow stretches


def _polyline_points(vertices: Sequence, per_edge: int) -> list:
    pts: list = []
    for i in range(len(vertices) - 1):
        p, q = vertices[i], vertices[i + 1]
        for k in range(per_edge + 1):
            if i > 0 and k == 0:
                continue
            pts.append(p + (q - p) * (k / per_edge))
    return pts


def curve_max_modulus(roots, vertices, per_edge: int) -> float:
    """max |f| on the polyline, sampled then refined at every local maximum.

    A sampled maximum under-reports, and the transport scale is read off this
    number, so an under-report would put the transported curve outside
    ``{|f| < 1}``.  Every interior local maximum of the sample is therefore
    polished by golden section before the maximum is taken."""
    best = 0.0
    for i in range(len(vertices) - 1):
        p, q = vertices[i], vertices[i + 1]

        def g(t: float) -> float:
            return float(abs(fval(roots, p + (q - p) * t)))

        ts = [k / per_edge for k in range(per_edge + 1)]
        vs = [g(t) for t in ts]
        best = max(best, vs[0], vs[-1])
        for k in range(1, per_edge):
            if vs[k] >= vs[k - 1] and vs[k] >= vs[k + 1]:
                lo, hi = ts[k - 1], ts[k + 1]
                phi = (math.sqrt(5.0) - 1) / 2
                a2, b2 = hi - phi * (hi - lo), lo + phi * (hi - lo)
                fa, fb = g(a2), g(b2)
                for _ in range(60):
                    if fa < fb:
                        lo, a2, fa = a2, b2, fb
                        b2 = lo + phi * (hi - lo)
                        fb = g(b2)
                    else:
                        hi, b2, fb = b2, a2, fa
                        a2 = hi - phi * (hi - lo)
                        fa = g(a2)
                    if hi - lo < 1e-15:
                        break
                best = max(best, fa, fb)
    return best


def transport(
    roots,
    vertices: Sequence,
    *,
    per_edge: int = 32,
    eps: float = 1e-9,
    gap_tol: float = 2e-3,
    max_points: int = 3000,
    newton_tol: float = 1e-14,
    scan: int = 512,
) -> Transport:
    """Transport the polyline ``vertices`` down to level ``1 - eps``."""
    src_max = curve_max_modulus(roots, vertices, max(per_edge, scan))
    one = 1.0 - eps
    lam = 1.0 if src_max <= one else one / src_max
    steps = _flow_steps_for(lam)

    pts = _polyline_points(vertices, per_edge)
    flowed = [flow_point(roots, p, lam, steps, newton_tol) for p in pts]

    stalled = False
    while len(pts) < max_points:
        worst = 0.0
        new_pts = [pts[0]]
        new_flowed = [flowed[0]]
        added = 0
        for i in range(len(pts) - 1):
            gap = abs(flowed[i + 1] - flowed[i])
            worst = max(worst, gap)
            if gap > gap_tol:
                mid = (pts[i] + pts[i + 1]) / 2
                new_pts.append(mid)
                new_flowed.append(flow_point(roots, mid, lam, steps, newton_tol))
                added += 1
            new_pts.append(pts[i + 1])
            new_flowed.append(flowed[i + 1])
        if added == 0:
            break
        prev_worst = worst
        pts, flowed = new_pts, new_flowed
        worst_after = max(
            abs(flowed[i + 1] - flowed[i]) for i in range(len(flowed) - 1)
        )
        if worst_after > 0.9 * prev_worst and worst_after > gap_tol:
            stalled = True
            break

    poly_len = 0.0
    max_gap = 0.0
    for i in range(len(flowed) - 1):
        g = abs(flowed[i + 1] - flowed[i])
        poly_len += float(g)
        max_gap = max(max_gap, float(g))

    integral = 0.0
    for i in range(len(pts) - 1):
        dz = abs(pts[i + 1] - pts[i])
        acc = 0.0
        for idx in (i, i + 1):
            fp_dst = fprime(roots, flowed[idx])
            if abs(fp_dst) == 0:
                acc = float("inf")
                break
            acc += lam * float(abs(fprime(roots, pts[idx])) / abs(fp_dst))
        integral += float(dz) * acc / 2

    level_max = max(float(abs(fval(roots, z))) for z in flowed)
    rates = [contraction_rate(roots, z) for z in flowed]
    min_rate = max(min(rates), -1e12)
    rate_neg_fraction = sum(1 for r in rates if r < 0) / len(rates)
    continuous = (not stalled) and max_gap <= gap_tol * 4

    return Transport(
        length=integral,
        polyline=poly_len,
        max_gap=max_gap,
        continuous=continuous,
        source_max=float(src_max),
        level_max=level_max,
        lam=float(lam),
        samples=len(pts),
        min_rate=min_rate,
        rate_neg_fraction=rate_neg_fraction,
    )


# --------------------------------------------------------------------------
# configurations
# --------------------------------------------------------------------------


def extremal(n: int, r: float) -> list:
    return [r * cmath.exp(2j * math.pi * k / n) for k in range(n)]


#: quintic at which four of five origin spokes provably exit (Form A' fails).
ORIGIN_SPOKE_QUINTIC: tuple[tuple[int, int], ...] = (
    (9999, 0),
    (1999, 9899),
    (-2799, 9599),
    (-9599, -2799),
    (1999, -9899),
)


def load_qc_witnesses() -> dict[int, list]:
    """Read the stored bit-exact QC witnesses from their owning script."""
    import importlib.util
    import pathlib

    root = pathlib.Path(__file__).resolve().parents[2]
    src = (
        root
        / "formal_math"
        / "erdos257_period_noncollapse"
        / "ErdosProblems"
        / "Erdos1041"
        / "scripts"
        / "check_erdos1041_straight_spoke_hub_criterion.py"
    )
    if not src.exists():
        return {}
    spec = importlib.util.spec_from_file_location("_ssh_criterion", src)
    if spec is None or spec.loader is None:
        return {}
    mod = importlib.util.module_from_spec(spec)
    try:
        spec.loader.exec_module(mod)
    except Exception:
        return {}
    out: dict[int, list] = {}
    for degree, literals in getattr(mod, "QC_REFUTATION_WITNESSES", {}).items():
        out[int(degree)] = [
            complex(float.fromhex(re), float.fromhex(im)) for re, im in literals
        ]
    return out


def chord_or_origin_cubic() -> list:
    """L(7+-24i)/25, -L with L = 999/1000: no safe chord and at most one safe
    origin spoke.  TwoSegmentContainmentReduction.md section 2."""
    L = 0.999
    return [L * complex(7, 24) / 25, L * complex(7, -24) / 25, complex(-L, 0)]


def near_fekete(n: int, eps: float, shift: Sequence[float]) -> list:
    r = 1 - eps
    return [
        r * cmath.exp(1j * (2 * math.pi * k / n + shift[k % len(shift)]))
        for k in range(n)
    ]


@dataclass
class Config:
    name: str
    roots: list
    note: str = ""


_SHIFT = (0.0, 4e-4, -2e-4, 7e-4, -5e-4, 3e-4, 0.0, -8e-4, 6e-4)


def build_configs(include_sweeps: bool) -> list[Config]:
    cfgs: list[Config] = []
    for n in (3, 4, 5, 6, 8):
        for r in (0.9, 0.99, 0.999, 0.9999):
            cfgs.append(
                Config(f"extremal_n{n}_r{r}", extremal(n, r), "z^n - r^n, sharp family")
            )
    cfgs.append(
        Config(
            "origin_spoke_quintic",
            [complex(a, b) / 10000 for a, b in ORIGIN_SPOKE_QUINTIC],
            "4 of 5 origin spokes exit; Form A' fails here",
        )
    )
    cfgs.append(
        Config(
            "chord_or_origin_cubic",
            chord_or_origin_cubic(),
            "no safe chord and <=1 safe origin spoke; minimal degree",
        )
    )
    for degree, roots in sorted(load_qc_witnesses().items()):
        cfgs.append(
            Config(
                f"qc_witness_n{degree}",
                roots,
                "no admissible critical hub carries two contained spokes",
            )
        )
    if include_sweeps:
        for n in (3, 4, 5, 6):
            for e in (1e-3, 1e-5, 1e-7):
                cfgs.append(
                    Config(
                        f"near_fekete_n{n}_eps{e:g}",
                        near_fekete(n, e, _SHIFT),
                        "perturbed regular gon at radius 1-eps",
                    )
                )
    return cfgs


# --------------------------------------------------------------------------
# objectives
# --------------------------------------------------------------------------


def best_transport(
    roots, *, per_edge: int = 32, use_origin: bool = True, scan: int = 512,
    gap_tol: float = 2e-3, max_points: int = 3000,
) -> dict:
    """min over pairs and over the two canonical starting curves of the
    transported length, restricted to transports certified continuous."""
    n = len(roots)
    best = None
    form_a_slack = float("inf")
    worst_gap = 0.0
    min_rate = float("inf")
    for i in range(n):
        for j in range(i + 1, n):
            a, b = roots[i], roots[j]
            cands = [("chord", [a, b], abs(a - b))]
            if use_origin:
                cands.append(("origin", [a, _zero(), b], abs(a) + abs(b)))
            for kind, verts, budget in cands:
                tr = transport(
                    roots, verts, per_edge=per_edge, scan=scan,
                    gap_tol=gap_tol, max_points=max_points,
                )
                worst_gap = max(worst_gap, tr.max_gap)
                min_rate = min(min_rate, tr.min_rate)
                if not tr.continuous or not math.isfinite(tr.length):
                    continue
                if kind == "origin":
                    form_a_slack = min(form_a_slack, tr.length - float(budget))
                rec = {
                    "kind": kind,
                    "pair": (i, j),
                    "length": tr.length,
                    "polyline": tr.polyline,
                    "budget": float(budget),
                    "source_max": tr.source_max,
                    "level_max": tr.level_max,
                    "gap": tr.max_gap,
                    "samples": tr.samples,
                }
                if best is None or rec["length"] < best["length"]:
                    best = rec
    return {
        "best": best,
        "form_a_min_slack": form_a_slack,
        "max_gap_any": worst_gap,
        "min_contraction_rate": min_rate,
    }


def control_untransported_origin(roots) -> float:
    """NEGATIVE CONTROL.  Form A': min over pairs of |a|+|b| subject to BOTH
    straight origin spokes lying in {|f| <= 1}.  Known false (the quintic).
    Returns +inf when no pair qualifies."""
    n = len(roots)
    best = float("inf")
    for i in range(n):
        for j in range(i + 1, n):
            a, b = roots[i], roots[j]
            ok = True
            for e in (a, b):
                if curve_max_modulus(roots, [_zero(), e], 400) > 1.0:
                    ok = False
                    break
            if ok:
                best = min(best, float(abs(a) + abs(b)))
    return best


# --------------------------------------------------------------------------
# the extremal family in closed form: no branch tracking at all
# --------------------------------------------------------------------------


def extremal_transported_chord(n: int, r: float, j: int = 1, K: int = 200001):
    """Transported chord length on ``z^n - r^n`` from the closed form.

    Here ``zeta^n = r^n + lam (z^n - r^n)`` determines ``|zeta|`` outright, so
    the stretch ``lam |z/zeta|^{n-1}`` involves no branch continuation and no
    Newton solve.  This is the independent method behind the elimination in
    NewtonFlowTransport.md section 5.  The integrand has an integrable
    ``|t-1/2|^{-(n-1)/n}`` singularity at ``r = 1``; the mesh is cubically
    graded about the midpoint to resolve it."""
    w = cmath.exp(2j * math.pi * j / n)
    a, b = r, r * w

    def zz(t: float):
        return a + (b - a) * t

    src = max(abs(zz(k / 20000) ** n - r**n) for k in range(20001))
    closed = r**n * (1 + abs(math.cos(math.pi * j / n)) ** n)
    # A curve already inside the lemniscate needs NO transport.  Omitting this
    # clamp flows it UPWARD to level one and lengthens it, which is what made
    # an earlier pass report a spurious elimination at n = 4: for even n the
    # diametral chord IS the origin broken line, with M = r^n < 1.
    lam = min(1.0, 1.0 / src)
    total = 0.0
    prev = None
    for k in range(K):
        u = -1.0 + 2.0 * k / (K - 1)
        t = 0.5 + 0.5 * math.copysign(abs(u) ** 3, u)
        z = zz(t)
        # d = r^n + lam(z^n - r^n) rearranged so that r^n does not cancel
        # against lam*r^n.  The naive form loses every digit when lam is near
        # one and the chord passes through the origin (the diametral pair at
        # even n), which is where an earlier pass produced a 4.5e4 "length".
        d = r**n * (1.0 - lam) + lam * z**n
        if abs(d) == 0.0:
            continue
        g = abs(z) ** (n - 1) / abs(d) ** ((n - 1) / n)
        if prev is not None:
            total += 0.5 * (g + prev[1]) * (t - prev[0])
        prev = (t, g)
    length = 2 * r * math.sin(math.pi * j / n) * lam * total
    return {
        "n": n,
        "r": r,
        "j": j,
        "length": length,
        "source_max_sampled": src,
        "source_max_closed_form": closed,
        "midpoint_closed_form_error": abs(src - closed),
        "origin_path_length": 2 * r,
    }


def extremal_closed_form_report() -> dict:
    """Reproduces NewtonFlowTransport.md section 5."""
    rs = (0.9, 0.99, 0.999, 0.9999, 0.999999, 1.0)
    grid = []
    for n in (3, 4, 5, 6, 8, 10):
        grid.append(
            {"n": n, "r_values": list(rs),
             "lengths": [extremal_transported_chord(n, r)["length"] for r in rs]}
        )
    sharp = []
    for n in (3, 4, 5, 6, 8, 10):
        vals = [extremal_transported_chord(n, 1 - 1e-9, j)["length"]
                for j in range(1, n // 2 + 1)]
        sharp.append({"n": n, "per_pair": vals, "best": min(vals),
                      "exceeds_two": min(vals) > 2.0})
    lemma = [extremal_transported_chord(n, 0.999) for n in (3, 4, 6, 10)]
    return {
        "grid": grid,
        "sharp_limit": sharp,
        "chord_maximum_lemma": [
            {"n": d["n"], "sampled": d["source_max_sampled"],
             "closed_form": d["source_max_closed_form"],
             "error": d["midpoint_closed_form_error"]}
            for d in lemma
        ],
        "eliminated_degrees": [d["n"] for d in sharp if d["exceeds_two"]],
    }


# --------------------------------------------------------------------------
# adversarial search: try to push the objective above 2
# --------------------------------------------------------------------------


def _project(z, cap: float):
    m = abs(z)
    return z if m <= cap else z * (cap / m)


def adversarial_search(
    n: int,
    *,
    objective: str,
    restarts: int,
    steps: int,
    per_edge: int,
    cap: float = 1 - 1e-9,
    seed: int = 20260824,
) -> dict:
    rng = random.Random(seed + 1000 * n + (0 if objective == "transport" else 7))

    def score(roots) -> float:
        if objective == "transport":
            res = best_transport(
                roots, per_edge=per_edge, scan=96, gap_tol=6e-3, max_points=700
            )
            return res["best"]["length"] if res["best"] else float("inf")
        return control_untransported_origin(roots)

    def seeds() -> list:
        out = [extremal(n, cap)]
        out.append(near_fekete(n, 1e-7, _SHIFT[:n] if n <= len(_SHIFT) else _SHIFT))
        while len(out) < restarts:
            out.append(
                [
                    _project(
                        cmath.rect(cap * rng.random() ** 0.35, 2 * math.pi * rng.random()),
                        cap,
                    )
                    for _ in range(n)
                ]
            )
        return out[:restarts]

    best_score = -1.0
    best_roots = None
    for start in seeds():
        roots = list(start)
        cur = score(roots)
        scale = 0.08
        for _ in range(steps):
            cand = [
                _project(z + cmath.rect(scale * rng.random(), 2 * math.pi * rng.random()), cap)
                for z in roots
            ]
            val = score(cand)
            if val > cur:
                roots, cur = cand, val
            else:
                scale *= 0.93
                if scale < 1e-7:
                    break
        if cur > best_score:
            best_score, best_roots = cur, roots
    return {
        "degree": n,
        "objective": objective,
        "sup": best_score,
        "exceeds_two": bool(best_score > 2.0),
        "roots": [[z.real, z.imag] for z in (best_roots or [])],
    }


# --------------------------------------------------------------------------


def main(argv: Iterable[str] | None = None) -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--dps", type=int, default=0, help="mpmath digits (0 = float64)")
    ap.add_argument("--per-edge", type=int, default=32)
    ap.add_argument("--no-sweeps", action="store_true")
    ap.add_argument("--only", default=None)
    ap.add_argument("--search", action="store_true")
    ap.add_argument("--extremal-closed-form", action="store_true")
    ap.add_argument("--search-degrees", default="3,4,5,6")
    ap.add_argument("--restarts", type=int, default=4)
    ap.add_argument("--steps", type=int, default=40)
    ap.add_argument("--json", action="store_true")
    args = ap.parse_args(list(argv) if argv is not None else None)

    if args.dps:
        use_mpmath(args.dps)

    cfgs = build_configs(include_sweeps=not args.no_sweeps)
    if args.only:
        cfgs = [c for c in cfgs if args.only in c.name]

    rows = []
    failures: list[list[str]] = []
    for cfg in cfgs:
        res = best_transport(cfg.roots, per_edge=args.per_edge)
        best = res["best"]
        if best is None:
            failures.append(["no_continuous_transport", cfg.name])
            rows.append({"name": cfg.name, "degree": len(cfg.roots), "best": None})
            continue
        row = {
            "name": cfg.name,
            "note": cfg.note,
            "degree": len(cfg.roots),
            "max_root_modulus": max(float(abs(r)) for r in cfg.roots),
            "winner": best["kind"],
            "pair": list(best["pair"]),
            "transported_length": best["length"],
            "polyline_length": best["polyline"],
            "start_budget": best["budget"],
            "source_max_modulus": best["source_max"],
            "transported_level_max": best["level_max"],
            "margin_below_two": 2.0 - best["length"],
            "vs_radius_bound": best["length"]
            - 2 * max(float(abs(r)) for r in cfg.roots),
            "form_a_min_slack": res["form_a_min_slack"],
            "min_contraction_rate": res["min_contraction_rate"],
            "max_gap": best["gap"],
            "samples": best["samples"],
        }
        rows.append(row)
        if not (row["transported_length"] < 2.0):
            failures.append(["transported_not_below_two", cfg.name])
        if row["transported_level_max"] >= 1.0:
            failures.append(["transported_curve_not_interior", cfg.name])
        if abs(row["transported_length"] - row["polyline_length"]) > 5e-3 * max(
            1.0, row["transported_length"]
        ):
            failures.append(["integral_polyline_mismatch", cfg.name])

    searches = []
    if args.search:
        degs = [int(x) for x in args.search_degrees.split(",") if x.strip()]
        for n in degs:
            searches.append(
                adversarial_search(
                    n,
                    objective="transport",
                    restarts=args.restarts,
                    steps=args.steps,
                    per_edge=max(16, args.per_edge // 2),
                )
            )
            searches.append(
                adversarial_search(
                    n,
                    objective="control_form_a_prime",
                    restarts=args.restarts,
                    steps=args.steps,
                    per_edge=max(16, args.per_edge // 2),
                )
            )
        for s in searches:
            if s["objective"] == "transport" and s["exceeds_two"]:
                failures.append(["search_broke_transport", f"n={s['degree']}"])
        controls = [s for s in searches if s["objective"] != "transport"]
        if controls and not any(s["exceeds_two"] for s in controls):
            failures.append(["negative_control_did_not_break", "control_form_a_prime"])

    extremal_cf = extremal_closed_form_report() if args.extremal_closed_form else None
    if extremal_cf is not None:
        # the elimination is the expected outcome, not a failure of the probe;
        # what WOULD be a failure is the closed form drifting off the lemma.
        for row in extremal_cf["chord_maximum_lemma"]:
            if row["error"] > 1e-12:
                failures.append(["chord_maximum_lemma_drift", f"n={row['n']}"])
        if extremal_cf["eliminated_degrees"] != [3]:
            failures.append(
                ["chord_elimination_degrees_changed",
                 str(extremal_cf["eliminated_degrees"])]
            )

    payload = {
        "probe": "erdos1041_newton_flow_transport",
        "extremal_closed_form": extremal_cf,
        "precision": f"mpmath dps={args.dps}" if args.dps else "float64",
        "configurations": rows,
        "searches": searches,
        "failures": failures,
        "status": "ok" if not failures else "violation",
    }
    if args.json:
        print(json.dumps(payload, indent=2))
        return 0 if not failures else 1

    hdr = (
        f"{'configuration':24s} {'n':>2s} {'win':>6s} {'srcMax':>8s} "
        f"{'budget':>8s} {'transported':>12s} {'2-L':>8s} {'L-2R':>9s} "
        f"{'FormA':>9s} {'minRate':>10s} {'gap':>8s}"
    )
    print(hdr)
    print("-" * len(hdr))
    for r in rows:
        if r.get("best", 0) is None:
            print(f"{r['name']:24s} {r['degree']:2d}   NO CONTINUOUS TRANSPORT")
            continue
        fa = r["form_a_min_slack"]
        fas = "     inf" if not math.isfinite(fa) else f"{fa:9.5f}"
        print(
            f"{r['name']:24s} {r['degree']:2d} {r['winner']:>6s} "
            f"{r['source_max_modulus']:8.5f} {r['start_budget']:8.5f} "
            f"{r['transported_length']:12.6f} {r['margin_below_two']:8.5f} "
            f"{r['vs_radius_bound']:9.5f} {fas} "
            f"{r['min_contraction_rate']:10.2f} {r['max_gap']:8.1e}"
        )
    if extremal_cf:
        print()
        print("Extremal family z^n - r^n, transported adjacent chord, closed form:")
        head = f"{'n':>3s} " + " ".join(f"{('r=' + str(r)):>12s}"
                                        for r in extremal_cf["grid"][0]["r_values"])
        print(head)
        for row in extremal_cf["grid"]:
            print(f"{row['n']:3d} " + " ".join(f"{v:12.6f}" for v in row["lengths"]))
        print()
        print("  sharp limit r = 1 - 1e-9, minimised over ALL pairs:")
        for row in extremal_cf["sharp_limit"]:
            mark = "ABOVE 2 -- chord transport eliminated" if row["exceeds_two"] else ""
            print(f"    n={row['n']:2d}  best={row['best']:.6f}   {mark}")
        print(f"  chord-maximum lemma max error: "
              f"{max(r['error'] for r in extremal_cf['chord_maximum_lemma']):.2e}")
    if searches:
        print()
        print(f"{'objective':22s} {'n':>2s} {'sup':>12s} {'>2?':>5s}")
        print("-" * 45)
        for s in searches:
            sup = s["sup"]
            sups = "inf" if not math.isfinite(sup) else f"{sup:12.7f}"
            print(f"{s['objective']:22s} {s['degree']:2d} {sups:>12s} "
                  f"{'YES' if s['exceeds_two'] else 'no':>5s}")
    print()
    print(f"configurations: {len(rows)}   failures: {len(failures)}")
    for kind, name in failures:
        print(f"  FAIL {kind}: {name}")
    return 0 if not failures else 1


if __name__ == "__main__":
    raise SystemExit(main())
