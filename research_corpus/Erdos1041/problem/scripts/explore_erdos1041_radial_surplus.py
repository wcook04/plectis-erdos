"""High-precision explorer for the Erdos 1041 GP3 radial surplus.

The GP3 derivative certificate (ThreeExteriorGreenPolarization.md) reduces to a
radial surplus inequality S >= 0 after the exact weighted-cosine minimization.
This script measures, at 60+ decimal digits:

  1. validation of the closed-form minimum M(alpha,beta,gamma) of the
     weighted cosine problem against direct two-angle numerical minimization;
  2. the full isosceles slice S(q; x, x, z) where only the local transverse
     second variation at z=x is currently proved;
  3. a Schur-convexity probe of S in log-radius coordinates on the
     product-preserving simplex, the hypothesis that would reduce the
     stationary branch to the isosceles slice;
  4. a global random search with the branch condition enforced.

No packet or Lean surface is mutated; this is a disposable evidence probe.
"""

from __future__ import annotations

import json
import math
import random
import sys

import mpmath as mp

mp.mp.dps = 60

ONE = mp.mpf(1)
HALF = mp.mpf(1) / 2


def h(q: mp.mpf, r: mp.mpf, c: mp.mpf) -> mp.mpf:
    """d/dq log rho_D(q e^{i theta}, r e^{i phi}) at cos(theta-phi)=c."""
    a = q * q + r * r - 2 * q * r * c
    b = 1 + q * q * r * r - 2 * q * r * c
    return (q - r * c) / a - (q * r * r - r * c) / b


def hc(q: mp.mpf, r: mp.mpf, c: mp.mpf) -> mp.mpf:
    """d/dc of the kernel above (strictly positive for 0<r<=q<1)."""
    a = q * q + r * r - 2 * q * r * c
    b = 1 + q * q * r * r - 2 * q * r * c
    return r * (q * q - r * r) / (a * a) + r * (1 - q * q * r * r) / (b * b)


def surplus(q: mp.mpf, radii: tuple[mp.mpf, ...]) -> dict:
    """Radial surplus on both branches at fixed (q, radii)."""
    r1, r2, r3 = radii
    total = r1 + r2 + r3
    p = r1 * r2 * r3
    rhs = total * (3 * q * q / (q**3 - p) + 3 * p * q * q / (1 - p * q**3))

    self_terms = sum(r * h(q, r, ONE) for r in radii)
    pairs = ((0, 1), (0, 2), (1, 2))
    k_half = []
    alpha = []
    for i, j in pairs:
        k_half.append(
            radii[i] * h(q, radii[j], -HALF) + radii[j] * h(q, radii[i], -HALF)
        )
        alpha.append(
            radii[i] * hc(q, radii[j], -HALF) + radii[j] * hc(q, radii[i], -HALF)
        )
    a12, a13, a23 = alpha

    # Minimum of a12*cosA + a13*cosB + a23*cosC over A+B+C=0.
    # Nested exact form: min_t in [-1,1] of a12*t - sqrt(b^2+g^2+2*b*g*t).
    # Interior stationary t* is admissible iff the reciprocals form a
    # triangle; otherwise the convex minimum sits at the endpoint whose
    # weight violates it, giving -sum(alpha) + 2*min(alpha).
    m_stat = -(a12 * a13 / a23 + a12 * a23 / a13 + a13 * a23 / a12) / 2
    m_end = -(a12 + a13 + a23) + 2 * min(alpha)
    inv = sorted([1 / a12, 1 / a13, 1 / a23], reverse=True)
    tri = inv[0] <= inv[1] + inv[2]
    base = self_terms + sum(k_half) + sum(alpha) / 2 - rhs
    s_stat = base + m_stat
    s_end = base + m_end
    return {
        "q": q,
        "radii": radii,
        "p": p,
        "rhs": rhs,
        "self_terms": self_terms,
        "pairs": sum(k_half),
        "alpha": alpha,
        "m_stat": m_stat,
        "m_end": m_end,
        "tri": tri,
        "s_stat": s_stat,
        "s_end": s_end,
        "s_operative": s_stat if tri else s_end,
    }


def m_direct(alpha: tuple[mp.mpf, ...], steps: int = 400) -> mp.mpf:
    """Direct numerical minimum of sum a_i cos(theta differences)."""
    a12, a13, a23 = alpha
    grid = [2 * mp.pi * mp.mpf(k) / steps for k in range(steps)]
    best = mp.mpf("1e30")
    arg = (mp.mpf(0), mp.mpf(0))
    for aa in grid:
        ca = mp.cos(aa)
        for bb in grid:
            val = a12 * ca + a13 * mp.cos(bb) + a23 * mp.cos(aa + bb)
            if val < best:
                best = val
                arg = (aa, bb)
    for _ in range(6):
        step = (grid[1] - grid[0]) / 2 ** (_ + 1)
        aa0, bb0 = arg
        cand = [
            (aa0 + da, bb0 + db)
            for da in (-step, mp.mpf(0), step)
            for db in (-step, mp.mpf(0), step)
        ]
        for aa, bb in cand:
            val = a12 * mp.cos(aa) + a13 * mp.cos(bb) + a23 * mp.cos(aa + bb)
            if val < best:
                best = val
                arg = (aa, bb)
    return best


def exact_residual(
    q: mp.mpf, radii: tuple[mp.mpf, ...], angles: tuple[mp.mpf, ...]
) -> mp.mpf:
    """True D'(q) at explicit angles (radians)."""
    r1, r2, r3 = radii
    p = r1 * r2 * r3
    total = r1 + r2 + r3
    rhs = total * (3 * q * q / (q**3 - p) + 3 * p * q * q / (1 - p * q**3))
    acc = sum(r * h(q, r, ONE) for r in radii)
    for i, j in ((0, 1), (0, 2), (1, 2)):
        c = mp.cos(angles[i] - angles[j])
        acc += radii[i] * h(q, radii[j], c) + radii[j] * h(q, radii[i], c)
    return acc - rhs


def experiment_validation() -> list[dict]:
    """Check M_stat / M_end against direct angular minimization."""
    random.seed(20260828)
    rows = []
    for _ in range(12):
        q = mp.mpf(random.uniform(0.15, 0.95))
        radii = tuple(mp.mpf(random.uniform(0.02, float(q))) for _ in range(3))
        info = surplus(q, radii)
        alpha = tuple(info["alpha"])
        md = m_direct(alpha)
        pred = info["m_stat"] if info["tri"] else info["m_end"]
        rows.append(
            {
                "q": float(q),
                "radii": [float(r) for r in radii],
                "tri": bool(info["tri"]),
                "m_direct": float(md),
                "m_formula": float(pred),
                "abs_err": float(abs(md - pred)),
            }
        )
    return rows


def experiment_isosceles() -> list[dict]:
    """Scan the isosceles slice S(q; x, x, z) with the branch enforced."""
    rows = []
    q_values = ["0.2", "0.35", "0.5", "0.65", "0.8", "0.9", "0.97"]
    x_fracs = [0.02, 0.1, 0.25, 0.45, 0.6, 0.75, 0.9, 0.98]
    z_fracs = [0.02, 0.1, 0.25, 0.45, 0.6, 0.75, 0.9, 0.98]
    for q_str in q_values:
        q = mp.mpf(q_str)
        worst = None
        norm_worst = None
        for xf in x_fracs:
            x = q * mp.mpf(xf)
            for zf in z_fracs:
                z = q * mp.mpf(zf)
                if x == 0 or z == 0:
                    continue
                info = surplus(q, (x, x, z))
                s = info["s_operative"]
                denom = (x - z) ** 2
                if worst is None or s < worst["s"]:
                    worst = {
                        "s": s,
                        "x": x,
                        "z": z,
                        "tri": info["tri"],
                    }
                if x != z:
                    norm = s / denom
                    if norm_worst is None or norm < norm_worst["norm"]:
                        norm_worst = {"norm": norm, "x": x, "z": z}
        rows.append(
            {
                "q": q_str,
                "min_s": float(worst["s"]),
                "at_x": float(worst["x"]),
                "at_z": float(worst["z"]),
                "tri": bool(worst["tri"]),
                "min_s_over_square": (
                    float(norm_worst["norm"]) if norm_worst else None
                ),
                "norm_at": (
                    [float(norm_worst["x"]), float(norm_worst["z"])]
                    if norm_worst
                    else None
                ),
            }
        )
    return rows


def schur_probe(q: mp.mpf, s: mp.mpf, v: tuple[mp.mpf, ...], eps: mp.mpf) -> dict:
    """Schur condition (v_i-v_j)(dS/dv_i - dS/dv_j) at in-domain log radii.

    Every sampled configuration must keep all radii <= q (the GP3 domain);
    out-of-domain stencils are rejected rather than evaluated.
    """
    def in_domain(u: tuple[mp.mpf, ...]) -> bool:
        return all(s * mp.exp(ui) <= q for ui in u)

    def at(u: tuple[mp.mpf, ...]) -> mp.mpf:
        radii = tuple(s * mp.exp(ui) for ui in u)
        return surplus(q, radii)["s_operative"]

    stencil = [tuple(v[i] + d for i in range(3)) for d in (0,)]
    stencil = [tuple(v)] + [
        tuple(v[i] + eps * (1 if k == i else 0) for i in range(3))
        for k in range(3)
    ] + [
        tuple(v[i] - eps * (1 if k == i else 0) for i in range(3))
        for k in range(3)
    ]
    if not all(in_domain(u) for u in stencil):
        return {"rejected": True}
    grads = []
    for i in range(3):
        up = list(v)
        um = list(v)
        up[i] += eps
        um[i] -= eps
        grads.append((at(tuple(up)) - at(tuple(um))) / (2 * eps))
    worst = mp.mpf(0)
    for i in range(3):
        for j in range(3):
            if i == j:
                continue
            cond = (v[i] - v[j]) * (grads[i] - grads[j])
            if cond < worst:
                worst = cond
    hess = []
    for i in range(3):
        up = list(v)
        um = list(v)
        up[i] += eps
        um[i] -= eps
        hess.append((at(tuple(up)) - 2 * at(tuple(v)) + at(tuple(um))) / (eps**2))
    return {
        "rejected": False,
        "s": at(v),
        "worst_schur": worst,
        "diag_hess": hess,
        "grads": grads,
    }


def experiment_schur() -> list[dict]:
    """Probe Schur convexity of the operative surplus on the in-domain simplex."""
    random.seed(1041)
    rows = []
    attempts = 0
    while len(rows) < 40 and attempts < 400:
        attempts += 1
        q = mp.mpf(random.uniform(0.2, 0.95))
        # Keep the whole Gaussian stencil inside the domain r<=q.
        s_rel = random.uniform(0.05, 0.6)
        s = q * mp.mpf(s_rel)
        amp = min(random.uniform(0.05, 1.2), -mp.log(mp.mpf(s_rel)) / 3)
        v = [mp.mpf(random.gauss(0, amp)) for _ in range(3)]
        v = [vi - sum(v) / 3 for vi in v]
        eps = mp.mpf("1e-12")
        probe = schur_probe(q, s, tuple(v), eps)
        if probe.get("rejected"):
            continue
        rows.append(
            {
                "q": float(q),
                "s_rel": float(s / q),
                "amp": float(amp),
                "max_exp_v": float(max(mp.exp(vi) for vi in v)),
                "s_val": float(probe["s"]),
                "worst_schur": float(probe["worst_schur"]),
                "min_diag_hess": float(min(probe["diag_hess"])),
            }
        )
    return rows


def experiment_global() -> dict:
    """Random search for negative operative surplus, branch enforced."""
    random.seed(41041)
    worst = None
    checks = 0
    endpoint_checks = 0
    endpoint_worst = None
    for _ in range(4000):
        q = mp.mpf(random.uniform(0.05, 0.995))
        radii = tuple(
            mp.mpf(random.uniform(1e-4, 1.0)) * q for _ in range(3)
        )
        info = surplus(q, radii)
        s = info["s_operative"]
        checks += 1
        if not info["tri"]:
            endpoint_checks += 1
            if endpoint_worst is None or s < endpoint_worst["s"]:
                endpoint_worst = {
                    "s": s,
                    "q": q,
                    "radii": radii,
                }
        if worst is None or s < worst["s"]:
            worst = {"s": s, "q": q, "radii": radii, "tri": info["tri"]}
    return {
        "checks": checks,
        "endpoint_checks": endpoint_checks,
        "worst": {
            "s": float(worst["s"]),
            "q": float(worst["q"]),
            "radii": [float(r) for r in worst["radii"]],
            "tri": bool(worst["tri"]),
        },
        "endpoint_worst": (
            {
                "s": float(endpoint_worst["s"]),
                "q": float(endpoint_worst["q"]),
                "radii": [float(r) for r in endpoint_worst["radii"]],
            }
            if endpoint_worst
            else None
        ),
    }


def main() -> int:
    out = {}
    out["validation"] = experiment_validation()
    out["isosceles"] = experiment_isosceles()
    out["schur"] = experiment_schur()
    out["global"] = experiment_global()
    print(
        json.dumps(
            out,
            indent=1,
            sort_keys=True,
        )
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())
