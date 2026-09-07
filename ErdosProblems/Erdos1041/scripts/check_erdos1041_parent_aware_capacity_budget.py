#!/usr/bin/env python3
"""Receipt for LastLobeCapacityLaw.md section 4 (parent-aware budget no-go).

QUESTION (posed by AdmissibleCriticalArcProductLab.md after its hybrid-graft
falsifier): can a parent-aware area/capacity budget repay the observed graft
debt -- i.e. can a sharper AREA INPUT rescue the proof template "replace each
certified cherry factor by its rigorous Bergman--Polya bound and multiply"?

INSTRUMENT.  The kappa-coupled cherry certificate: for a simple cherry with
birth beta, parent cut b, ratio r = beta/b, and two-root component U_t at any
regular level t in (beta, b),

    h_v  <=  kappa_t * t^(1/n) * sqrt(artanh(beta/t)) / r^(1/n),       (KC)

where kappa_t = cap(U_t)/t^(1/n) is the EXACT component capacity ratio of
ComponentCapacityFormula.md Theorem 1.  (KC) composes three proved pieces:
the Bergman segment bound at level t, the isoperimetric Area <= pi cap^2, and
the exact capacity.  The lab's (CB4) is the special case
kappa_t <= (n-1)^(-1/n) (the exterior-Blaschke fibre gap), t -> b.  Since
Theorem 1 is an identity, (KC) at t -> b is the OPTIMAL area-input form of the
cherry certificate: no further area/capacity refinement exists.

ARMS
  FALSIFIER  replay the stress cubic's lab values exactly.
  KC         evaluate (KC) over levels; the decision gate: even the optimal
             area input leaves the hybrid product above one.
  SATURATE   measure kappa * 2^(1/3) at t just below the parent merge on the
             falsifier and on extra cubics.  LastLobeCapacityLaw.md proves the
             limit is exactly 1 for every cubic whose top merge hangs a single
             root: kappa -> (1/2)^(1/3), which at n = 3 coincides with the
             exterior-Blaschke gap (n-1)^(-1/n).  The insufficiency is
             therefore structural, not numerical.
  CONTROL    a second cubic with a very different cherry ratio r: the law pins
             its parent-cut kappa at the same 2^(-1/3), confirming
             configuration-independence where a naive reading of the KAPPA arm
             of check_erdos1041_component_capacity.py (bulk values 0.39-0.58,
             measured far below the parent cut) would predict small kappa.

Every number is float at the solver resolution measured by the CAL arm of
check_erdos1041_component_capacity.py (1.2e-4 relative).  Survival of a gate is
measurement, not proof; Erdos #1041 remains open.
"""
from __future__ import annotations

import importlib.util
import math
import os
import sys

import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))


def _load(name: str, filename: str):
    spec = importlib.util.spec_from_file_location(name, os.path.join(HERE, filename))
    mod = importlib.util.module_from_spec(spec)
    sys.modules[name] = mod
    spec.loader.exec_module(mod)
    return mod


cap_mod = _load("_pacb_cap", "check_erdos1041_component_capacity.py")
lab_mod = _load("_pacb_lab", "check_erdos1041_admissible_critical_arc_product.py")

FALSIFIER = np.array(
    [
        0.027647095206652 + 0.073111096775191j,
        -0.069742851100732 - 0.659321277291393j,
        0.670877914107613 - 0.436422467336396j,
    ],
    dtype=complex,
)

LAB_SQRT_B = 0.514126276899
LAB_GRAFT = 2.091848616726
LAB_CHERRY_H = 0.401184511995


def cherry_and_graft(roots: np.ndarray):
    """Merge rows of a cubic: (cherry_row, graft_row, beta, b, r) or None."""
    rows = lab_mod.merging_pair_tree(roots)
    if rows is None or len(rows) != len(roots) - 1:
        return None
    rows = sorted(rows, key=lambda row: float(row["critical_value_modulus"]))
    cherry, graft = rows[0], rows[-1]
    beta = float(cherry["critical_value_modulus"])
    b = min(float(graft["critical_value_modulus"]), 1.0)
    if not (0 < beta < b):
        return None
    return cherry, graft, beta, b, beta / b


def kappa_at(roots: np.ndarray, t: float, seed_root: int,
             expect_pair: list[int]) -> float | None:
    n = len(roots)
    zs = cap_mod.trace_boundary(roots, t, seed_root, 2)
    if zs is None:
        return None
    inside = sorted(j for j in range(n) if cap_mod.winding(zs, roots[j]) != 0)
    if inside != sorted(expect_pair):
        return None
    cap, _, _ = cap_mod.equilibrium(zs)
    return cap / t ** (1.0 / n)


def arm_falsifier():
    print("  FALSIFIER  replay the lab's stress cubic")
    n = len(FALSIFIER)
    data = cherry_and_graft(FALSIFIER)
    assert data is not None, "merge tree not recovered"
    cherry, graft, beta, b, r = data
    L_cherry = float(cherry["total_length"])
    L_graft = float(graft["total_length"])
    h_cherry = (L_cherry / 2.0) / r ** (1.0 / n)
    graft_factor = (L_graft / 2.0) / b ** (2.0 / n)
    sqrt_b_lab = math.sqrt(
        b ** (2.0 / n)
        * math.log((1.0 + r) / (1.0 - r))
        / (2.0 * ((n - 1.0) * r) ** (2.0 / n))
    )
    print(f"       beta {beta:.12f}  b {b:.12f}  r {r:.12f}")
    print(f"       h_cherry {h_cherry:.12f}  graft {graft_factor:.12f}  "
          f"sqrt(B_lab) {sqrt_b_lab:.12f}")
    ok = (
        abs(sqrt_b_lab - LAB_SQRT_B) < 1e-6
        and abs(graft_factor - LAB_GRAFT) < 1e-6
        and abs(h_cherry - LAB_CHERRY_H) < 1e-6
    )
    return ok, (cherry, graft, beta, b, r, graft_factor, sqrt_b_lab)


def arm_kc(state):
    cherry, graft, beta, b, r, graft_factor, sqrt_b_lab = state
    n = len(FALSIFIER)
    pair = [int(i) for i in cherry["root_pair"]]
    need = 1.0 / graft_factor
    print("  KC  kappa-coupled certificate over the cherry lifetime")
    print(f"       bound needed to repay the graft: {need:.9f}")
    best_bound = math.inf
    best = None
    kap_last = None
    for frac in (0.30, 0.60, 0.85, 0.95, 0.99, 0.999):
        t = beta + frac * (b - beta)
        kap = kappa_at(FALSIFIER, t, pair[0], pair)
        if kap is None:
            print(f"       t/b {t / b:.6f}  untraceable/misclassified; skip")
            continue
        q = beta / t
        bound = kap * t ** (1.0 / n) * math.sqrt(math.atanh(q)) / r ** (1.0 / n)
        print(f"       t/b {t / b:.6f}  kappa {kap:.6f}  bound(h) {bound:.6f}  "
              f"hybrid {bound * graft_factor:.6f}")
        kap_last = kap
        if bound < best_bound:
            best_bound, best = bound, (t, kap)
    # t -> b limit using the last measured kappa with artanh(r) exactly
    assert kap_last is not None
    limit_bound = kap_last * b ** (1.0 / n) * math.sqrt(math.atanh(r)) / r ** (1.0 / n)
    limit_hybrid = limit_bound * graft_factor
    best_bound = min(best_bound, limit_bound)
    recovery = (sqrt_b_lab - best_bound) / sqrt_b_lab
    print(f"       t->b limit bound {limit_bound:.9f}  hybrid {limit_hybrid:.9f}")
    print(f"       relative recovery over the lab bound: {100 * recovery:.3f}%")
    print(f"       (needed to reach {need:.6f}: "
          f"{100 * (sqrt_b_lab - need) / sqrt_b_lab:.1f}%)")
    kappa_needed = need * r ** (1.0 / n) / (
        b ** (1.0 / n) * math.sqrt(math.atanh(r))
    )
    print(f"       kappa needed {kappa_needed:.6f}  vs measured {kap_last:.6f}")
    hybrid_floor = best_bound * graft_factor
    still_fails = hybrid_floor > 1.05
    return still_fails, kap_last, hybrid_floor


def arm_saturate(kap_falsifier):
    n = 3
    gap = (n - 1.0) ** (1.0 / n)
    print("  SATURATE  kappa * (n-1)^(1/n) at t just below the parent merge")
    sat = kap_falsifier * gap
    print(f"       falsifier cubic: {sat:.6f}")
    rng = np.random.default_rng(20260828)
    extras = []
    while len(extras) < 3:
        z = rng.uniform(-1, 1, 3) + 1j * rng.uniform(-1, 1, 3)
        z = z * (0.9 / max(1.0, np.max(np.abs(z))))
        data = cherry_and_graft(z)
        if data is None:
            continue
        cherry, graft, beta, b, r = data
        if not (b < 1.0 and 0.05 < r < 0.999):
            continue
        pair = [int(i) for i in cherry["root_pair"]]
        t = beta + 0.999 * (b - beta)
        kap = kappa_at(z, t, pair[0], pair)
        if kap is None:
            continue
        extras.append((r, kap * gap))
        print(f"       extra cubic  r {r:.4f}  kappa*(n-1)^(1/n) {kap * gap:.6f}")
    falsifier_saturated = abs(sat - 1.0) < 0.02
    extras_saturated = all(abs(v - 1.0) < 0.02 for _, v in extras)
    return falsifier_saturated and extras_saturated, extras


def arm_control():
    """A cubic with small cherry ratio r: the law still pins kappa at 2^(-1/3)."""
    n = 3
    print("  CONTROL  small-r cubic: parent-cut kappa is pinned at 2^(-1/3)")
    roots = np.array([0.12, -0.12, -0.05 + 0.88j], dtype=complex)
    data = cherry_and_graft(roots)
    assert data is not None
    cherry, graft, beta, b, r = data
    pair = [int(i) for i in cherry["root_pair"]]
    t = beta + 0.999 * (b - beta)
    kap = kappa_at(roots, t, pair[0], pair)
    assert kap is not None
    law = 0.5 ** (1.0 / 3.0)
    print(f"       roots 0.12, -0.12, -0.05+0.88j: r {r:.4f}  b {b:.6f}")
    print(f"       kappa {kap:.6f}  vs last-lobe law 2^(-1/3) = {law:.6f}")
    pinned = abs(kap - law) < 0.02
    return pinned


def main() -> int:
    print("check_erdos1041_parent_aware_capacity_budget")
    ok_replay, state = arm_falsifier()
    still_fails, kap_last, hybrid_floor = arm_kc(state)
    saturated, extras = arm_saturate(kap_last)
    widened = arm_control()
    gates = {
        "falsifier_lab_values_reproduced": ok_replay,
        "exact_capacity_cannot_repay_graft": still_fails,
        "falsifier_kappa_saturates_blaschke_gap": saturated,
        "control_kappa_pinned_by_last_lobe_law": widened,
    }
    print()
    for key, val in gates.items():
        print(f"  {key}={val}")
    print(f"  hybrid_floor_with_optimal_area_input={hybrid_floor:.9f}")
    ok = all(gates.values())
    print(f"\nverdict {'pass' if ok else 'FAIL'}")
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
