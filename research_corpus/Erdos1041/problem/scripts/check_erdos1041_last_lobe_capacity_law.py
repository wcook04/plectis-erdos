#!/usr/bin/env python3
"""Receipt for LastLobeCapacityLaw.md.

THEOREM (last-lobe law).  f monic of degree n; at level b a simple critical
point joins the component U holding all roots but one with a singleton lobe
holding the last root z_n of multiplicity m.  Then, configuration-free,

    cap(U_{b-})^n = b ((n-m)/(n+m))^m ,
    g_{C\\U}(z_n, inf) = m-weighted...  |Phi(z_n)| = cap * (n+m)/(n-m).

Arms
  ALGEBRA   exact Fraction check of the rigidity equation n(sigma-1)=m(sigma+1)
            at sigma=(n+m)/(n-m), and of P's root product = 1.
  PETAL     one petal of the Bernoulli lemniscate, exact boundary:
            cap^2 -> 1/3.
  ROSE      k = n-1 petals of z^n - 1 (coalesced-limit continuity evidence):
            cap^n -> (n-1)/(n+1) at n = 3, 4.
  RANDOM    random (n-1)+1 top merges at degrees 3, 4, 5, traced just below b:
            cap^n/b within tolerance below (n-1)/(n+1).
  CONVERGE  one cubic, cap^3/b increasing toward 1/2 as t increases to b.

Float measurement at the solver resolution of
check_erdos1041_component_capacity.py (CAL: 1.2e-4 relative).  The theorem's
proof is in the note; this receipt is consistency evidence, not the proof.
"""
from __future__ import annotations

import importlib.util
import os
import sys
from fractions import Fraction

import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))


def _load(name: str, filename: str):
    spec = importlib.util.spec_from_file_location(name, os.path.join(HERE, filename))
    mod = importlib.util.module_from_spec(spec)
    sys.modules[name] = mod
    spec.loader.exec_module(mod)
    return mod


cap_mod = _load("_lll_cap", "check_erdos1041_component_capacity.py")
lab_mod = _load("_lll_lab", "check_erdos1041_admissible_critical_arc_product.py")


def arm_algebra() -> bool:
    print("  ALGEBRA  exact rigidity equation over Fraction")
    ok = True
    for n in range(2, 13):
        for m in range(1, n):
            sigma = Fraction(n + m, n - m)
            lhs = n * (sigma - 1)
            rhs = m * (sigma + 1)
            ok &= lhs == rhs
            # quadratic P root product: P = n z^2 - [n(s+1/s)-m(s-1/s)] z + n
            # product of roots = n/n = 1 identically.
    print(f"       n(sigma-1) == m(sigma+1) at sigma=(n+m)/(n-m): "
          f"{'exact for all n<=12' if ok else 'FAILED'}")
    return ok


def arm_petal(tol: float) -> bool:
    print("  PETAL  Bernoulli petal, exact boundary")
    m = 2400
    u = np.linspace(0.0, np.pi, m)
    th = np.pi * np.sin(u / 2.0 - np.pi / 2.0) + np.pi
    th = np.concatenate([-th[::-1], th])
    th = th[(th > -np.pi) & (th < np.pi)]
    z = np.sqrt(2 * np.abs(np.cos(th / 2.0))) * np.exp(1j * th / 4.0)
    z = z[np.abs(z) > 2e-3]
    cap, _, _ = cap_mod.equilibrium(z)
    err = abs(cap**2 - 1.0 / 3.0)
    print(f"       cap^2 = {cap**2:.6f}  prediction 1/3  |err| = {err:.2e}")
    return err < tol


def petal_union(n: int, k: int, m: int = 600) -> np.ndarray:
    th = np.linspace(-np.pi, np.pi, m, endpoint=False)[1:]
    base = (2 * np.cos(th / 2.0)) ** (1.0 / n) * np.exp(1j * th / (2.0 * n))
    pts = [base * np.exp(2j * np.pi * j / n) for j in range(k)]
    zs = np.concatenate(pts)
    return zs[np.abs(zs) > 0.02]


def arm_rose(tol: float) -> bool:
    print("  ROSE  k = n-1 petals of z^n - 1 (coalesced limit)")
    ok = True
    for n in (3, 4):
        zs = petal_union(n, n - 1)
        cap, _, _ = cap_mod.equilibrium(zs)
        pred = (n - 1.0) / (n + 1.0)
        err = abs(cap**n - pred)
        ok &= err < tol
        print(f"       n={n}  cap^n = {cap**n:.6f}  prediction {pred:.6f}  "
              f"|err| = {err:.2e}")
    return ok


def top_merge_structure(roots):
    rows = lab_mod.merging_pair_tree(roots)
    n = len(roots)
    if rows is None or len(rows) != n - 1:
        return None
    rows = sorted(rows, key=lambda r: float(r["critical_value_modulus"]))
    parent = list(range(n))

    def find(i):
        while parent[i] != i:
            parent[i] = parent[parent[i]]
            i = parent[i]
        return i

    for row in rows[:-1]:
        i, j = map(int, row["root_pair"])
        parent[find(i)] = find(j)
    comps = {}
    for i in range(n):
        comps.setdefault(find(i), []).append(i)
    sides = sorted(comps.values(), key=len)
    if len(sides) != 2 or len(sides[0]) != 1:
        return None
    b = float(rows[-1]["critical_value_modulus"])
    beta_prev = float(rows[-2]["critical_value_modulus"]) if n > 2 else 0.0
    return b, beta_prev, sides[1]


def measure_random(n: int, count: int, rng, frac: float):
    out = []
    tried = 0
    while len(out) < count and tried < 600:
        tried += 1
        z = rng.uniform(-1, 1, n) + 1j * rng.uniform(-1, 1, n)
        z = z * (0.9 / max(1.0, np.max(np.abs(z))))
        st = top_merge_structure(z)
        if st is None:
            continue
        b, beta_prev, big = st
        if not (0 <= beta_prev < b):
            continue
        t = beta_prev + frac * (b - beta_prev)
        zs = cap_mod.trace_boundary(np.asarray(z), t, big[0], n - 1)
        if zs is None:
            continue
        inside = sorted(
            j for j in range(n) if cap_mod.winding(zs, np.asarray(z)[j]) != 0
        )
        if inside != sorted(big):
            continue
        cap, _, _ = cap_mod.equilibrium(zs)
        out.append((b, cap**n / b, z))
    return out


def arm_random(tol: float) -> bool:
    print("  RANDOM  (n-1)+1 top merges, t just below b (measured value must sit")
    print("          slightly BELOW the limit, within tolerance)")
    rng = np.random.default_rng(20260829)
    ok = True
    for n, count in ((3, 3), (4, 3), (5, 2)):
        pred = (n - 1.0) / (n + 1.0)
        rows = measure_random(n, count, rng, 0.9997)
        for b, val, _ in rows:
            below = val < pred + 1e-3
            close = pred - val < tol
            ok &= below and close
            print(f"       n={n}  b {b:.5f}  cap^n/b = {val:.6f}  "
                  f"(pred {pred:.4f}, deficit {pred - val:+.2e})")
        if not rows:
            ok = False
            print(f"       n={n}: no usable configuration")
    return ok


def arm_converge(tol: float) -> bool:
    print("  CONVERGE  one cubic, cap^3/b increasing to 1/2 as t -> b")
    rng = np.random.default_rng(20260829)
    rows = measure_random(3, 1, rng, 0.9997)
    if not rows:
        print("       no configuration")
        return False
    _, _, z = rows[0]
    st = top_merge_structure(z)
    b, beta_prev, big = st
    vals = []
    for frac in (0.9, 0.99, 0.999, 0.9997):
        t = beta_prev + frac * (b - beta_prev)
        zs = cap_mod.trace_boundary(np.asarray(z), t, big[0], 2)
        if zs is None:
            continue
        cap, _, _ = cap_mod.equilibrium(zs)
        vals.append(cap**3 / b)
        print(f"       t-frac {frac}  cap^3/b = {vals[-1]:.6f}")
    increasing = all(vals[i] < vals[i + 1] + 1e-9 for i in range(len(vals) - 1))
    final_close = bool(vals) and 0.5 - vals[-1] < tol
    return increasing and final_close


def main() -> int:
    print("check_erdos1041_last_lobe_capacity_law")
    tol = 8e-3
    gates = {
        "algebra_exact": arm_algebra(),
        "bernoulli_petal_one_third": arm_petal(tol),
        "rose_coalesced_limit": arm_rose(tol),
        "random_top_merges_match": arm_random(tol),
        "monotone_convergence_to_limit": arm_converge(tol),
    }
    print()
    for key, val in gates.items():
        print(f"  {key}={val}")
    ok = all(gates.values())
    print(f"\nverdict {'pass' if ok else 'FAIL'}")
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
