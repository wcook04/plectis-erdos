#!/usr/bin/env python3
"""Erdos #1041: an exact identity at every critical point, and the length budget it buys.

Why this probe exists
---------------------
Every earlier #1041 measurement in this repo is a GRID measurement of a geodesic,
and the recurring failure mode is that a tight statement tested on a grid reports
a false violation (recorded three times in TrueGeodesicLab.md).  This probe is
grid-free.  Everything it computes is exact arithmetic on roots and critical
points, so the thin-corridor trap cannot fire here at all.

The identity
------------
Let f be monic of degree n with roots z_1..z_n, and let c be a critical point, so
that sum_i 1/(z_i - c) = 0.  Writing w_i = z_i - c and expanding |c + w_i|^2 <= 1:

    |c|^2 + 2 Re(conj(c) w_i) + |w_i|^2 <= 1,   with slack exactly 1 - |z_i|^2.

Divide by |w_i|^2, note Re(conj(c) w_i)/|w_i|^2 = Re(c / w_i), and sum over i.
The critical-point condition kills the cross term (sum_i Re(c/w_i) = 0), leaving

    sum_i (1 - |z_i|^2)/|z_i - c|^2  +  n  =  (1 - |c|^2) sum_i 1/|z_i - c|^2.   (ID)

This is an identity, not an inequality, and it holds at EVERY critical point of
EVERY monic polynomial (no disk hypothesis is used in deriving it -- the disk
hypothesis is what makes the first sum non-negative).

Two immediate consequences when all roots lie in the closed unit disk:

    (STAR)  sum_i 1/|z_i - c|^2  >=  n / (1 - |c|^2),  equality iff every |z_i| = 1.
    (NEAR)  the nearest root to c satisfies  d_min <= sqrt(1 - |c|^2)  <=  1.

EHP's existence theorem, via the discriminant
---------------------------------------------
Separately, the resultant identity for monic f gives

    prod over critical points |f(c_k)|  =  prod_{i<j} |z_i - z_j|^2 / n^n,

and Fekete's theorem says the Vandermonde product over the closed unit disk is at
most n^(n/2).  So the product of critical values is at most 1, with equality iff
the roots are the n-th roots of unity.  Hence some critical value has modulus < 1
when the roots lie in the OPEN disk, hence {|f| < 1} has fewer than n components,
hence some component holds two roots.  That is exactly the theorem of
Erdos-Herzog-Piranian quoted on the problem page, and its equality case is the
same family (z^n - r^n as r -> 1) that the sharpness theorem in TrueGeodesicLab
identifies as extremal for the constant 2.

The budget conjectures under test
---------------------------------
A path from z_a up to a critical point c and back down to z_b has a natural
length target |z_a - c| + |z_b - c|.  Which pair is available at c is not a free
choice: the two roots joinable through c are the two whose sublevel components
MERGE there, found by descending the two curves of constant arg f out of c.

    B1  at EVERY critical point, the two NEAREST roots satisfy d_1 + d_2 <= 2.
    B3  the MINIMUM over critical points c with |f(c)| < 1 of the merge-pair
        budget |z_a - c| + |z_b - c| is at most 2.

B3 is the half of #1041 that says the length is affordable; the other half is
that a path of that length exists inside {|f| < 1}, which this probe reports on
but does not settle.  B1 is cleaner but says nothing about joinability -- the
nearest pair is usually NOT the merge pair.

A refuted intermediate is kept here on purpose.  Selecting the hub by LEAST
CRITICAL VALUE and taking its merge pair gives a quantity that exceeds 2: at
n = 4 with roots near 0.762, i, -0.970+0.115i, -i the least-value hub merges the
two near-antipodal roots for a budget of 2.0068, while a different hub merges the
other pair for 1.7444.  That is not a numerical artifact and not a counterexample
to anything -- it is a badly chosen selector.  The hub is ours to choose, so the
statement has to take the minimum over hubs, not the value at a distinguished
one.

Both are tight, and at two structurally different families:
    z^n - r^n           at c = 0        gives  2r
    (z+r)^(n-1)(z-r)    at c = r(n-2)/n gives  2r
so a maximum of exactly 2 in the closed-disk limit is the expected answer.  The
second family is not incidental: putting n-1 roots at -1 and solving the
critical-point condition for the last root gives z_0 = t + (1+t)/(n-1), and
|z_0| <= 1 forces t <= 1 - 2/n, with equality exactly at (z+1)^(n-1)(z-1).  That
is the configuration a relaxation of B1 identifies as its own extremal case.

What this script checks
-----------------------
  * (ID) to machine precision on random and structured configurations.
  * the discriminant/Fekete identity for the product of critical values.
  * B1 and B3 on structured families and under direct maximisation.
  * how often the B3 budget is actually REALISED, i.e. both segments of the
    broken line through the hub are certified interior.

Segment interiority is CERTIFIED, not sampled: |f|^2 restricted to a segment is
a real polynomial of degree 2n, so its maximum is computed from the roots of the
derivative (see erdos1041_geodesic.segment_max_modulus).

Nothing here is a proof of #1041.  (ID), (STAR), (NEAR) and the discriminant
identity are exact; the budget statements are conjectures that this probe tries
to refute.
"""

from __future__ import annotations

import argparse
import json
import math
from pathlib import Path

import numpy as np

from formal_math.probes.erdos1041_geodesic import segment_max_modulus

RCAP = 1.0 - 1e-12


# ---------------------------------------------------------------- basics


def coeffs(roots: np.ndarray) -> np.ndarray:
    return np.poly(np.asarray(roots, dtype=complex))


def critical_points(roots: np.ndarray) -> np.ndarray:
    co = coeffs(roots)
    der = np.polyder(co)
    if der.size <= 1:
        return np.array([], dtype=complex)
    return np.roots(der)


def clamp_to_disk(roots: np.ndarray, cap: float = RCAP) -> np.ndarray:
    r = np.abs(roots)
    scale = np.where(r > cap, cap / np.maximum(r, 1e-300), 1.0)
    return roots * scale


# ---------------------------------------------------------------- exact identities


def identity_terms(roots: np.ndarray, c: complex) -> dict:
    """Both sides of (ID) at one critical point."""
    d2 = np.abs(roots - c) ** 2
    lhs = float(np.sum((1.0 - np.abs(roots) ** 2) / d2) + len(roots))
    rhs = float((1.0 - abs(c) ** 2) * np.sum(1.0 / d2))
    return {
        "lhs": lhs,
        "rhs": rhs,
        "abs_residual": abs(lhs - rhs),
        "rel_residual": abs(lhs - rhs) / max(1.0, abs(rhs)),
    }


def vandermonde(roots: np.ndarray) -> float:
    n = len(roots)
    out = 1.0
    for i in range(n):
        for j in range(i + 1, n):
            out *= abs(roots[i] - roots[j])
    return out


def fekete_terms(roots: np.ndarray) -> dict:
    """prod |f(c_k)| against |disc| / n^n, and the Fekete bound on the Vandermonde."""
    n = len(roots)
    co = coeffs(roots)
    cps = critical_points(roots)
    prod_cv = float(np.prod(np.abs(np.polyval(co, cps)))) if cps.size else 1.0
    van = vandermonde(roots)
    disc_over_nn = van ** 2 / float(n) ** n
    return {
        "prod_critical_values": float(prod_cv),
        "disc_over_n_to_the_n": float(disc_over_nn),
        "rel_residual": float(abs(prod_cv - disc_over_nn) / max(1e-300, disc_over_nn)),
        "vandermonde": float(van),
        "fekete_max": float(n) ** (n / 2.0),
        "vandermonde_ratio": float(van / float(n) ** (n / 2.0)),
        "min_critical_value": float(np.min(np.abs(np.polyval(co, cps)))) if cps.size else float("nan"),
    }


# ---------------------------------------------------------------- budgets


def budget_at(roots: np.ndarray, c: complex) -> float:
    d = np.sort(np.abs(roots - c))
    return float(d[0] + d[1])


def b1_profile(roots: np.ndarray) -> dict:
    cps = critical_points(roots)
    if cps.size == 0:
        return {"b1_max": float("nan"), "b1_min": float("nan")}
    budgets = [budget_at(roots, c) for c in cps]
    k = int(np.argmax(budgets))
    return {
        "b1_max": float(max(budgets)),
        "b1_min": float(min(budgets)),
        "argmax_critical_point": [float(cps[k].real), float(cps[k].imag)],
        "argmax_modulus": float(abs(cps[k])),
        "d_min_bound_ok": bool(
            all(
                np.min(np.abs(roots - c)) <= math.sqrt(max(0.0, 1.0 - abs(c) ** 2)) + 1e-9
                for c in cps
            )
        ),
    }


# ------------------------------------------------- which two roots merge at c


def descend_branches(co: np.ndarray, c: complex, ratio: float = 0.8,
                     floor: float = 1e-10) -> list[complex] | None:
    """DO NOT TRUST THIS FOR BRANCH IDENTITY.  It mistracks.

    It names the wrong root often enough to have produced three retracted
    "counterexamples" in this problem's lab: the n=4 budget 2.0068 and the n=3/4/7
    merge-pair budgets 2.132 / 2.116 / 2.014, all void.  A residual-gated
    continuation at 20000 steps, the inverse-ray lab's own scorer, and a concurrent
    session's regression check all disagree with it and agree with each other.  The
    geometric step ladder here is too coarse near a neighbouring critical point,
    where the constant-arg branch passes close to another saddle and it hops.

    For anything that depends on WHICH root a branch reaches, use
    inverse_ray_aggregate_score from
    ErdosProblems/Erdos1041/scripts/search_counterexample.py, which gates every
    branch on endpoint error and value-ray residual; see
    formal_math/probes/erdos1041_descent_length.py for that route.

    Kept rather than deleted because components_below_one still calls it, and its
    union-find consistency check is what makes the mistracking visible at all.

    Follow the two curves of constant arg f descending from a simple critical
    point c.  Returns None at a degenerate critical point or if the continuation
    fails to track.

    Both branches are advanced together as a length-2 array, and the multiplier
    on |f| is halved toward 1 whenever a Newton solve does not converge, so the
    step adapts instead of silently jumping between branches.
    """
    w0 = complex(np.polyval(co, c))
    if w0 == 0:
        return None
    d2 = complex(np.polyval(np.polyder(co, 2), c))
    if abs(d2) < 1e-11 * max(1.0, abs(w0)):
        return None  # degenerate critical point: more than two branches

    der = np.polyder(co)
    s0 = 1e-4
    off = np.sqrt(-2.0 * s0 * w0 / d2)
    z = np.array([c + off, c - off], dtype=complex)
    t = 1.0 - s0

    def newton(zz: np.ndarray, target: complex) -> tuple[np.ndarray, float]:
        zz = zz.copy()
        step = np.inf
        for _ in range(40):
            fp = np.polyval(der, zz)
            fp = np.where(np.abs(fp) < 1e-300, 1e-300 + 0j, fp)
            d = (np.polyval(co, zz) - target) / fp
            zz = zz - d
            step = float(np.max(np.abs(d)))
            if step < 1e-13:
                break
        return zz, step

    guard = 0
    while t > floor:
        q = ratio
        for _ in range(8):
            nt = max(t * q, 0.0)
            zz, step = newton(z, w0 * nt)
            if step < 1e-10:
                z, t = zz, nt
                break
            q = math.sqrt(q)  # smaller descent per step
        else:
            return None
        guard += 1
        if guard > 4000:
            return None

    zz, step = newton(z, 0.0 + 0j)
    if step < 1e-8:
        z = zz
    return [complex(z[0]), complex(z[1])]


def merge_pair(roots: np.ndarray, c: complex) -> dict | None:
    co = coeffs(roots)
    ends = descend_branches(co, c)
    if ends is None:
        return None
    idx = []
    for e in ends:
        dists = np.abs(roots - e)
        j = int(np.argmin(dists))
        if dists[j] > 1e-4:
            return None  # descent did not land on a root
        idx.append(j)
    if idx[0] == idx[1]:
        return None  # both branches hit the same root: not a clean merge
    a, b = roots[idx[0]], roots[idx[1]]
    return {
        "root_a": [float(a.real), float(a.imag)],
        "root_b": [float(b.real), float(b.imag)],
        "budget": float(abs(a - c) + abs(b - c)),
        "chord": float(abs(a - b)),
    }


def components_below_one(roots: np.ndarray) -> dict:
    """The components of {|f| < 1}, as a partition of the roots, plus the hub tree.

    The number of components of {|f| < t} is n minus the number of critical points
    with |f(c)| < t, so if EVERY critical value is below 1 the set is connected and
    every pair of roots is joinable.  That case needs no descent at all.

    Otherwise the tree is built by processing the hubs below level 1 in increasing
    critical value and unioning the two components their descent branches reach.  A
    merge must join two DISTINCT components, so a hub whose two branches land in
    the same class is a mistracked descent, not a merge: it is reported unresolved
    and left un-unioned rather than folded in.
    """
    n = len(roots)
    co = coeffs(roots)
    cps = critical_points(roots)
    vals = np.abs(np.polyval(co, cps)) if cps.size else np.array([])
    below = [(float(v), complex(c)) for v, c in zip(vals, cps) if v < 1.0]

    parent = list(range(n))

    def find(i):
        while parent[i] != i:
            parent[i] = parent[parent[i]]
            i = parent[i]
        return i

    if cps.size and bool(np.all(vals < 1.0)):
        # every critical value below 1 => one component, no descent needed
        return {"connected": True, "labels": [0] * n, "hubs": [(v, c, 0) for v, c in below],
                "unresolved_hubs": 0}

    unresolved = 0
    hubs = []
    for v, c in sorted(below, key=lambda t: t[0]):
        ends = descend_branches(co, c)
        if ends is None:
            unresolved += 1
            hubs.append((v, c, None))
            continue
        idx = []
        for e in ends:
            d = np.abs(roots - e)
            j = int(np.argmin(d))
            idx.append(j if d[j] <= 1e-4 else -1)
        if -1 in idx or find(idx[0]) == find(idx[1]):
            unresolved += 1
            hubs.append((v, c, None))
            continue
        ra, rb = find(idx[0]), find(idx[1])
        hubs.append((v, c, ra))
        parent[rb] = ra

    labels = [find(i) for i in range(n)]
    return {"connected": len(set(labels)) == 1, "labels": labels,
            "hubs": [(v, c, (find(r) if r is not None else None)) for v, c, r in hubs],
            "unresolved_hubs": unresolved}


def hub_rows(roots: np.ndarray) -> dict:
    """The hub budget, with the pair chosen correctly.

    WARNING: the DISCONNECTED case depends on descend_branches for the merge tree,
    and that routine mistracks branch identity -- see its docstring.  Numbers from
    that path are not reliable.  The connected case (every critical value below 1)
    needs no descent at all and is sound.

    A path through a hub c can join ANY two distinct roots of the component of
    {|f| < 1} that contains c -- not only the two roots whose sublevel components
    merge at c.  When that component holds several roots the merge pair is an
    arbitrary restriction, and since the conjecture bounds a MINIMUM from above,
    restricting the pair biases the statistic upward: the direction that fakes a
    refutation.  That is a real hazard, but note it was never actually WITNESSED:
    the configurations once offered as evidence for it came from the mistracking
    descent above, and on retracing, the merge-pair and component readings there
    are identical.

    So the budget at c is the sum of the two smallest distances from c to roots in
    c's own component, and B3' is the minimum of that over hubs with |f(c)| < 1.
    When {|f| < 1} is connected this is exactly B1's quantity at the best hub.
    """
    info = components_below_one(roots)
    labels = info["labels"]
    rows = []
    for v, c, root_label in info["hubs"]:
        if info["connected"]:
            members = np.arange(len(roots))
        elif root_label is None:
            continue
        else:
            members = np.array([i for i in range(len(roots)) if labels[i] == root_label])
        if members.size < 2:
            continue
        d = np.sort(np.abs(roots[members] - c))
        rows.append({
            "critical_point": [float(c.real), float(c.imag)],
            "critical_modulus": float(abs(c)),
            "critical_value": float(v),
            "component_size": int(members.size),
            "budget": float(d[0] + d[1]),
        })
    if not rows:
        return {"b3_prime": float("nan"), "rows": [],
                "connected": info["connected"],
                "unresolved_hubs": info["unresolved_hubs"],
                "status": "no_usable_hub"}
    return {
        "b3_prime": float(min(r["budget"] for r in rows)),
        "connected": info["connected"],
        "usable_hubs": len(rows),
        "unresolved_hubs": info["unresolved_hubs"],
        "rows": rows,
        "status": "ok",
    }


# ------------------------------------------------- the two-segment construction


TWO_SEGMENT_ABSENT = 10.0   # sentinel score when no admissible construction exists


def mechanism_hubs(roots: np.ndarray) -> tuple[np.ndarray, dict]:
    """The critical points usable as hubs, with multiple ones collapsed.

    np.roots cannot resolve a multiple root: an m-fold zero of f' comes back as m
    points spread by about eps^(1/m), which is 0.017 at m = 9, not 1e-16.  For
    z^n - r^n the true critical set is {0} with multiplicity n-1, and the solver
    returns n-1 points on a circle of radius 0.017 around it.

    Those spurious points are NOT admissible hubs for this mechanism, whose claim
    is "through a critical point", and admitting them biases in the hiding
    direction: an extra hub can only LOWER the cheapest connection, so a
    configuration whose genuine constructions all cost 2 or more could be reported
    as satisfied.  (For polyline_upper_bound in erdos1041_geodesic.py the same
    extra hubs are harmless and in fact sound, because there the claim is only that
    some interior path exists, and a certified broken line through any point is a
    genuine path.  The distinction is the claim, not the arithmetic.)

    A multiple critical point is detected by f'' vanishing there, which is
    well-conditioned even where the location is not; the cluster is then replaced
    by its centroid, which estimates a multiple root to full precision because the
    elementary symmetric sum is well-conditioned.
    """
    cps = critical_points(roots)
    if cps.size == 0:
        return cps, {"degenerate_clusters": 0, "collapsed": 0}
    d2 = np.polyder(coeffs(roots), 2)
    scale = float(np.sum(np.abs(d2))) if d2.size else 1.0
    resid = np.abs(np.polyval(d2, cps)) / max(scale, 1e-300) if d2.size else np.zeros(cps.size)

    # erring toward collapsing is the safe direction here: merging two genuinely
    # distinct hubs REMOVES a candidate, which raises the reported minimum, while
    # keeping a spurious one lowers it and can hide a failure.
    simple = [c for c, r in zip(cps, resid) if r >= 1e-6]
    degen = [c for c, r in zip(cps, resid) if r < 1e-6]

    centroids, used = [], [False] * len(degen)
    for i, c in enumerate(degen):
        if used[i]:
            continue
        group = [c]
        used[i] = True
        for j in range(i + 1, len(degen)):
            if not used[j] and abs(degen[j] - c) < 0.25:
                group.append(degen[j])
                used[j] = True
        centroids.append(sum(group) / len(group))

    radius = 0.0
    for cen in centroids:
        for c in degen:
            if abs(c - cen) < 0.25:
                radius = max(radius, float(abs(c - cen)))

    hubs = np.array(simple + centroids, dtype=complex) if (simple or centroids) else np.array([], dtype=complex)
    return hubs, {"degenerate_clusters": len(centroids), "collapsed": len(degen),
                  "max_cluster_radius": radius}


def two_segment_profile(roots: np.ndarray, full: bool = False) -> dict:
    """The cheapest CERTIFIED two-segment connection between two roots.

    AllStraightSegmentsCounterexampleComputationalLab.md kills the direct chord
    (every chord of z^3 - r^3 with r^3 > 8/9 leaves the lemniscate at its midpoint)
    and in the same breath opens the replacement: on that cubic the broken line
    r -> 0 -> r*omega has length 2r < 2 and stays inside.  It closes by asking for
    "the existence and metric budget of such hubs".  The budget half is the theorem
    in CriticalBudgetLab.md.  This measures the existence half.

    Candidates are the mechanism exactly as proposed: the direct chord, and the
    broken line through the origin or through a critical point, over all root
    pairs.  A segment is admitted only when the exact maximum of |f| along it is
    below 1, so a reported length is a genuine upper bound on the geodesic.

    Since the answer is the MINIMUM admissible length, candidates are sorted by
    length and the first that certifies wins: that is exact, and it skips the
    expensive check on everything longer.  Pass full=True for the per-mechanism
    breakdown, which has to check them all.

    A configuration with no admissible construction refutes the mechanism outright,
    which is stronger than one with an expensive construction, so the two outcomes
    are reported separately rather than merged into one number.
    """
    n = len(roots)
    crit, hub_info = mechanism_hubs(roots)
    hubs = [("origin", 0j)] + [("critical", complex(c)) for c in crit]

    cands = []
    for i in range(n):
        for j in range(i + 1, n):
            a, b = complex(roots[i]), complex(roots[j])
            cands.append((float(abs(a - b)), "chord", a, b, None))
            for name, h in hubs:
                cands.append((float(abs(a - h) + abs(h - b)), name, a, b, h))
    cands.sort(key=lambda t: t[0])

    def admissible(a, b, h):
        if h is None:
            return segment_max_modulus(roots, a, b) < 1.0
        return (segment_max_modulus(roots, a, h) < 1.0
                and segment_max_modulus(roots, h, b) < 1.0)

    best, best_via, by_mech = None, None, {}
    for L, name, a, b, h in cands:
        if best is not None and not full:
            break
        if name in by_mech:
            continue  # candidates are sorted, so this mechanism's minimum is fixed
        if admissible(a, b, h):
            by_mech[name] = L
            if best is None:
                best, best_via = L, name

    return {
        "best": best,
        "best_via": best_via,
        "best_by_mechanism": by_mech if full else None,
        "exists": best is not None,
        "score": TWO_SEGMENT_ABSENT if best is None else float(best),
        "hub_info": hub_info,
    }


# ---------------------------------------------------------------- families


def family_roots(name: str, n: int, r: float) -> np.ndarray:
    if name == "sym":  # z^n - r^n
        return r * np.exp(2j * np.pi * np.arange(n) / n)
    if name == "spike":  # (z+r)^(n-1) (z-r), split so the roots stay simple
        eps = 1e-7
        cluster = -r + eps * np.exp(2j * np.pi * np.arange(n - 1) / max(1, n - 1))
        return np.concatenate([cluster, np.array([r + 0j])])
    if name == "cassini":
        return np.array([r + 0j, -r + 0j])
    raise ValueError(name)


# ------------------------------------------------- case split and the theorem


def case_of(roots: np.ndarray, c: complex) -> str:
    """Which case of the B1 proof this critical point falls in.

    With c != 0, write z_i = c + d_i exp(i phi_i) with phi_i measured from the
    direction of c.  Then |z_i| <= 1 reads d_i^2 + 2|c| d_i cos(phi_i) <= 1-|c|^2,
    so a root with cos(phi_i) >= 0 has d_i <= m := sqrt(1-|c|^2); and the
    critical-point condition gives sum_i cos(phi_i)/d_i = 0.

      two_or_more_on_c_side  two roots with cos(phi) >= 0, so d_1+d_2 <= 2m <= 2.
      none_on_c_side         impossible with a strict sign, and if all cos are 0
                             every d_i <= m, so again d_1+d_2 <= 2m <= 2.
      exactly_one_on_c_side  the only case the elementary argument leaves open,
                             and the only one where equality is ever observed.
    """
    if abs(c) < 1e-12:
        return "c_at_origin"
    u = c / abs(c)
    cosphi = np.real((roots - c) * np.conjugate(u)) / np.abs(roots - c)
    k = int(np.sum(cosphi > 1e-12))
    return {0: "none_on_c_side", 1: "exactly_one_on_c_side"}.get(k, "two_or_more_on_c_side")


def theorem_covers(n: int, c: complex) -> bool:
    """|c| <= 1 - 2/n: the region where B1 is PROVED, not merely measured.

    Suppose d_1 + d_2 > 2.  The case split above forces exactly one root on the
    c-side, at distance delta <= m, and forces the nearest other root to sit at
    e > 2 - delta while e <= 1 + |c|, so delta > 1 - |c|.  Writing S for the
    weighted sum over the far roots, sum_i cos(phi_i)/d_i = 0 gives cos(phi_1) =
    delta*S, and |z_1| <= 1 then gives delta^2 (1 + 2|c| S) <= m^2, while the far
    roots give 2|c| S >= (n-1)(1 - m^2/(2-delta)^2).  Together

        psi(delta) := n delta^2 - (n-1) m^2 delta^2 / (2-delta)^2  <=  m^2.

    psi rises then falls on (0, m], so its minimum over (1-|c|, m] is at an
    endpoint.  psi(m) > m^2 whenever |c| > 0, and psi(1-|c|) >= m^2 exactly when
    |c| <= 1 - 2/n.  So the assumption is contradicted throughout that region.

    The threshold is not an artifact of the estimate: (z+1)^(n-1)(z-1) has its
    non-root critical point at exactly 1 - 2/n and attains d_1 + d_2 = 2 there.
    """
    return abs(c) <= 1.0 - 2.0 / n + 1e-12


def stress(max_n: int, trials: int, steps: int, rng: np.random.Generator,
           cap: float = 1.0) -> dict:
    """Maximise B1 directly, and report it split by case and by proof coverage."""
    per_degree, case_max, envelope = [], {}, {}
    covered_max, open_max = -math.inf, -math.inf
    gauss_lucas_overshoot = 0.0
    worst = (-math.inf, None, None)

    def b1_rows(roots):
        out = []
        for c in critical_points(roots):
            d = np.sort(np.abs(roots - c))
            out.append((float(d[0] + d[1]), complex(c)))
        return out

    for n in range(2, max_n + 1):
        best = -math.inf
        for trial in range(trials):
            if trial == 0:
                roots = family_roots("sym", n, cap)
            elif trial == 1:
                roots = family_roots("spike", n, cap)
            else:
                roots = cap * rng.uniform(0.25, 1.0, n) * np.exp(2j * np.pi * rng.uniform(0, 1, n))
            roots = clamp_to_disk(roots, cap)
            val = max((v for v, _ in b1_rows(roots)), default=-math.inf)
            scale = 0.4
            for _ in range(steps):
                cand = clamp_to_disk(roots + scale * (rng.normal(size=n) + 1j * rng.normal(size=n)), cap)
                cval = max((v for v, _ in b1_rows(cand)), default=-math.inf)
                if cval > val:
                    roots, val = cand, cval
                else:
                    scale *= 0.95
                if scale < 1e-6:
                    break
            best = max(best, val)
            for v, c in b1_rows(roots):
                case_max[case_of(roots, c)] = max(case_max.get(case_of(roots, c), -math.inf), v)
                envelope[round(abs(c), 1)] = max(envelope.get(round(abs(c), 1), -math.inf), v)
                gauss_lucas_overshoot = max(gauss_lucas_overshoot, abs(c) - 1.0)
                if theorem_covers(n, c):
                    covered_max = max(covered_max, v)
                else:
                    open_max = max(open_max, v)
                if v > worst[0]:
                    worst = (v, n, [[float(z.real), float(z.imag)] for z in roots])
        per_degree.append({"n": n, "max_b1": float(best)})

    return {
        "per_degree": per_degree,
        "by_case": {k: float(v) for k, v in sorted(case_max.items())},
        "envelope_by_critical_modulus": {f"{k:.1f}": float(v) for k, v in sorted(envelope.items())},
        "max_where_theorem_applies": float(covered_max),
        "max_where_theorem_is_silent": float(open_max),
        "gauss_lucas_overshoot": float(gauss_lucas_overshoot),
        "global_max": float(worst[0]),
        "global_max_degree": worst[1],
        "global_max_roots": worst[2],
        "violation": bool(worst[0] > 2.0 + 1e-9),
    }


# ---------------------------------------------------------------- search


def objective(roots: np.ndarray, mode: str) -> float:
    if mode == "b1_max":
        return b1_profile(roots)["b1_max"]
    if mode == "b1_min":
        return b1_profile(roots)["b1_min"]
    if mode == "two_segment":
        return two_segment_profile(roots)["score"]
    if mode in ("b3", "b3_prime"):
        v = hub_rows(roots).get("b3_prime", float("nan"))
        return float("-inf") if (v is None or math.isnan(v)) else float(v)
    raise ValueError(mode)


def search(n: int, mode: str, restarts: int, steps: int, rng: np.random.Generator,
           cap: float) -> dict:
    best_val, best_roots = -math.inf, None
    seeds = [family_roots("sym", n, cap)]
    if n >= 2:
        seeds.append(family_roots("spike", n, cap))
    for t in range(restarts):
        if t < len(seeds):
            roots = seeds[t].astype(complex)
        else:
            ang = rng.uniform(0, 2 * np.pi, n)
            rad = cap * rng.uniform(0.3, 1.0, n)
            roots = rad * np.exp(1j * ang)
        roots = clamp_to_disk(roots, cap)
        val = objective(roots, mode)
        scale = 0.35
        for _ in range(steps):
            cand = roots + scale * (rng.normal(size=n) + 1j * rng.normal(size=n))
            cand = clamp_to_disk(cand, cap)
            cval = objective(cand, mode)
            if cval > val:
                roots, val = cand, cval
            else:
                scale *= 0.94
            if scale < 1e-5:
                break
        if val > best_val:
            best_val, best_roots = val, roots
    return {
        "n": n,
        "mode": mode,
        "best": float(best_val),
        "roots": [[float(z.real), float(z.imag)] for z in best_roots],
        "root_moduli": [float(abs(z)) for z in best_roots],
        "min_chord": float(min(abs(best_roots[i] - best_roots[j])
                               for i in range(n) for j in range(i + 1, n))),
    }


# ---------------------------------------------------------------- main


def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--max-n", type=int, default=9)
    ap.add_argument("--restarts", type=int, default=14)
    ap.add_argument("--steps", type=int, default=260)
    ap.add_argument("--cap", type=float, default=1.0 - 1e-9)
    ap.add_argument("--seed", type=int, default=20260823)
    ap.add_argument("--modes", type=str, default="b1_max",
                    help="b1_max is cheap; b3 runs a constant-arg descent per hub per "
                         "objective call, so keep --max-n and --steps small for it")
    ap.add_argument("--stress-trials", type=int, default=0,
                    help="if > 0, also run the direct B1 maximisation with this many restarts")
    ap.add_argument("--stress-steps", type=int, default=320)
    ap.add_argument("--stress-max-n", type=int, default=14)
    ap.add_argument("--out", type=Path, default=None)
    args = ap.parse_args()

    rng = np.random.default_rng(args.seed)
    report: dict = {"identity": [], "fekete": [], "families": [], "search": []}

    # ---- (ID) and the discriminant identity on random configurations
    worst_id, worst_fek = 0.0, 0.0
    for n in range(2, args.max_n + 1):
        for _ in range(60):
            roots = clamp_to_disk(
                rng.uniform(0.05, 1.0, n) * np.exp(2j * np.pi * rng.uniform(0, 1, n)),
                args.cap,
            )
            for c in critical_points(roots):
                worst_id = max(worst_id, float(identity_terms(roots, c)["rel_residual"]))
            worst_fek = max(worst_fek, float(fekete_terms(roots)["rel_residual"]))
    report["identity"] = {"worst_rel_residual": float(worst_id), "configs_per_degree": 60}
    report["fekete"] = {"worst_rel_residual": float(worst_fek)}

    # ---- structured families
    for name in ("sym", "spike"):
        for n in range(2, args.max_n + 1):
            for r in (0.9, 0.999, 1.0 - 1e-9):
                roots = family_roots(name, n, r)
                prof = b1_profile(roots)
                fek = fekete_terms(roots)
                row = {
                    "family": name,
                    "n": n,
                    "r": r,
                    "b1_max": prof["b1_max"],
                    "b1_min": prof["b1_min"],
                    "d_min_bound_ok": prof["d_min_bound_ok"],
                    "vandermonde_ratio": fek["vandermonde_ratio"],
                    "min_critical_value": fek["min_critical_value"],
                }
                hub = hub_rows(roots)
                row["b3_prime"] = hub.get("b3_prime")
                row["connected"] = hub.get("connected")
                row["usable_hubs"] = hub.get("usable_hubs")
                row["unresolved_hubs"] = hub.get("unresolved_hubs")
                row["b3_status"] = hub.get("status")
                report["families"].append(row)

    # ---- maximisation
    for mode in args.modes.split(","):
        for n in range(2, args.max_n + 1):
            report["search"].append(
                search(n, mode.strip(), args.restarts, args.steps, rng, args.cap)
            )

    # ---- direct B1 maximisation with the case split
    if args.stress_trials > 0:
        report["stress"] = stress(args.stress_max_n, args.stress_trials,
                                  args.stress_steps, rng, cap=1.0)

    # ---- verdict
    viol = [r for r in report["families"]
            if (r["b1_max"] is not None and r["b1_max"] > 2.0 + 1e-9)]
    sviol = [r for r in report["search"] if r["best"] > 2.0 + 1e-9]
    report["verdict"] = {
        "identity_exact": bool(worst_id < 1e-9),
        "fekete_identity_exact": bool(worst_fek < 1e-7),
        "family_budget_violations": len(viol),
        "search_budget_violations": len(sviol),
        "max_budget_seen": float(max([r["best"] for r in report["search"]] +
                                     [r["b1_max"] for r in report["families"]])),
    }

    print(json.dumps(report, indent=2))
    if args.out:
        args.out.parent.mkdir(parents=True, exist_ok=True)
        args.out.write_text(json.dumps(report, indent=2) + "\n")


if __name__ == "__main__":
    main()
