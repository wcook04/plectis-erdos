# Erdős 1041 — current frontier (2026-08-29)

Read this before `STRONGEST_RESULTS.json`.  That map is generated from the
2026-08-28 activation lists and therefore still presents as live several rows
that were **refuted on 2026-08-29**.  This file is the dated delta.  The
unrestricted problem is **OPEN**.

Target (unchanged): for monic `f` of degree `n >= 2` with all roots in the
open unit disk, two roots are joined by a rectifiable path of length `< 2`
inside `{|f| < 1}`.

## 1. Refuted — do not rebuild these

Each row has a certified witness in the file named; each was killed by
measurement plus adjudication, not by an absent proof.

| Row | Status | Owner file |
|---|---|---|
| `L(c*) < 2` at the strict-argmin first-merge hub (universal form) | **FALSE**, closed disk, deg 4 (`>= 2.000146`) and deg 5 (`2.0142514`, margin 97x) | `MinimalHubArmBudgetRefutation.md` |
| Every critical-value-slack envelope, incl. `L(c*) <= 2 D^{1/(n(n-1))}` (`D = |disc f|/n^n`) and its geometric-mean/discriminant forms | **FALSE**; the extremality lemma makes this the weakest Hadamard-sufficient member, so the whole family dies with it | same, Result B + addenda |
| Aggregate `Sigma_c L(c) <= 2(n-1) R_MEC` (AGG) | **FALSE** at `n = 4` (open violating region, ratio `1.001059`) and `n = 5` (one certified witness, ratio `1.000338`) | `SeparatrixAggregateReduction.md` addendum |
| `CriticalTreeLengthCharge.md` (A), (E), componentwise (F) | **FALSE** — same deg-4 witness has ALL hubs admissible, so the admissible-set aggregate is exactly the refuted sum | same addendum |
| `AdmissibleCriticalArcProductLab.md` (AQ), (CAQ) | **FALSE** at the same witness (measured `1.001853`) | same addendum |
| Aggregate/sum form of the open producer `critical_point_selection_with_inverse_ray_length_control` | **FALSE**; only its SELECTION form survives | same addendum |
| Origin two-radii connector inside the near-Fekete shell (any `eta`-neighbourhood) | **FALSE** for `n = 3` (proved) and every `n >= 5` (exact rational quintic witness; 4 of 5 spokes escape by rational signs) | `NearFeketeRadialAngularSplit.md` Theorem 7 |

Older no-gos in `research_packet.json::negative_results` remain in force.

## 2. Surviving carriers of the parent theorem

- **Hub selection**, `min_c L(c) < 2` over admissible hubs.  This is now the
  canonical metric row: it survived every 2026-08-29 killer
  (`0.977` at the deg-4 aggregate witness, `0.964` at the deg-5 one,
  `0.973` at the argmin witness).  Wiring, all proved in-corpus:
  `AttachmentAwareReeb.md` Corollary 3a gives
  `Lam(f) <= min_c L(c)` for ray-separated `f`; its Corollary G gives density
  of ray-separated polynomials in `K_n`; `GenericSufficiencyClosure.md`
  Theorem L (lower semicontinuity of `Lam`) and Corollary S then convert
  `min_c L(c) <= 2` on that dense class into the strict open-disk theorem.
  **So proving `min_c L(c) <= 2` on ray-separated `K_n` proves Erdős 1041 in
  degree `n`, with no further bookkeeping.**
- COVER (`one_root_covering_of_the_first_merge_component`), FP–GM free-pair
  selector, fixed-block monodromy average lift, and the capacity-geodesic
  conjecture (C) are unaffected by the 2026-08-29 refutations.

Selection must NOT be by minimal critical value (§1 row 1), and no
surviving envelope may be a function of the critical-value moduli alone
(§1 row 2): the deg-4 witness has all critical values tied to `7.1e-7` while
its arms exceed the radial budget, so those data cannot separate it from
`z^4 - lambda`.

## 3. New proved tools available to a solver

All proved on 2026-08-29 unless stated; see the named file for full proofs.

- **Quantitative Fekete–Hadamard stability** (`NearFeketeRadialAngularSplit.md`
  Theorem 2): `D >= 1 - eta`, `eta <= 1/(80 n^2)` forces
  `1 - rho_i^2 <= n eta/(n-1)`, pairwise separation
  `>= (2 - 2 sqrt(eta) - n eta)/(n-1)`, and a bijection to a rotated regular
  `n`-gon within `7 sqrt(eta)`.  (The object `HardRegimeIsNearFekete.md`
  names as missing.)
- **Radial monotonicity and reduction** (Theorem 3, Corollary 3a): near
  Fekete, radial deficits only help — the entire difficulty is **angular**.
- **Radial slice** (Theorem 4): exact gon directions with arbitrary radii
  give the two-radii path unconditionally for `n <= 6`; general `n` admits
  the radial band `1 - rho <= 2(1 - cos(2 pi/n))`.
- **Spoke expansion / averaging identity** (Theorem 5) and the **centroid
  half-plane law** (Theorem 6) for roots on a circle.
- **Lemma S5** (`Degree5AssemblyAndSharpenedCuts.md`): `|f(c)| <= 1/M_n`
  makes both nearest straight spokes safe; `1/M_5 = 0.2760461` (11x the
  previous deep-low row), `M_3 = 27/25` exact, branch switch at `t_c = 2/n`.
- **Grönwall area identity** at a connected terminal component, with
  `a_1 = -c_{n-2}/(n t^{1/n})` exact — replaces Pólya's area bound there.
- **Fiber derivative product identity**
  `prod_{f(z)=w} f'(z) = n^n prod_k (f(c_k) - w)`, the weighted-mean arm
  form, and the **GM-damped quadratic consumer** `L_arm^2 <= mu^{1/n} J`
  (`MinimalHubArmBudgetRefutation.md` Lemmas 1–2, Proposition 3).
- **Plurisubharmonicity of the arm aggregate** in root coordinates, with the
  extremum pushed to circle / saddle-connection / degenerate strata
  (`SeparatrixAggregateReduction.md` §§PSH, MAX) — machinery that outlived
  its target inequality and applies to any arm functional.

## 4. Open gaps worth attacking (the actual ask)

1. **Conjecture (S)** — `Sigma_{k=1}^{n-1} |f(c_k)|^{1/n} <= (n-1) R`, the
   arithmetic mean of the merge-level capacities bounded by the circumradius.
   Strictly strengthens Schur–Fekete (which gives only the geometric mean),
   tight exactly on `(z-tau)^n - lambda`, **proved for `n = 2, 3`**,
   adversarial sup exactly `1.000000` through `n = 13`, and unrefuted by
   every 2026-08-29 witness.  It is the surviving algebraic half of the
   refuted aggregate (`AGG ratio = S * V`; the violation is entirely in the
   metric factor `V`).  Reduces to a **free-point** inequality: for
   `c_1..c_m` in the closed unit disk,
   `(1/m) Sigma_j (prod_k |1 - conj(c_j) c_k|)^{1/m} <= 1`.  Unused
   ingredient: the rank-2 Lorentzian structure of `N_{jk} = <u_j, u_k>`,
   `u_j = (1, conj(c_j))`.  **(S) does not imply the parent by itself** — it
   is a standalone theorem worth having.
2. **Decide (AGG) at `n = 3`.**  Two independent hunts stall at `0.999386`,
   both on the instrument's `d_pt >= 0.02 R` gate.  A gate-free
   high-precision sweep would settle whether (AGG) is true at `n = 3` and
   false for all `n >= 4`.  Also: widen the `n = 5` witness into an open
   region.
3. **(R1), the near-Fekete containment selector.**  After §3's reductions
   the near-Fekete keystone is exactly: find `eta_n > 0` such that
   `D >= 1 - eta_n` implies there are `i != j` and a hub `c` with
   `|a_i - c| + |a_j - c| <= 2` and `|f| <= 1` on both segments.  The metric
   side is free (length `<= 2` is automatic near the gon), the radial
   direction is discharged, and `c = 0` is refuted — so the whole content is
   choosing `c`.  Measured: the rescuing hub sits at `|c| ~ 0.35-0.4 rho`,
   `rho = max_m |q_m/n|^{1/(n-m)}`.
4. **(SPOKE-5).**  "For every monic quintic with roots in the closed unit
   disk there is a critical point `c` with `|f(c)| <= 1` and two roots
   `a, b` with `|f| <= 1` on `[c,a] u [c,b]` and `|c-a| + |c-b| <= 2`."  By
   `TwoSegmentContainmentReduction.md` + `GenericSufficiencyClosure.md`
   Corollary S this proves Erdős 1041 **at `n = 5`** — the first new full
   degree (3 is proved in-corpus, 4 is Pendyala's).  It is genuinely
   degree-specific: FALSE at degrees 6 and 9.  Adversarial search pins its
   two functionals at `0.9999997708` and `1.9975399`, both under budget,
   maximised at `z^5 - 1`.
5. **Two-root component area bound**: `Area(U) <= A* pi t^{2/5}` with
   `A* < (1/4)^{2/5} = 0.5743490`.  Measured max `0.482` overall and `0.264`
   in the decisive band.  Would shrink the degree-5 residual band ~58x; the
   Grönwall identity (§3) extended to proper components is the natural route.
6. **Instrument law to adopt**: the binding degeneracy for arm measurements
   is a foreign critical **value** near the descending segment `[0, f(c)]`,
   invisible to critical-**point** separation gates.  Use
   `value_gap := min_{i != j} dist(f(c_j), segment[0, f(c_i)]) / |f(c_i)|`.
   An apparent (AGG) violation at `value_gap = 1.2e-16` was adjudicated FAKE;
   the certified witnesses sit at `~1e-9`.
7. **Priority/novelty unchecked** for Theorem 2, the coarea identity
   `Sigma_k |f(c_k)|^{1/n} = int_0^inf (nu(lambda^n) - 1) d lambda`, the
   self-inversive torus identity, and (S).  Assume classical until searched.

## 5. Residual degree map

`n = 3` proved (`CubicCriticalHub.md`).  `n = 4` proved externally
(Pendyala, arXiv:2606.24875; extended locally by `QuarticCoreRadiusCase.md`).
`n = 5` **open**, with the residual localised to rapid nearly-simultaneous
merging near the regular pentagon; generic families are fully covered by the
named theorems, and the uncovered region is `beta_1 > 0.2760`, every merge
ratio above its `Theta_{5,k}`, `D` median `0.986`.  Closed sub-families at all
degrees: collinear, concyclic with radius `<= 2^{-1/n}`, cyclic trinomials
and tetranomials, cyclic quotients, binomials, sparse quintics, quartic-core,
deep-low critical value, separated-level Bergman, and the new exact-gon
radial slice for `n <= 6`.

## 6. Evidence classes used here

Ordinary proved mathematics; exact rational/interval certificates; 50-dps
mpmath certificates with independent-instrument agreement; and adversarial
measurement (never presented as proof).  Each owner file labels its own rows.
Checkers for the 2026-08-29 results:
`scripts/check_erdos1041_minimal_hub_arm_budget_refutation.py`,
`scripts/check_erdos1041_separatrix_aggregate.py`,
`scripts/check_erdos1041_near_fekete_radial_angular_split.py`,
`scripts/check_erdos1041_degree5_sharpened_cuts.py`.
