# Erdős 1041 — current frontier (2026-08-30, updated by the proof wave of that date)

Read this before `STRONGEST_RESULTS.json`.  That map is generated from the
2026-08-28 activation lists and therefore still presents as live several rows
that were **refuted on 2026-08-29**.  This file is the dated delta.  The
unrestricted problem is **OPEN**.

2026-08-30 PROOF WAVE (nine-agent verification fleet + main loop; six new
owner notes, six new checkers, all green):
- **(EX) base stratum PROVED at every degree**: the one-face radial
  scattering theorem (`OneFaceRadialScatteringTheorem.md`) — strict
  negative excess `<= 2|c*|(pi/n - 1)` at the trace-nonneg critical hub
  on every one-mode model, `n >= 4`, plus the `n = 3` case with constant
  `sqrt 3 - 2`; this is (MLS-strict) at `|M| = 1` with explicit constants.
- **Tangent certificate (ii) is now EXACT** (`QuinticTangentOrbitExactCertificate.md`):
  Sturm-certified containment, closed-form budget, stability floors
  `m_- = 0.4847` / `m_+ = 1` — the "one box" of the §7 recipe, with the
  gauge sign-slip in `QuinticStarKernelMechanics.md` §6 repaired.
- **(EX) measured GLOBALLY TRUE on the quintic core with uniform margin**
  (`TraceMaxRadialExcessLaw.md`): `sup(e_i + e_j) = -0.0362736374` for the
  rightward Main-Theorem arms, extremal EXACTLY at certificate (ii); the
  coercivity invariant is `|c*|` (corr `-0.99`), NOT `Delta_5`; the OUTWARD
  RADIAL carrier fails in an open pocket at the orbit (do not re-propose).
- **The explicit two-root area constant is DONE**
  (`ProperComponentExplicitAreaConstant.md`): `A_{5,2} <= 4^{-2/5}(1 - 6.76e-8)`
  by an exact-rational certificate; `Theta_{5,2} >= 0.940354223795` (+1.36e-8).
- **The AGG3 radial constant is DERIVED and uniformly positive in every
  phase** (`AggregateN3InnerModelClosedForm.md`,
  `AggregateN3PshUniformityClosure.md`): the psh tangent cone proves
  `D+9D''<=0` and the explicit barrier
  `D(phi)>=D(0)cos((phi-pi/2)/3)/cos(pi/6)>=D(0)>=(3pi-8)/16`; the wall is
  now the global minimum by proof, not a sweep.  The campaign's `C=0.0705`
  was a wall-adjacent instrument artifact (see §4.2).
- **FP_4 is PROVED completely** (`FreePointZeroInsertionFP4Matching.md`):
  split at `max |c_j|^2 = 21/25`.  In the central region the exact
  logarithmic energy/variance theorem combines with a Bernstein-certified
  row envelope and rational Taylor bounds.  In the outer region the
  K4-Hoelder bound `S_4^4 <= 8W`, a symmetric-square identity, and a
  one-variable radical certificate give the strict estimate `W < 32`.
  Equality is possible only at `c_1=...=c_4=0`.  The former insertion,
  matching-stratum, and no-go results remain useful subordinate structure,
  but there is no residual FP_4 case.  The free-point family remains open
  only for `m >= 5`; RM and the Lorentzian-Gram route are now higher-degree
  routes rather than FP_4 obligations.
- **The all-degree FP-to-(S) bridge is PROVED**
  (`FreePointTorusPshReduction.md`): the symmetric critical-value functional
  is continuous plurisubharmonic on the root polydisk, so its maximum moves
  to the root torus; there the exact self-inversive identity converts it to
  `FP_{n-1}`, and the tangent inequality
  `y^{(n-1)/n} <= ((n-1)y+1)/n` corrects the exponent.  Hence
  `FP_{n-1} ==> (S)_n` at every degree.  In particular, the landed `FP_3`
  and `FP_4` now prove (S) in degrees four and five.  This advances the
  auxiliary algebraic frontier only; (S) still does not imply the parent.
- **Integrated entropy sum rule** (`TraceMaxEntropyAngularBudget.md`):
  `sum_j int log|q_j| = -(pi/sin(pi/n)) sum_k Re(v - H(c_k))^{1/n}` — the
  exact all-sheet budget for the (EX) allocation step.
- **The surviving admissible product now has a psh terminal-stratum
  reduction** (`AdmissibleCriticalArcProductPshReduction.md`): on every
  wall-free cell with fixed admissible hubs,
  `log prod_c L(c)/(2|f(c)|^(1/n))` is plurisubharmonic.  Thus the exact
  target-deciding product `(AP)` has no generic interior maximizer; its proof
  burden moves to root-boundary, admissibility-wall, saddle-connection, and
  collision strata.  Four guarded quintic holomorphic disks satisfy the
  predicted sub-mean law.  This is a reduction, not a proof of `(AP)`.
- **The first saddle-wall AP block is compressed exactly**
  (`SaddleWallPairCompression.md`): if the lower outgoing arms have lengths
  `A,B` and the upper stem plus unaffected arm has length `X`, the wall can
  choose the shorter continuation and
  `(A+B)(X+min(A,B)) <= (A+B+X)^2/2`, with exact slack
  `[X^2+(A+B)|A-B|]/2`. Thus the two normalized wall factors close under
  the single three-arm threshold
  `A+B+X <= 2sqrt(2)|w_low w_high|^(1/(2n))`. The branch-switch allocation is
  no longer an unspecified residual.
- **The scalar three-arm threshold is FALSE, while `(AP)` is exact on a full
  all-even wall family** (`SymmetricTwoLevelWallFamily.md`). For
  `f=(z^m-a^m)(z^m+b^m)`, every critical value lies on one two-level saddle
  wall, the inner edges have length `2b`, the outer edges have length `a+b`,
  and the complete admissible product is
  `r^((m-1)/2)(1+r)^m/[2^(m-1)(1+r^m)]<=1`, `r=b/a`, by the midpoint
  power-mean inequality. Equality is only the regular `2m`-gon limit. The
  parent path theorem on this centred-trinomial family was already subsumed by
  `CyclicTrinomialFiberCase.md`; the new content is the exact AP/wall
  calculation. Already at the quartic ratio `r=9/10`, the discarded scalar
  `T` threshold fails by
  exact fourth-power gap `5836/625`, while the true wall-pair square is
  `3249/3620<1`. The correct general residual retains the exact stem/imbalance
  slack:
  `T^2-X^2-(A+B)|A-B|<=8|w_low w_high|^(1/n)`, or works with the complete
  rooted merger block directly.

SAME-DAY UPDATE (2026-08-29 solve session, evening): §§1, 3, 4, 5 below carry
that session's deltas — the model star kernel became a THEOREM at every degree
(`QuinticStarKernelMechanics.md`), the two-root area gap (old gap 5) is
PROVED in existence form (`ProperComponentUniformAreaGap.md`), (SPOKE-5)
as stated is VIOLATED at an exact pocket corner, and the near-gon
adversarial geography is mapped (`TwoTierStraightStarSelectorLab.md`).

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
| Aggregate/sum form of the open inverse-ray selection producer | **FALSE**; only its SELECTION form survives | same addendum |
| Universal scalar saddle-wall threshold `T<=2sqrt(2)|w_low w_high|^(1/(2n))` | **FALSE** for the exact quartic wall `(z^2-a^2)(z^2+b^2)` at `b/a=9/10`; the true normalized pair is still `<1` | `SymmetricTwoLevelWallFamily.md` |
| Origin two-radii connector inside the near-Fekete shell (any `eta`-neighbourhood) | **FALSE** for `n = 3` (proved) and every `n >= 5` (exact rational quintic witness; 4 of 5 spokes escape by rational signs) | `NearFeketeRadialAngularSplit.md` Theorem 7 |
| (SPOKE-5) as stated (critical hub + two contained straight segments, length `<= 2`, closed disk) | **VIOLATED** at an exact on-circle rotated-gon-pocket corner: min over admissible hubs x pairs of star `sup|f| = 1.00008536426413` (two independent instruments, 35/60 dps, exact rational input; completes the deg-6/9 pattern at deg 5) | `Degree5AssemblyAndSharpenedCuts.md` addendum; `TwoTierStraightStarSelectorLab.md` |
| The OUTWARD RADIAL value-ray carrier at the trace-max hub, as a GLOBAL quintic-core mechanism | **FAILS in an open pocket** at the tangent orbit (`sup E_radial = +0.358`, cone measure `2.7%`; ray blocked by a collinear double foreign value); survives only on the one-face stratum (theorem) and at `dist >= 0.30` from the orbit (measured) | `TraceMaxRadialExcessLaw.md` (2026-08-30) |
| The SYMMETRIC K4-matching Hoelder family for FP_4 (dedicated x-column; incl. `W <= 32` and its CS polynomial variant), and more generally every UNWEIGHTED four-column row-factor permutation | **DEAD as stated**: exact extremals (`W* = 32.106...` at the triangle+origin family, `P* = 131.587...` at `u = 3/8`) and the closed-form symmetric obstruction `C >= 3/256`; for the full unweighted permutation class, majorization proves the aligned assignment is pointwise best and at `u=1/6` its product is `329/2+14sqrt(43)>256`.  Weighted/product-merged and label-minimized variants evade these exact no-gos and reach `2.19e-6` excess — measured violated, not covered by either obstruction | `FreePointZeroInsertionFP4Matching.md` (2026-08-30) |

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

Added by the same-day solve session (owner files carry full proofs):

- **The model star kernel is a THEOREM at every degree**
  (`QuinticStarKernelMechanics.md` §1): for the blow-up
  `H = w^n + sum_{k <= (n-1)/2} b_k w^k`, the trace-maximal critical hub's
  two value-ray arms join two DISTINCT tracts at the OPTIMAL level
  `D = max Re H(c) >= 0` (tangent case included), and no connector exists
  above level `D`.  Component census `#comp{Re H > t} = n - #{Re H(c) > t}`;
  hub bound `|c| <= 0.858594`; exact origin region; arm normal form with
  exact C+ constants; the excess/curvature-budget identity (the exact
  metric side); hub-shift desingularisation.
- **The quintic tangent stratum is ONE closed-form gauge orbit**
  (`320 |b_1|^3 = 27 |b_2|^4`, twist pinned at `+- i`; identification with
  `QuinticEqualityTetrahedron.md`'s equality chart; two explicit connector
  certificates there) — two independent derivations agree.
- **Sector–ellipse hub metric, trace identity/selector, spine containment,
  exact origin-ray criteria** (`NearFeketeAngularSelectorToolkit.md`).
- **The uniform proper-component area gap**
  (`ProperComponentUniformAreaGap.md`): `A_{n,k} < (k/(2n-k))^{2/n}`
  exists for all `(n, k)` — old gap 5 is now a theorem in existence form —
  plus the Schur-tail lemma for the future explicit constant.
- **FP_3** (`FreePointMeanInequalityFP3.md`): the `m = 3` free-point case
  of (S)'s reduction target.
- **Real-scale selector geography** (`TwoTierStraightStarSelectorLab.md`,
  computational): the near-gon pocket's mechanism ordering under three
  adversarial rounds — origin, critical-hub stars, and radial-truncation
  cuts die in successively deeper sub-pockets, while free-hub stars
  survive thinly and DESCENT ARMS keep a `~0.15` length margin throughout
  (`min_c L(c) <= 1.85` at every located corner).

## 4. Open gaps worth attacking (the actual ask)

1. **Conjecture (S)** — `Sigma_{k=1}^{n-1} |f(c_k)|^{1/n} <= (n-1) R`, the
   arithmetic mean of the merge-level capacities bounded by the circumradius.
   Strictly strengthens Schur–Fekete (which gives only the geometric mean),
   tight on `(z-tau)^n - lambda`, **proved for `n = 2, 3, 4, 5`**,
   adversarial sup exactly `1.000000` through `n = 13`, and unrefuted by
   every 2026-08-29 witness.  It is the surviving algebraic half of the
   refuted aggregate (`AGG ratio = S * V`; the violation is entirely in the
   metric factor `V`).  Reduces to a **free-point** inequality: for
   `c_1..c_m` in the closed unit disk,
   `(1/m) Sigma_j (prod_k |1 - conj(c_j) c_k|)^{1/m} <= 1`.  Unused
   ingredient: the rank-2 Lorentzian structure of `N_{jk} = <u_j, u_k>`,
   `u_j = (1, conj(c_j))`.  **(S) does not imply the parent by itself** — it
   is a standalone theorem worth having.  SAME-DAY (08-29): the `m = 3`
   free-point case was proved (`FreePointMeanInequalityFP3.md`).  On
   2026-08-30 the complete `m = 4` case was then proved
   (`FreePointZeroInsertionFP4Matching.md`): the central/outer split at
   `max |c_j|^2 = 21/25` combines the rowwise log-energy theorem with the
   K4-Hoelder majorant and an exact one-variable radical certificate.
   Equality is only the all-zero tuple.  The all-degree bridge
   `FP_{n-1} ==> (S)_n` is now proved in
   `FreePointTorusPshReduction.md`, including the multiple-critical psh
   removability step, exact root-torus identity, and exponent conversion.
   Thus the next free-point burden is exactly `FP_m` for `m >= 5`.  The
   all-degree small-angle insertion and adaptive rowwise theorem,
   plus RM and the Lorentzian-Gram structure, remain the leading mechanisms
   for that higher-degree frontier; there is no remaining FP_4 residual.
2. **Decide (AGG) at `n = 3` — the radial constant and its all-phase
   uniformity are now PROVED (2026-08-30), and the campaign's headline
   constant corrected.**  The
   gate-free campaign (no violation, 3500+ configs, two-tier instrument)
   stands; the matched asymptotics it asked for has landed as an EXACT
   reduction (`AggregateN3InnerModelClosedForm.md`): every cubic
   normal-forms to `z^3 - 3s^2 z - 1`, both hubs solve one inner problem
   with the single-valued label `w = 2 cos(2 nu/3)`, and

   `4R - Sigma L = 2|s| D(phi) + O(|s|^2)`,
   `min_phi D = D(0) = 3E - (9/4)K - 1/2 = 0.10944833 >= (3pi-8)/16 > 0`

   (closed form at the saddle-connection wall, elementary positivity,
   sqrt-cusp `c = 0.6917`, max `D(pi/2) = 0.6080`).
   `AggregateN3PshUniformityClosure.md` closes the former psh-uniformity
   residual: `D+9D''<=0` and
   `D(phi)>=D(0)cos((phi-pi/2)/3)/cos(pi/6)>=D(0)`, so all-phase
   positivity and the wall's global-minimum property are unconditional.
   the conversion is `C(phase) = 2 sqrt(|b_1|/3) D(phi)` (MEASURED), so
   the campaign's `C = 0.0705(1)` was a WALL-ADJACENT ARTIFACT (true
   phase-minimum at `|b_1| = 0.7` is `0.1057`); its `D = 0.375/0.489`
   rows are confirmed on the derived curve.  Third instrument-defect
   direction exhibited: branch-jump at a foreign critical value ON the
   ray (false negatives at the wall) — see §4.6.  Owners:
   `AggregateN3GateFreeCampaign.md` (+ 2026-08-30 corrections),
   `AggregateN3InnerModelClosedForm.md`,
   `AggregateN3PshUniformityClosure.md`; checkers
   `check_erdos1041_aggregate_n3_gatefree.py`,
   `check_erdos1041_aggregate_n3_inner_model.py`,
   `check_erdos1041_aggregate_n3_psh_uniformity.py`.  The `n = 5`
   open-region widening below stands.  Remaining for the cap: the
   psh-uniformity interchange (or direct `A + 9A'' >= 0`); the global
   (non-near-radial) `n = 3` decision is now a 2-real-parameter
   certified-computation target.
3. **(R1), the near-Fekete containment selector — first order PROVED;
   the metric half now has a proved base stratum, an exact extremal, and
   a measured global margin.**  The Main Theorem of
   `QuinticStarKernelMechanics.md` closes (R1)'s first-order containment
   content AT EVERY DEGREE.  2026-08-30 state of obligation (a), the
   EXCESS inequality `e_i + e_j <= 0` for the rightward arms (capture
   `cap_quick_prove_the_model_excess_inequality_ex_the_c88f4d5faf54`):
   - PROVED on the one-face stratum at every degree with the explicit
     constant `2|c*|(pi/n - 1)` (`OneFaceRadialScatteringTheorem.md` —
     the (MLS-strict) `|M| = 1` base case; radial and rightward carriers
     coincide in the constant there);
   - PROVED for the CURVED RIGHTWARD INVERSE-RAY PAIR at the isolated tangent
     orbit (`QuinticTangentCurvedExcessCertificate.md`): exact
     resultant/Sturm slope control plus rational transverse-oscillation
     bounds give `E_pair <= -19517458527181/5000000000000000 < 0` in the
     real tangent normal form.  The older straight-connector certificate
     (`QuinticTangentOrbitExactCertificate.md`) remains a separate
     target-valid rescue with quantified R5 curvature/jet stability data;
   - PROVED UNIFORMLY on the ENTIRE repeated-critical `mu=-10` phase arc
     (`QuinticMinusTenFullArcExcessCertificate.md`): for
     `phi_0=arctan(1/(2sqrt(2)))`, the fixed-box coordinates
     `t=r(q)+(k(q)-r(q))y`, `w=b(k-t)` and the exact square-integrand identity
     `h|w_y|=(k-r)^3(1-y)^2S_t^2/(S_w Delta)` remove the turn singularity.
     Exact rational branch isolation at 64 phase anchors, 640 point cells per
     signed arm, and 128 dual cells for one mean-value transport per phase
     slab prove
     `mathcal E(-10,phi)<-1/100<0` for every `|phi|<=phi_0`.  The central
     certificate (`QuinticMinusTenCentralExcessCertificate.md`, bound
     `-2853/100000`) and endpoint certificate
     (`QuinticMinusTenEndpointExcessCertificate.md`, bound `-1/80`) remain
     sharper pointwise predecessors.  Thus (EX-10) is discharged; by the
     proved wall reduction, the remaining universal model obligation (EX-U)
     is exactly (EX-W);
   - **(EX-W) has now dropped from TWO real dimensions to ONE on every
     regular wall sheet** (`QuinticWallSheetSubharmonicReduction.md`).  In
     the active-critical-root coordinate
     `mu(u)=-(5/2)(u+2)(u^2+2u+2)`, `lambda=g(u)`, fifth-root gap
     normalization freezes the wall ray and proves
     `mathcal E/|lambda|^(1/5)` subharmonic.  Hence sign on a regular sheet
     is controlled by its double-tight boundary and puncture limsups.  The
     double-tight boundary first had an exact degree-ten critical-root cover;
     `QuinticDoubleTightCriticalValueCarrier.md` now replaces it by the
     smaller unordered invariant `kappa=t/(1+t^2)`.  Its complete physical
     event set is `-1/2,(1-3sqrt(3))/13,0,(1+3sqrt(3))/13,1/2`; exact
     discriminant and denominator resultants leave exactly five
     upper-half-plane `mu` branches on four regular intervals.  A single
     compact arm chart is regular at both the double hub and infinity, so the
     remaining ordinary wall target is a finite `4 x 5 x 2 x [0,1]` atlas
     with no ordered-root reconstruction or tail chart.  The
     direction-dependent triple-hub limits are
     now also PROVED NEGATIVE
     (`QuinticMinusTenWallLimitSideArmCertificate.md`): the three approach
     lobes limit to `{T_0,T_1}`, `{T_1,T_4}`, `{T_0,T_4}`; a degree-110
     no-turn Sturm certificate gives the missing shallow-arm bound
     `e_0<-13/15`, hence exact pair ceilings `-23/30`, `-1/80`, `-47/48`.
     Thus every `mu=-10` puncture limsup is closed.  The two formerly open
     endpoint rays on the gap-zero fibre are now also PROVED NEGATIVE
     (`QuinticMuStarEndpointExcessCertificate.md`): exact
     resultant/Sturm/Krawczyk atlases on the factorization
     `P(u)=(u^2-1)^2(u+i sqrt(5))` give
     `E_+<-47/125` and `E_-<-2/5`, hence both are `<-3/8`.
     `QuinticMuStarAngularFiberReduction.md` then controls the whole allowed
     half-circle at `mu=(-70+10i sqrt(5))/27`, and conjugation handles the
     other `mu_*`; the global phase Sturm theorem gives an independent
     endpoint-domination route.  Consequently the **sole remaining
     model-metric burden is the compact `4 x 5 x 2 x [0,1]` double-tight
     atlas**.  Its three interior event fibres are now excised exactly
     (`QuinticDoubleTightCompactAtlas.md`): certified margins give
     `E<-1/6` at `kappa_-` and `E<-1` at `kappa_+`, while the squarefree
     Newton charts plus the already-closed `mu=-10` and `mu_*` limits give a
     negative neighborhood of `kappa=0`.  The effective residual is only
     the disjoint compact regular branch truncations between those
     neighborhoods;
   - MEASURED globally true on the quintic core with uniform margin
     `0.0362736374`, extremal at that same point; coercivity invariant
     `|c*|`, NOT `Delta_5` (`TraceMaxRadialExcessLaw.md`);
   - exact all-sheet currency available: the integrated entropy sum rule
     (`TraceMaxEntropyAngularBudget.md`); the open step is the
     TWO-SHEET ALLOCATION, routed through `|c*|`.
   - exact universal compactification available:
     `QuinticTraceMaxUniversalChamber.md` proves
     `E_pair=|c*| mathcal E(mu,phi)`, identifies trace-maximality with an
     algebraic three-gap chamber, and proves the explicit outer bound
     `|mu|<67500`.  Thus the whole quintic (EX) obligation is one compact
     three-real-variable certification problem with the hub scale deleted;
     `mu=0` is closed by the one-face theorem, the isolated tangent point is
     closed by its curved-excess certificate, and the entire `mu=-10` phase
     arc is closed by its uniform quadratic-arm certificate.  Its real-`mu`
     chamber is classified
     exactly as two algebraic intervals plus the isolated tangent point; the
     sharp real-axis radius is `197.4409737432...`.  The critical gap also
     collapses from the fixed quintic to the bilinear formula
     `x(2mu+20-3mu x)/5`.  The later wall-sheet theorem sharpens the
     remaining exact target to the one-dimensional degree-ten carrier and
     its exceptional fibres rather than a two-dimensional wall cover.
   Obligation (b), the real-scale remainder budget, remains OPEN but its
   previous naive form is now computationally refuted
   (`QuinticModelRealTransferLaw.md`): at an exact-root tangent-orbit
   specimen the model-selected hub has positive real excess about
   `+0.0024` even though its model excess is negative.  The real trace-max
   hub stays deeply safe on 263/263 sampled quintics, but that is a measured
   degree-five law, not a theorem, and a replayed near-square quartic shows
   it is false as an all-degree principle.  The degree-five endgame sweep
   (`QuinticEndgameResidualMap.md`) finds no counterexample and localizes the
   true real residual to a linear `|c|` cusp at the regular pentagon
   (measured adversarial max `min_c L=1.985293810`; exact boundary value
   `2` at `z^5-1`).  Thus an eventual consumer must prove either a small
   model-hub transfer window or the degree-five real-hub cusp with explicit
   remainder; the measured laws are not promoted to proof.
4. **Degree-5 finite-certificate targets (REDIRECTED — (SPOKE-5) as
   previously stated here is refuted, see §1).**  In order of measured
   robustness in the pocket: (i) the descent-arm bound `min_c L(c) <= 2`
   over admissible hubs (the canonical carrier of §2; containment
   automatic, `min_c L <= 1.85` at every adversarial corner) and the
   free-hub two-segment family (`TwoSegmentContainmentReduction.md`);
   the new cellwise psh theorem for the surviving admissible product
   (`AdmissibleCriticalArcProductPshReduction.md`) independently removes
   generic cell interiors and gives a second finite-certificate route on the
   root/admissibility/saddle/collision terminal strata;
   (ii) the length-free Form A-cut family (`TruncatedSpokeReduction.md`,
   atlas-aligned) on the bulk, carried at real scale by the exact
   remainder budget (`FormACutQuantitativeExpansion.md` (S)) — model
   margins alone fail near the gon (measured, round 3).  Capture:
   `cap_quick_build_the_cut_5_finite_certificate_for_d_b122beb7e514`.
5. **Two-root component area bound — PROVED, and now EXPLICIT
   (2026-08-30)**: `ProperComponentUniformAreaGap.md` gives
   `A_{n,k} < (k/(2n-k))^{2/n}` for all `(n, k)`;
   `ProperComponentExplicitAreaConstant.md` makes it numeric:
   `A_{5,2} <= 4^{-2/5}(1 - 6.76e-8)` (exact-rational certificate
   `L(13/50000)^2 <= 15/16777216`; elementary fallback `8.27e-11`),
   hence `Theta_{5,2} >= 0.940354223795` — explicit `+1.362e-8`.  The
   measured `0.482`/`0.264` show the TRUE gap is far larger; the route
   itself caps near `1.1e-7`, so sharpening toward the measured value
   needs a new mechanism (open, low priority), not better roundings.
   General table: `(5,1): 2.5e-11`, `(5,3): 1.1e-5`, `(6,2): 2.1e-10`.
6. **Instrument law to adopt**: the binding degeneracy for arm measurements
   is a foreign critical **value** near the descending segment `[0, f(c)]`,
   invisible to critical-**point** separation gates.  Use
   `value_gap := min_{i != j} dist(f(c_j), segment[0, f(c_i)]) / |f(c_i)|`.
   An apparent (AGG) violation at `value_gap = 1.2e-16` was adjudicated FAKE;
   the certified witnesses sit at `~1e-9`.  THREE defect directions are now
   on record: UNDER-report at degenerate hubs (NEG 32/42/49), OVER-report at
   nearly-double critical points (`AggregateN3GateFreeCampaign.md` Result 3),
   and BRANCH-JUMP at a foreign critical value ON the ray — false negatives,
   up to false violations, at a saddle-connection wall
   (`AggregateN3InnerModelClosedForm.md` §3; the admissible instrument there
   is a globally single-valued branch label).
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

Same-day pocket geography (computational, three adversarial rounds +
35/60-dps adjudication of every corner): uniform-angle on-circle quintics
close by the origin tier alone (1500/1500); the hard territory is
exclusively the rotated-gon pocket, where straight mechanisms die in the
order origin -> critical-hub stars -> radial-truncation cuts as the corner
deepens, while free-hub stars survive thinly and descent arms never
dropped below a `0.15` length margin.  Checkers for the same-day results:
`scripts/check_erdos1041_angular_selector_toolkit.py`,
`scripts/check_erdos1041_two_tier_selector_lab.py`,
`scripts/check_erdos1041_quintic_star_kernel_mechanics.py`,
`scripts/check_erdos1041_proper_component_area_gap.py`,
`scripts/check_erdos1041_free_point_fp3.py`.

Checkers for the 2026-08-30 proof wave (all green at landing):
`scripts/check_erdos1041_one_face_radial_scattering.py`,
`scripts/check_erdos1041_tangent_orbit_exact_certificate.py`,
`scripts/check_erdos1041_quintic_tangent_curved_excess.py`,
`scripts/check_erdos1041_trace_max_entropy_budget.py`,
`scripts/check_erdos1041_explicit_area_constant.py`,
`scripts/check_erdos1041_aggregate_n3_inner_model.py`,
`scripts/check_erdos1041_aggregate_n3_psh_uniformity.py`,
`scripts/check_erdos1041_free_point_zero_insertion_fp4.py`,
`scripts/check_erdos1041_trace_max_radial_excess.py`.

## 6. Evidence classes used here

Ordinary proved mathematics; exact rational/interval certificates; 50-dps
mpmath certificates with independent-instrument agreement; and adversarial
measurement (never presented as proof).  Each owner file labels its own rows.
Checkers for the 2026-08-29 results:
`scripts/check_erdos1041_minimal_hub_arm_budget_refutation.py`,
`scripts/check_erdos1041_separatrix_aggregate.py`,
`scripts/check_erdos1041_near_fekete_radial_angular_split.py`,
`scripts/check_erdos1041_degree5_sharpened_cuts.py`.
