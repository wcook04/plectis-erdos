# Erdős 1041: the two-tier straight-star selector — (SEL-5) at real scale, with independent corroboration of the model-core coverage

Date: 2026-08-29.  Origin: main-loop solve session (operator-directed creation
push), three independent instruments, all run in the main loop; positioning
against the landed atlas corrected after the same session's corpus-mining
pass.  Checker: `scripts/check_erdos1041_two_tier_selector_lab.py`.
Companion theory: `NearFeketeAngularSelectorToolkit.md` (sector–ellipse
metric, trace selector, spine classification, origin-ray criteria — all
proved there).

Positioning (read first).  The MODEL-level quintic core is already CLOSED by
`QuinticMixedGlobalAtlas.md` (3,834 strict Bernstein boxes; connector = a
chord between two fifth-root directions at a common truncation radius plus
ray tails; coordinate dictionary `b_1 = -A`, `b_2 = -B`,
`max(|A|,|B|) = 1`), with the pure faces additionally closed by
`QuinticSecondModeConnector.md` (model level, exact `-1/1000` chord margin)
and `CyclicTrinomialFiberCase.md` (globally, at actual-polynomial level, via
origin spokes for trinomials).  What that certificate does NOT reach is real
scale: its transfer (`QuinticTransverseFiniteTransfer.md` Corollary B)
requires `rho <= 1e-20`, while the degree-5 residual band sits at
`rho ~ 0.25` — a 19-order-of-magnitude transfer gap.  This note's
contribution is therefore twofold: (i) an INDEPENDENT mechanism (straight
two-segment stars at a deterministically selected hub, instead of the
atlas's chord) that covers the same model core in a fresh scan, and — the
substantive part — (ii) computational evidence that this mechanism closes
the ACTUAL on-circle family at amplitudes covering and far exceeding the
residual band, i.e. exactly across the transfer gap that the certified
model route cannot cross.  A certificate of (SEL-5) at real scale would
bypass the blow-up transfer entirely.

This note records a COMPUTATIONAL LAW (not a theorem).  Everything below is
labeled by evidence class; nothing here is a parent-theorem claim.

## (SEL-5): the straight-line selector law (statement; conjectural, revised
## after two adversarial rounds — see the evidence section for the history)

Let `f` be a monic quintic with all roots on the unit circle.  Then at least
one of the following PIECEWISE-LINEAR connectors closes `f` in the closed
normalization (path in `{|f| <= 1}`, length `<= 2`):

- **Tier 1 (origin):** two full radial segments `[0, a_k]` contained;
- **Tier 2 (hub stars):** an admissible critical point `c` (`|f(c)| <= 1`),
  or a slid hub `t c` (`t in (0,1]`), with two roots at total distance
  `<= 2`, both straight segments contained;
- **Tier 3 (truncated cut / Form A-cut):** roots `a_i, a_j`, truncations
  `s_a, s_b in [0.25, 0.95]`, with `[a_i, s_a a_i] u [s_a a_i, s_b a_j] u
  [s_b a_j, a_j]` contained (length automatic: `<= |a_i| + |a_j| <= 2`).

Backstop (never yet needed on any sampled or adversarial point): the
descent-arm bound `min_c L(c) <= 2` over admissible hubs — containment is
automatic for descent arms, and the measured minimum stayed `<= 1.79` at
every adversarial corner.

The original two-tier form of this law survives on random samples but NOT
adversarially; the evidence section records both refinement rounds
honestly.  Original two tiers:

- **Tier 1 (origin).**  At least two full radial segments `[0, a_k]` lie in
  `{|f| <= 1}`.  (Then the two-radii path closes the closed-normalization
  parent for `f`: length `<= 2` automatic.)
- **Tier 2 (admissible hubs + bracketing stars).**  SOME critical point `c`
  with `|f(c)| <= 1` (the admissible set is nonempty off the tangent stratum
  by the trace selector, `NearFeketeAngularSelectorToolkit.md` Corollary B1)
  satisfies: both straight segments from `c` to the two roots angularly
  bracketing `c` lie in `{|f| <= 1}`, and `|c - a| + |c - b| <= 2` (the
  length side is automatic with margin by the sector–ellipse theorem when
  the roots are near a gon; enforced directly in all instruments).  This is
  a deterministic finite test: at most `4` hub–pair combinations, each hub
  paired only with ITS bracketing roots.

  ADVERSARIAL CORRECTION (same session): the stricter one-hub rule "take
  the admissible hub of smallest `|f(c)|` only" — which passed 1800 random
  samples with zero fallbacks — is REFUTED by an adversarial campaign
  (Nelder–Mead + differential evolution on the tier margin): near
  common-rotation gon configurations it fails by `~1e-4` while a SIBLING
  admissible hub's bracketing star closes the same configuration with
  margin `~2.2e-4`.  Four adversarial optima were adjudicated at 35 dps:
  in each, exactly one origin spoke is contained (the adversary correctly
  kills Tier 1), the near-origin critical point is inadmissible
  (`|f| = 1.000073`), the three outer critical points are admissible with
  nearly tied values (`0.99975`–`0.99980`), and at least one of them closes
  the configuration (`sup |f| <= 0.9997987`, `L <= 1.682`); the Form A-cut
  chord (`r = 0.5`, the landed atlas connector shape) ALSO closes all four
  (`sup |f| <= 0.99985`).  Random sampling had missed this corner entirely
  — the corpus's adversarial-supremum lesson reproduced in-session.

  SECOND ADVERSARIAL ROUND (attacking the corrected multi-hub functional):
  the optimizer drove into the rotated-gon pocket proper
  (`delta ~` common rotation + residual `~4e-3`) and found three corners
  where the multi-hub bracketing star ITSELF fails at 35 dps
  (`sup |f| = 1.0000009`–`1.0000854`), one of which
  (`delta = (0.0689, 0.06052, 0.0681, 0.06473, 0.06125)`) also defeats
  every origin spoke (0 contained) and the coarse common-radius chord grid.
  ESCALATION ADJUDICATION (35 dps, same point): three independent
  mechanisms all close it —
  (i) DESCENT ARMS from the admissible hubs: `min_c L(c) = 1.7885 <= 2`
  (containment automatic; endpoints land on two distinct roots to 1e-16) —
  matching the corpus's residual-band measurement (`min_c L(c)` max
  `1.9858`, never above 2);
  (ii) ASYMMETRIC Form A-cut with smaller truncations:
  `sup |f| = 0.999886911 < 1` at pair `(2,4)`, `s = (0.35, 0.35)` — the
  earlier chord failure was a grid artifact (radii `>= 0.5` only);
  (iii) slid-hub star with free pair: `sup |f| = 0.9999668` at
  `h = 0.95 c`, pair `(3,4)`.  The other two second-round corners close the
  same three ways (`min L = 1.749, 1.770`; cut sups `0.999773, 0.999841`).

  Net shape of the law after both adversarial rounds: straight-line tiers
  (origin, hub stars, slid stars, truncated cuts) cover everything found,
  with the truncated CUT — exactly the landed atlas's connector shape —
  taking over in the rotated-gon pocket, and the descent-arm bound
  `min_c L(c) <= 2` never yet needed as more than a backstop.

  CONSEQUENCE FOR (SPOKE-5) — frontier-relevant, stated exactly.  At the
  corner `delta = (0.0689, 0.06052, 0.0681, 0.06473, 0.06125)` (EXACT
  rational multipliers of the gon angles; roots on the unit circle, hence
  inside the closed-disk hypothesis class), the 35-dps adjudication gives:
  exactly two critical points are admissible (`|f(c)| = 0.999882188,
  0.999886801`; the other two are inadmissible at `1.0000052, 1.0000512`),
  and the MINIMUM over both admissible hubs and ALL root pairs with
  `|c-a|+|c-b| <= 2` of `sup |f|` on the two straight segments is
  `1.00008536` — every critical-hub straight star escapes `{|f| <= 1}`.
  Since (SPOKE-5) (`Degree5AssemblyAndSharpenedCuts.md`) asks precisely for
  a critical hub with two contained straight segments and length `<= 2`,
  THIS CONFIGURATION VIOLATES (SPOKE-5) AS STATED (evidence class:
  high-precision numerics on exact rational input, replayable via the
  checker; not an interval certificate).  It completes the pattern already
  proved at degrees 6 and 9 (`StraightSpokeHubCriterionLab.md`): the
  critical-hub straight-spoke mechanism fails in the rotated-gon pocket at
  degree 5 as well.  The corpus's earlier adversarial pin for (SPOKE-5)
  (`0.9999997708`, maximised at `z^5 - 1`) searched the beta-chart around a
  different functional and did not enter this pocket.  CONSTRUCTIVE
  REDIRECT: the degree-5 finite-certificate target should be the
  length-free cut family —

  > (CUT-5): every monic quintic with roots in the closed unit disk admits
  > roots `a_i, a_j` and truncations `s_a, s_b` with the three segments
  > `[a_i, s_a a_i] u [s_a a_i, s_b a_j] u [s_b a_j, a_j]` in
  > `{|f| <= 1}` —

  which carries the SAME parent wiring (`TruncatedSpokeReduction.md`: Form
  A-cut implies Erdős 1041, no length condition at all), is exactly the
  connector shape the model atlas already certifies in 3,834 boxes, and
  closed every configuration of the first two adversarial rounds.

  THIRD ADVERSARIAL ROUND (attacking origin|cut) — the cut is NOT universal
  either.  The optimizer went deeper into the gon limit (residual `~2e-3`
  off a pure rotation: `delta = (0.02673, 0.02557, 0.02867, 0.02503,
  0.02814)` and `(-0.11153, -0.10843, -0.11185, -0.10915, -0.10997)`) and
  found the FULL asymmetric-cut search (`(s_a, s_b) in [0.25, 0.95]^2`,
  all ordered pairs) failing at both corners (`sup |f| = 1.0000067`,
  `1.0000084` at 30 dps) — the `~rho^6` remainders swamp the model-level
  cut margin at this depth: the corpus's transfer problem, measured live.
  At the same corners: slid-hub stars still close, thinly
  (`sup = 0.9999854, 0.9999897` at `h = 0.9 c`), and DESCENT ARMS close
  with a large structural gap (`min_c L(c) = 1.8307, 1.8334`; containment
  automatic).  Measured mechanism ordering at the gon limit: origin dies
  first, critical-hub straight stars next, radial-truncation cuts next;
  free-hub stars survive thinly; descent arms keep a `~0.15` length margin
  throughout every round.  The robustness of descent has a visible
  mechanism: the near-gon quadruple critical point splits at scale
  `delta^{1/4}`, so admissible hubs sit far from the origin even for tiny
  perturbations, buying `~2 cos(pi/5) |c|` of length saving while
  containment is automatic — exactly why `min_c L(c) <= 2` is FRONTIER's
  canonical surviving metric row.  REFINED RECOMMENDATION (supersedes the
  bare (CUT-5) line above): the robust pocket mechanisms for a finite
  certificate are, in order, (i) the descent-arm bound `min_c L(c) <= 2`
  (canonical row; biggest measured margins) and the free-hub two-segment
  family (`TwoSegmentContainmentReduction.md`); (ii) (CUT-5) remains the
  right shape on the model-certified bulk, but its REAL-scale use near the
  gon must carry the exact remainder budget
  (`FormACutQuantitativeExpansion.md` certificate (S)), not model margins
  alone.

Tier 2 is exactly the (SPOKE-5) mechanism of
`Degree5AssemblyAndSharpenedCuts.md` with a DETERMINISTIC hub-and-pair rule;
Tier 1 is the origin member of the `TwoSegmentContainmentReduction.md`
sufficient family.  Either tier closes the sampled polynomial for the parent
in closed normalization.

Consistency notes.  (i) The hub rule is NOT the refuted argmin-critical-value
rule: it selects among ADMISSIBLE hubs only, ties are broken by position
(bracketing pair), and the refuted row concerned descent-arc length `L(c*)`,
not straight segments.  On the exact rational origin-refutation witness the
raw argmin critical point is INADMISSIBLE (`|f| = 1.0000178`) while the
selected hub is admissible and works — the two rules genuinely differ.
(ii) (SEL-5) is quintic-specific in ambition: straight-star hub criteria are
FALSE at degrees 6 and 9 (`StraightSpokeHubCriterionLab.md`), so no claim is
made beyond `n = 5`.

## Evidence (three independent instruments, main loop)

1. **Model-core scan (blow-up level).**  For the self-inversive quintic
   blow-up `H(w) = w^5 + b_2 w^2 + b_1 w` on the gauge core
   `max(|b_1|^{1/4}, |b_2|^{1/3}) = 1` (both branches, full phase torus,
   55,296 grid models; then a 30x30x8 rescan and 5x local refinement of the
   40 tightest cells): EVERY model is closed by
   `O` (>= 2 exactly-safe origin rays, per the exact criterion; 76.4%),
   `C+` (a critical point with `Re H(c) > 0` whose bracketing adjacent pair
   has both straight arms `[c, 8 u]` in `{Re H >= 0}`; 19.0%), or
   `F+` (hub slid along `[0, c]`, same test; 4.6%).  RESIDUAL: **empty**, in
   both scans and in every refined cell.  Worst observed `C+` margin
   `6.7e-4` (locally refined); the `F+` winning pair was the bracketing pair
   in 795/795 recorded cases, so the model selector is two-tier as stated.
2. **Real-scale sweep (actual polynomials).**  On-circle quintics
   `a_k = exp(i(2 pi k/5 + delta_k))`, `delta` uniform with amplitude
   `A in {0.02, ..., 0.5}` (covering `1 - D` from `1e-3` to `0.52`; the
   degree-5 residual band sits at `1 - D ~ 1.4e-2`): 960 samples with the
   search form and 1800 samples with the one-hub form: **zero failures on
   random samples** (the one-hub form's adversarial refutation and the
   corrected `<= 4`-hub form are in the Tier-2 statement above).  Worst
   Tier-2 containment margin on random samples grows with amplitude
   (`1.9e-3` at `A = 0.05` to `1.1e-1` at `A = 0.45`): the delicate zone is
   the small-amplitude near-gon region, where the adversarial corner lives
   and where the multi-hub form (and, redundantly, the chord tier) takes
   over.
3. **The hardest exact point.**  The exact rational origin-refutation witness
   (`NearFeketeRadialAngularSplit.md` Theorem 7; kills Tier 1 by
   construction: 4 of 5 spokes escape) sits at blow-up coordinates
   `b_1 = 0.2717`, `b_2 = 1.0000` (b_2-dominant mixed model, 1 safe origin
   ray).  The trace selector gives `max Re H(c) = +0.1323` at the model hub
   `c* = -0.6844`; the transferred ACTUAL critical point `c = -0.191021`
   is admissible (`|f(c)| = 0.999774992`) and its bracketing straight star
   (to the roots `-0.8124 +- 0.5831 i`, the model-predicted adjacent pair) is
   fully contained: `sup |f| = 0.999775057` (containment margin `2.2e-4`),
   length `1.7043` (margin `0.296`).  The mechanism transfers at
   `rho = 0.2509` — far beyond the micro-neighbourhood scale of the quintic
   atlas.

Instrument notes: grids `1501`–`20001` points per segment; tier boundaries
cross-checked at `4001`; margins quoted are grid minima of `Re H` (model) or
`1 - sup |f|` (real scale).  Precision: float64 with mpmath 30–40 dps
replays of the witness data.  Adversarial caveat: instruments 1 and 2 sample;
only instrument 3 is an adversarially-constructed point.  No interval
certificate exists yet; that is the named next step.

## Why this localizes the remaining degree-5 work

- The open degree-5 problem is a TRANSFER problem, not a mechanism problem:
  the model core is certified (atlas, above) but only reaches
  `rho <= 1e-20`; the residual band lives at `rho ~ 0.25`.  (SEL-5) attacks
  it from the other side: every tier is a direct test on the ACTUAL
  polynomial, so certifying (SEL-5) on the on-circle family needs no
  blow-up transfer at all.
- Certificate architecture suggested by the adversarial geography: in the
  rotated-gon pocket the winning connector is the truncated CUT — the same
  shape the atlas certifies at model level — so the natural finite
  certificate REUSES the atlas's per-box connector choices (pair +
  truncation radius) as candidate generators and verifies each candidate
  directly on the actual polynomial via the landed finite-expansion budget
  (`FormACutQuantitativeExpansion.md`'s certificate (S): model value +
  `B_M(r, eta)` budget `< 0`), instead of the `rho <= 1e-20` remainder
  chain.  The measured pocket margins (`~1e-4` at `eta ~ 5e-3`–`3e-2`)
  against the budget's size is then the box-refinement driver.
- Both tiers are finite, explicit tests: Tier 1 is five one-variable
  polynomial positivity checks; Tier 2 is one hub (a root of the quartic
  `f'`) plus two segment positivity checks of degree 10 in one variable.
  A Bernstein/Sturm certificate over the compact on-circle parameter torus
  (4 angles mod rotation, amplitude bounded by the existing coverage map's
  band) is the natural finite closure of the on-circle family; the interior
  then follows from the landed radial reduction where its hypothesis applies
  (`NearFeketeRadialAngularSplit.md` Theorems 3/3a) and the existing
  coverage families elsewhere.
- The margin structure is favorable: tier margins vanish only where the other
  tier takes over, and the Tier-2 margin GROWS with amplitude.
- Terminology guard (naming collisions are live in this directory): the
  (SEL-5) "hub star" is NOT the atlas's "Form A-cut chord" (different
  connector through the same territory); and the toolkit's TANGENT STRATUM
  (all critical values purely imaginary — trace-tangent) is NOT
  `NearFeketeTransverseClosure.md`'s tangent direction (small first mode).
  The exact rational witness below is second-mode dominant (transverse-file
  "tangent") but NOT trace-tangent (`max Re H(c) = +0.132 != 0`).

## Claim boundary

(SEL-5) is a CONJECTURAL LAW with multi-instrument computational support
(grid resolutions and precisions stated above), REVISED TWICE under
adversarial attack within the same session — the revision history is part
of the record above, and the final form is the three-tier piecewise-linear
law plus the descent backstop.  It is NOT proved, and no interval
certificate is claimed.  The model-core emptiness of the residual is a
sampled statement (55k + refinements), not a proof.  No tier's containment
has an analytic proof yet in any sub-band.  Nothing here touches degrees
other than 5 (hub-star mechanisms are FALSE at degrees 6 and 9 per
`StraightSpokeHubCriterionLab.md`; the tiered law as a whole is untested
beyond 5).  The parent theorem is not claimed.  The hub rules use
admissibility and position, not critical-value moduli alone, and so do not
conflict with the FRONTIER selection firewall; on trace-tangent models
(all critical values imaginary) the hub tiers can degenerate — that
stratum is classified in `NearFeketeAngularSelectorToolkit.md` Theorem D
and is part of the certification surface, not exempt from it.  Adversarial
searches used Nelder–Mead + differential evolution on float64 with 35-dps
mpmath adjudication of every located corner; float-level negatives smaller
than `~5e-5` near the gon are at the instrument's noise floor (quadruple
critical-root splitting), which is why every corner was re-adjudicated at
high precision before being treated as real.
