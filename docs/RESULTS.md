<!-- SPDX-FileCopyrightText: 2026 Will Cook -->
<!-- SPDX-License-Identifier: Apache-2.0 -->

# Results and limits

This repository formalises finite results, reductions, equivalences, and
obstructions related to eight Erdős problems — #68, #243, #249, #251, #257,
#269, #1041, and #1049 — with #249 and #257 as the two reviewed core
programmes. It does not solve any of them.

Lean source checked by the pinned Lean kernel is proof authority. The audit log
reports the headline declarations below with kernel assumptions
`[propext, Classical.choice, Quot.sound]`. A theorem with hypotheses proves only
the displayed implication; it does not prove that its hypotheses occur.

## Ten-minute verdict

All eight Erdős problems remain open. The development is neither a partial
solution nor an empty collection of restatements. For a first mathematical
pass, the high-signal spine is:

- **#257, a completed unconditional endpoint theorem in the full-support
  case.** The checked divisor-block proof combines a bounded Bertrand/CRT first
  block, middle-window divisor-pair averaging, weighted tail control, and
  parameter closure (`irrational_erdosSum_full_support`). It proves the
  canonical full-support series irrational in every integer base `b ≥ 2`, but
  not universal #257. A distinct adaptive-CRT certificate proves irrationality
  for every infinite pairwise-coprime support with summable reciprocal mass;
  those structured-support hypotheses likewise leave arbitrary support open.
- **#249, a constructive kernel-rank spine.** The exact dyadic totient-kernel
  rank `2^e + 1`, its odd-core basis, and the resulting infinite-dimensional
  span expose a real finite-level mechanism; the all-base rank is conditional
  on the displayed affine independence input. None of these gives a
  rationality-to-finite-rank bridge or solves the binary totient endpoint.
- **#68, an exact endpoint reduction.** Irrationality is equivalent to
  cofinally many strict factorial-top divisibility misses, equivalently to
  cofinally many non-unit carries. The equivalence transfers the hard
  producer question exactly; it does not supply that producer.
- **#243 and #251, boundary results that diagnose the missing input.** Fresh
  pairwise-coprime moduli obstruct bounded rises, while periodic/vanishing
  negative-error regimes are excluded; for #251, unbounded prime gaps and an
  exact prime-gap irrationality equivalence still leave the concrete tail
  bridge open.
- **#269, #1041, and #1049, structurally useful route checks.** Running-LCM
  height and rank-two obstructions, finite translation/root-retention inputs
  plus a diagnosed saddle gap, and the rational-base recurrence/no-go at
  `3/2` each isolate a mechanism without claiming the endpoint.

The finite #249 certificate band, Stern–Brocot and gcd-moment identities,
#257 measure/noncollapse geometry, and the cited-only ladders remain useful
supporting routes. They are deliberately secondary to the mechanisms above:
finite ranges do not become cofinal theorems, and cited analytic inputs do
not become Lean results by appearing in the same paper.

### Signal-audit dispositions

These are editorial dispositions for first-contact signal, not novelty,
priority, or proof-status claims. The detailed sections below retain the
full evidence and exact boundaries.

| Disposition | Reader-facing treatment | Mathematical reason |
|---|---|---|
| **promote** | #257's full-support irrationality theorem and distinct pairwise-coprime extension, #249 finite kernel rank/basis, and #68's exact carry/divisibility equivalence lead the first pass. | The #257 full-support row is an unconditional endpoint theorem for each `b ≥ 2`; the other promoted rows expose adaptive-CRT, finite-rank, and exact-equivalence mechanisms with their hypotheses visible. |
| **retain** | #243 bounded-rise/negative-orbit exclusions, #251's equivalence and countermodel, #269's height/rank obstruction, #1041's ray/root route, and #1049's recurrence/no-go remain the strongest boundary for each problem. | Each rules out a named regime or supplies an exact structural identity, but none supplies the missing universal, cofinal, topological, or irrationality bridge. |
| **consolidate** | The adjacent #249 gcd-moment, Stern–Brocot, finite-denominator, and synthetic LCM-shift results form one supporting arithmetic route; #257's geometry, finite-period, state, and defect results form one supporting universal-boundary route. | These results reuse finite-level or finite-support interfaces and share the same endpoint gap; grouping them preserves the mechanism without making repeated local identities look like separate endpoint advances. |
| **demote** | Citation-only #249 context and other classical formalised variants follow the local checked mechanisms; the canonical #257 full-support theorem stays promoted. | Provenance and known formalised cases establish context or a restricted theorem, not a new #249 conclusion; the completed full-support mechanism is the explicit exception because it is a direct checked endpoint case. |
| **replace** | The old citation-first/problem-order first pass is replaced by this mechanism-first spine; the eight problem sections remain the verification index. | Consequence and load-bearing mechanism are more informative to a first reader than paper order, while the per-problem sections preserve complete coverage and exact source routes. |
| **long-tail-only** | Finite searches, measurement logs, routine certificate shards, and unselected conditional predicate stacks remain discoverable through the source maps, but do not lead the reader. | A finite range, routine shard, or unconstructed antecedent cannot establish a cofinal family or universal endpoint, so it is evidence for follow-up rather than first-contact signal. |

The project also audits its own conditional routes. Of 23 substantial Lean
propositions extracted from hypotheses of conditional theorems, 17 are
provably equivalent to an endpoint—14 to #249 and 3 to the `1/2` membership
test for #257. This is a self-diagnosis of reformulation failure, not progress
on either endpoint.

<!-- BEGIN semantic_public_census -->
Only after those theorem-level facts comes the corpus census. The current semantic graph provides three diagnostic views across every indexed Erdős problem:

| View | #68 | #243 | #249 | #251 | #257 | #269 | #1041 | #1049 | both | shared | total |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| mechanically nonrecurring candidates | 0 | 3 | 88 | 0 | 168 | 0 | 0 | 5 | 0 | 19 | 283 |
| classical/prior-art formalisations | 0 | 1 | 36 | 0 | 23 | 0 | 0 | 1 | 0 | 40 | 101 |
| bare open-problem equivalences | 0 | 0 | 15 | 0 | 15 | 0 | 0 | 0 | 0 | 2 | 32 |

The nonrecurring view contains 183 unconditional object theorems, 54 scoped barriers, and 46 reductions or transports after aliases, open antecedents, bare equivalences, finite/generated instances, infrastructure, classical results, and routine corollaries are removed.

The internal adjudicated frontier shortlist contains 11 nodes; it is distinct from the 8-node public prior-art review queue. 228 nonrecurring candidates remain unassessed for prior art. The live authored open-antecedent surface has 52 clusters, of which 10 are marked endpoint-equivalent. None of these populations is a novelty census.
<!-- END semantic_public_census -->

The large #249 denominator exclusion is a direct, kernel-checked instantiation
of the classical neighbouring-fraction/mediant method. That method supplies the
displayed bound exactly (numerical delta `0`). The local addition is the checked
arithmetic instance, its transfers, and its sharp first failure.

The census is reproducible with:

```sh
python3 scripts/query_semantic.py nonrecurring
python3 scripts/query_semantic.py bare-equivalences
python3 scripts/query_semantic.py classical
python3 scripts/query_semantic.py open-antecedents
```

## Strongest checked results by problem

This is a high-signal orientation by problem, not a one-result roster: it gives
the strongest checked statements, their exact status, and where to verify them.
Each item carries the independent labels used across this repository: what Lean
checked, what the statement changes, and its literature relationship.
`formalised here` renders known mathematics;
`proved here` makes no novelty claim — that judgement is a human number
theorist's, and no query here supplies it. Reduction targets are named with
their own status in the same sentence. The reviewed claim registry
([`docs/claims.json`](claims.json)) covers the #249/#257 core; entries marked
*registry: none* are kernel-checked source whose reviewed claim rows do not
yet exist, and [`docs/problems.json`](problems.json) is the per-problem
authority for the six expansion problems.
For the complete per-problem family inventory with evidence classes, exact
Comparator dispositions, and surviving boundaries, use the machine-readable
[`docs/problems.json`](problems.json) authority. The generated
[`docs/EXTERNAL_VERIFICATION.md`](EXTERNAL_VERIFICATION.md) is the
reader-facing projection of the selected executable proposition set and its
Comparator routing; it is not the full family census. Treat an entry as
checked only at its stated scope, and do not use either projection as a
replacement for claim authority.

**#68 — is `∑_{n≥2} 1/(n!−1)` irrational?**

- Irrationality is equivalent, with no hypotheses, to one integer
  divisibility test on exact rational prefixes failing infinitely often —
  `irrational_factorialGapSeries_iff_cofinal_strictFacTopRat_misses`,
  `ErdosProblems/Erdos68/FactorialZeroPlateau.lean:1090`. Checked theorem;
  exact equivalence, transporting the difficulty without reducing it;
  registry: none.
- A separate finite quotient-band obstruction is now explicit. For a finite
  coefficient family whose indices all satisfy `k d ≤ i_j < (k+1)d`, the
  factorial moment factors as `M = (d!)^k C_d`; in the first band, channel
  cancellation `C_d = 0` therefore forces `M = 0`. More generally, if all
  indices are at least `d`, channel cancellation with `M ≠ 0` forces some
  index to be at least `2d` (`ErdosProblems/Erdos68/ChannelBreakpointRigidity.lean`;
  paper discussion in `erdos-68-factorial-denominator-irrationality.pdf`).
  This is a finite-family breakpoint only: it supplies no cancelling family,
  simultaneous-channel control, residual estimate, or cofinal non-unit carry.
- The kernel-internal denominator bound is `q ≥ 67`
  (`ErdosProblems/Erdos68/FactorialZeroPlateau.lean:940`); the `300000`
  exclusion is a checked implication
  (`ErdosProblems/Erdos68/FactorialZeroPlateau.lean:876`) whose evaluation is an external
  computation, not a kernel result.
- Open: produce infinitely many non-unit carries.
- A parallel carry form makes the same boundary explicit: irrationality is
  equivalent to cofinally many non-unit carries
  (`irrational_factorialGapSeries_iff_cofinal_nonunit_carries`,
  `ErdosProblems/Erdos68/FactorialZeroPlateau.lean`). The equivalence supplies
  no cofinal carry producer, so #68 remains open.

**#243 — does rationality force eventual Sylvester recurrence?**

- A divergent natural sequence with upward steps bounded by `B` cannot stay
  coprime to an infinite family of fresh pairwise-coprime moduli —
  `no_boundedRise_of_tailAvoidance`,
  `ErdosProblems/Erdos243/ReciprocalTailRigidity.lean:897`. Checked theorem;
  reusable obstruction; registry: none.
- Given normalised vanishing — supplied for the canonical orbit by Koizumi
  (Integers 26 (2026), A28; cited, prose bridge) — a bounded negative part or
  finite normalised negative mass forces the error to vanish and the
  Sylvester recurrence to begin
  (`ErdosProblems/Erdos243/ReciprocalTailRigidity.lean:2177`,
  `ErdosProblems/Erdos243/ReciprocalTailRigidity.lean:2264`;
  `ErdosProblems/Erdos243/SparseResetRecovery.lean:155`,
  `ErdosProblems/Erdos243/SparseResetRecovery.lean:175`). Checked conditional theorems; the
  note concedes its absorption and descent lemmas as Koizumi prior art.
- A separate no-go rules out an eventually periodic negative-error orbit when
  the phase growth is positive
  (`no_eventuallyPeriodicNegative_orbit`,
  `ErdosProblems/Erdos243/ReciprocalTailRigidity.lean`). It does not cover
  arbitrary unbounded negative behaviour, so the mixed-sign boundary remains.
- The Comparator interface
  `no_cofinallyBoundedNegative_of_normalizedVanishes` makes another conditional
  no-go exact: with `a(n) > 1`, positive `C` and `magnitude`, the coupled
  recurrences `C(n+1) + D(n) = a(n)·C(n)` and
  `D(n+1) = a(n)·D(n)`, a bounded rise `C(n+1) ≤ C(n) + B`, normalized
  vanishing `K·magnitude(n) < C(n)` eventually for every `K`, and a cofinally
  bounded negative part, the hypotheses are inconsistent
  (`ErdosProblems/Erdos243/ReciprocalTailRigidity.lean`). Every dynamical,
  positivity, bounded-rise, and vanishing assumption remains explicit; this
  does not close the original mixed-sign regime.
- Open: the unbounded mixed-sign regime.

**#249 — is `∑ φ(n)/2ⁿ` irrational? (reviewed core)**

- Cited-only source ceiling: Nesterenko's 1996 Corollary 2 gives algebraic
  independence of the Ramanujan values at algebraic `q` with `0 < |q| < 1`.
  At `q = 1/2`, its exact identity
  `P(1/2) = 1 − 24 ∑_{n≥1} σ(n)/2ⁿ` makes the divisor-sum series
  `∑_{n≥1} σ(n)/2ⁿ` transcendental by an elementary affine rewrite
  ([source closure](primary-sources/totient-kernel/nesterenko-1996-source-closure.md)).
  This is a distinct `σ`-coefficient ladder rung, not the Euler-totient
  constant `S`; Nesterenko's analytic proof is not formalised here, and no
  #249 irrationality or novelty claim follows.
- Cited-only q-zeta antecedent: Postelmans and Van Assche prove that
  `1`, `ζ_q(1)`, and `ζ_q(2)` are linearly independent for `q = 1/p` with
  integer `p > 1` (Theorem 1.3). At `q = 1/2`, the release's separately
  formalised identity `L₂(1) = ζ_{1/2}(2) − ζ_{1/2}(1)` therefore gives an
  irrational constant-weight squared-Lambert value
  ([source closure](primary-sources/reciprocal-tail/postelmans-van-assche-2007-source-closure.md)).
  This does not transfer to the Möbius-weighted totient constant `S`, and the
  source supplies no #249 or #257 solution.
- A nearby cited-only sparse criterion of Kaneko, Suzuki, and Tachiya gives
  irrationality of `∑ f(n)/t^{σ(n)}` and `∑ f(n)/t^{φ(n)}` under explicit
  nonnegative infinite-support and growth hypotheses ([source closure](primary-sources/reciprocal-tail/kaneko-suzuki-tachiya-2026-source-closure.md)).
  Here `φ(n)` is a denominator exponent, not the coefficient of `2⁻ⁿ`; this
  result does not transfer to `S`, arbitrary-support #257, or the release's
  gcd-moment identities.
- Unconditional: the dyadic sections `n ↦ φ(2ʲn+r)` of Euler's totient have
  an explicit rational basis, and the level-`e` span has dimension exactly
  `2ᵉ + 1` — `finrank_canonicalTotientKernel_eq`,
  `Erdos249257/TotientMahlerDefect.lean:989`; basis object at
  `Erdos249257/TotientMahlerDefect.lean:1392`. A
  theorem about the coefficient sequence, not about irrationality of `S`;
  it quantifies the known qualitative fact that `φ` is not 2-regular
  (Coons 2008, arXiv:0810.3709, via ζ zero-density — no exact rank appears
  there).
  Claim `dyadic_totient_certificate_interface` (the basis declarations at
  `Erdos249257/TotientMahlerDefect.lean:1265`,
  `Erdos249257/TotientMahlerDefect.lean:1380`,
  `Erdos249257/TotientMahlerDefect.lean:1392` — registry:
  dyadic_totient_certificate_interface).
- The Comparator interfaces make the rank frontier precise: for every
  `e ≥ 1`, `finrank_totientKernelThroughLevelFamily_eq` gives dimension
  `2ᵉ + 1` for the actual finite truncation, while
  `exists_totientDyadicSectionBasis` supplies the explicit odd-core-indexed
  basis. The full-kernel interface
  `not_finiteDimensional_span_fullTotientKernel` proves that the rational span
  is not finite-dimensional. These are coefficient-space facts, not a
  rationality-to-finite-rank bridge or an irrationality proof.
- For every base `k ≥ 2` and level `e ≥ 1`, an all-base extension has an
  explicit canonical spanning family; under its stated linear-independence
  hypothesis, the level-`e` span has dimension `kᵉ + 1`
  (`finrank_allBaseTotientKernelThroughLevelFamily_eq_of_linearIndependent`,
  `Erdos249257/TotientKernelConditional.lean`). The independence is an
  external affine-ordering input not proved here, and this conditional rank
  statement does not prove irrationality of `S`.
- Irrationality of `S` has six checked exact characterisations, from
  tail-difference certificates through the lcm-diagonal form to
  window-separated pairs — `Erdos249257/LcmConeFlatness.lean:316–426`,
  `Erdos249257/PivotAntiReconstruction.lean:1775`; claims
  `certificate_completeness`, `certificate_reduction`.
- Finite: the classical Farey/mediant window at `K = 240` excludes reduced
  denominators through `7.96 × 10³⁴` — improvement over the classical bound:
  zero (claim `denominator_exclusion`) — and diagonal certificates exist at
  every `t ≤ 82`, with the plateau broken at `t = 83` and a proved depth
  floor of `125` there
  (`ErdosProblems/Skip/LadderT67.lean:71264`,
  `ErdosProblems/Skip/LadderT67.lean:71285`,
  `ErdosProblems/Skip/LadderT67.lean:71294`; claim `certified_kill_instances`;
  no certificate at `t = 83` is
  claimed).
- Open: the unbounded certificate supply, which is equivalent to #249 itself;
  a checked splice construction shows no finite inspection can settle it.
- A checked synthetic no-go shows that, for every `t ≥ 3`, a nonzero dyadic
  coboundary can survive every finite integer shift polynomial while retaining
  the period-LCM totient factor ideals, exact cleared-prefix cancellation, and
  uniform state and letter bounds
  (`Erdos249257.TotientTailPeriodKiller.lcm_factorIdeal_finiteRank_shiftAlgebra_not_sufficient`,
  `Erdos249257/LcmFactorIdealPulseObstruction.lean`). This obstructs that
  finite shift-algebra route only: the forcing letters are synthetic rather
  than actual totient differences, nonlinear combinations are not covered,
  and no unbounded certificate supply follows.
- Two additional checked #249 families are directly inspectable: an exact
  [squared-Lambert gcd-moment transfer](../Erdos249257/GcdMomentCalculus.lean)
  at base `1/2` — `tsum_totient_div_mersenne_sq_eq_gcd_moment_series` identifies
  the totient-weighted squared-Mersenne Lambert series with the dyadic series
  of Pillai's gcd-sum function minus `n` — and the Comparator-transported
  `runHeight_defect_fib_sum_lower`
  (`Erdos249257/SternBrocotRunGeometry.lean`). For every finite defect list
  `e`, this theorem bounds the height of its positive Stern–Brocot run word
  from below by `(F_{r+3} + F_{r+1}) · ∑ eᵢ`, where `r` is the number of runs.
  These finite identities/inequalities do not establish analytic denominator
  survival or the unbounded family, so #249 remains open.
- At every positive Stern–Brocot node `(a,b)`,
  `cylinderMass_split` exactly decomposes the closed cylinder mass into the
  node's stop mass and the two child-cylinder masses
  (`Erdos249257/GcdMomentCalculus.lean`). This telescoping recursion and its
  geometric interpretation do not establish denominator survival,
  irrationality, or novelty; the #249 endpoint remains open.
- The same gcd-moment source gives the exact visible-coprime lattice
  normalization `∑ 1/(2ⁿ−1) = 1` over positive coprime pairs
  (`tsum_pos_coprime_inv_mersenne_eq_one`). It supplies the reduced-direction
  mass behind the fair-coin form of the totient constant, but is a rational
  normalization identity, not an irrationality result.

**#251 — is `∑ pₙ/2ⁿ` irrational?**

- Unconditional: `pₙ ≤ 1250(n+1)⁴` by an elementary argument, so the series
  is summable and equals `2 +` the prime-gap dyadic series with no external
  input (`ErdosProblems/Erdos251/PrimeGapDyadicTail.lean:360`,
  `ErdosProblems/Erdos251/PrimeGapDyadicTail.lean:379`,
  `ErdosProblems/Erdos251/PrimeGapDyadicTail.lean:427`); and for any sequence obeying the checked integer-digit dyadic
  tail recurrence, irrationality is exactly equivalent to cofinal
  non-integral tail shifts
  (`irrational_initial_iff_cofinalNonintegralTailShifts`,
  `ErdosProblems/Erdos251/PrimeGapDyadicTail.lean:1572`) — the
  identification of the concrete prime tail with that recurrence is
  paper-level. Checked theorems; registry: none.
- The Comparator-facing boundary is also explicit: `exists_primeGap0_gt`
  proves that consecutive prime gaps are unbounded, while
  `irrational_tsum_primeDyadicTerm_iff_primeGap` proves, for a summable prime
  dyadic term, that its irrationality is equivalent to irrationality of the
  prime-gap dyadic series
  (`ErdosProblems/Erdos251/PrimeGapDyadicTail.lean`). Unbounded coefficients
  and this equivalence alone prove irrationality of neither series.
- A checked countermodel closes the periodicity route: an explicit unbounded,
  non-eventually-periodic digit sequence with rational dyadic sum
  (`carryCoeff_natCast_not_eventually_periodic`,
  `ErdosProblems/Erdos251/PrimeGapDyadicTail.lean:1163`).
- Open: cofinally many adjacent index pairs with small tail shifts and
  differing gaps; each smallness condition constrains a complete infinite
  tail.

**#257 — is `∑_{n∈A} 1/(2ⁿ−1)` irrational for every infinite `A`? (reviewed
core)**

- Native unconditional: for every finite nonempty support `F` of positive
  exponents and every base `b ≥ 2`, the reduced denominator of `∑_{n∈F} 1/(bⁿ−1)` is coprime to `b`
  and has multiplicative order exactly `lcm F` — `finite_period_noncollapse`
  (Comparator interface `finite_period_noncollapse_rat_den_interface`),
  `Erdos249257/CertificateKernel.lean:5091`, with no witness-supply
  hypothesis. Checked theorem; registry: none.
- Formalised known results: the full-support series is irrational in every
  base `b ≥ 2` (Erdős 1948; claim `eb_full_support`), as are pairwise-coprime
  supports with summable reciprocals (Erdős 1968) and eventually periodic
  supports.
- The committed Comparator interface
  `irrational_erdosSupportSeries_pairwise_coprime` makes the pairwise-coprime
  row exact: for every base `b ≥ 2`, infinite support `A`, pairwise
  `Nat.Coprime` elements of `A`, and summable reciprocal indicator
  `Set.indicator A (fun a : ℕ => 1 / a)`, the support series
  `erdosSupportSeries b A` is irrational
  (`Erdos249257/CertificateKernel.lean`; independent statement wrapper in
  `ExternalVerification/Challenge.lean`). At base `2` this is a dedicated
  non-dilation family inside #257, not the universal infinite-support claim.
- Historical source boundary: Chowla's 1947 paper defines the ordinary
  Lambert series `f(x) = ∑ xⁿ/(1−xⁿ)` and a sine-twisted companion, conjectures
  irrationality for both at nonzero rational arguments, but expressly says he
  cannot prove the ordinary `f(x)` case. It proves only the sine-twisted
  `g(1/t)` case for integer `t ≥ 5`, via long zero blocks in sums of two
  squares ([source closure](primary-sources/reciprocal-tail/chowla-1947-source-closure.md)).
  Thus Chowla is historical context for the full-support `x = 1/2` Lambert
  value, not evidence for arbitrary-support #257 or a new release theorem.
- A distinct periodic-support antecedent is due to Luca and Tachiya: for a
  nonzero purely periodic integer coefficient sequence, their Theorem A gives
  irrationality of the associated divisor-convolution Lambert value at every
  integer base with absolute value greater than one; their stronger Theorem 1
  gives linear independence for nonnegative periodic coefficients, including
  full- and odd-support examples ([source closure](primary-sources/reciprocal-tail/luca-tachiya-2014-source-closure.md)).
  The hypotheses are periodic and coefficient-specific, so this is not a
  theorem for arbitrary infinite supports and remains distinct from the
  release's periodic-divisor certificate and mixed-sign boundary.
- The base-2 Mersenne achievement set — all subsums of `∑ 1/(2ⁿ−1)` — is
  compact, perfect, totally disconnected, nowhere dense, and of Lebesgue
  measure one (strict-tail Cantor structure after Kovač–Tao, Remark 4.1; the
  measure clause is proved here; positive measure was asserted informally by
  Kovač on the erdosproblems.com #257 discussion page in August 2025, and no
  published source computes the exact value) — the Comparator theorem
  `volume_mersenneAchievementSet`,
  `Erdos249257/GreedyAchievementSet.lean:996`,
  `Erdos249257/GreedyAchievementSet.lean:1633–1658`; claim
  `greedy_achievement_geometry`. Membership of `1/2` is equivalent to
  infinitely many greedy skips
  (`Erdos249257/GreedyAchievementSet.lean:2527`) and to the absence of
  a fatal half-gap (`Erdos249257/HalfCutLocator.lean:654`); the dyadic
  membership question was posed publicly by Kovač in the same discussion,
  and a positive answer would refute universal #257.

- Historical topological source boundary: Kakeya's 1914 paper proves
  perfectness for subsum sets of absolutely convergent real or complex
  series, gives the real interval enclosure, and states the exact term-versus-
  remaining-tail criterion for filling that interval. It also states
  nowhere density when the criterion fails, but explicitly leaves the
  “infinitely many failures” necessary-and-sufficient refinement unproved
  ([source closure](primary-sources/reciprocal-tail/kakeya-1914-source-closure.md)).
  This is classical subsum-set context only: it does not prove an arithmetic
  statement about Mersenne denominators, rational points, or universal #257.

- The Comparator theorem `seven_le_of_intBand_odd` adds a local two-adic
  band exclusion: for positive odd integers `p`, `D`, and `q` satisfying the
  stated `IntBand` inequalities, `7 ≤ p`
  (`Erdos249257/HalfGreedyTwoThirdsBand.lean`). Thus numerator classes `1`,
  `3`, and `5` are excluded in that band, while `p = 7` is sharp. The theorem
  does not show that an actual half-greedy orbit reaches or avoids the band,
  and does not decide half-membership.
- A newly transported conditional reduction makes the rational-support boundary
  concrete: if the support has a positive seed and its base-2 value is
  `p/(2^c·v)` with `v > 0`, then a positive natural shifted-tail state exists
  with the exact binary recurrence and modular orbit
  (`exists_shifted_odd_tail_nat_states_of_support_fraction`,
  `Erdos249257/RationalSupportCarrySkeleton.lean`). This exposes structure
  under a rationality hypothesis; it does not exclude rational infinite
  supports or settle universal #257.
- For a support restriction `J`, the transported measure dichotomy
  `volume_supportedMersenneAchievementSet_dichotomy`
  (`ErdosProblems/Erdos257/MersenneSubseriesRigidity.lean`) gives exact
  measure `((2 : ℝ≥0∞) ^ F.card)⁻¹` when `J = (↑F)ᶜ` for a finite `F`, or
  measure zero when `Jᶜ` is infinite. This classifies the restricted
  achievement-set measure, not its rational points, so it does not settle
  universal #257.
- A separate unconditional composite-dilation identity now exposes the
  lower-rank defect rather than hiding it in a prime-only adapter:
  `supportCoeff_mul_eq_add_defect`
  (`Erdos249257/CompositeDilationDefect.lean`). For `a ∈ A`, `0 < a`, and
  `0 < x`, it states
  `supportCoeff A (a·x) = supportCoeff A x + (if a ∣ x then 0 else 1) + compositeDilationDefect A a x`.
  The exact defect is not bounded for arbitrary supports and supplies no tail
  selector or irrationality theorem; the separate bouquet budget remains
  conditional on its structural hypotheses.
- Methodological: a formalised squarefree-support no-go theorem is shown to
  be an artefact of normalisation — adjoining `1` to the support shifts the
  value by a rational and flips the divisor-incidence parity, and the
  finite-change principle is itself checked
  (`ErdosProblems/Erdos257/SquarefreeSupportIncidence.lean:94`,
  `ErdosProblems/Erdos257/SquarefreeSupportIncidence.lean:111`,
  `ErdosProblems/Erdos257/SquarefreeSupportIncidence.lean:140`;
  `Erdos249257/CertificateKernel.lean:9467`,
  `Erdos249257/CertificateKernel.lean:9476`). The squarefree value
  itself is settled at power-of-two bases in the literature (Duverney–Tachiya
  2019; cited, not formalised). Registry: none.
- Open: universal #257, and the `1/2` and `1/21` memberships.

**#269 — are reciprocal sums of running lcms irrational?**

- For every pair of distinct primes, both the de-duplicated and the repeated
  running-lcm reciprocal sums are transcendental — a paper argument in the
  problem note; the transcendence engine is Loxton–van der Poorten 1977,
  quoted in the modern Bugeaud–Laurent form (Theorem 1.1); deliberately not a
  Lean theorem, and the note says so. Independently found and not first: the
  same reduction and conclusion were posted by Steve Fan on the
  erdosproblems.com #269 discussion page on 26 June 2026, before the note was
  finalised, with follow-ups there extending it to arbitrary coprime pairs;
  the note acknowledges this.
- Lean-checked: the exact Comparator interface
  `smoothPrefixLcm_eq_threePrimeHeight` states that, for primes `p`, `q`, and
  `r` with `p ≠ q`, `p ≠ r`, `q ≠ r`, and `x ≠ 0`, the running lcm of the
  three-prime smooth prefix is exactly `threePrimeHeight p q r x`
  (`ErdosProblems/Erdos269/ThreePrimeRunningLcm.lean:123`; formalisation of a
  classical identity). The same source also gives the four-letter block
  alphabet `{2, 6, 10, 30}`
  (`ErdosProblems/Erdos269/ThreePrimeRunningLcm.lean:699`), and a rank-two
  kernel obstruction
  (`ErdosProblems/Erdos269/ThreePrimeRunningLcm.lean:479`,
  `ErdosProblems/Erdos269/ThreePrimeRunningLcm.lean:721`): the Comparator
  theorem `kernel_235_minor_eq_neg_one_fifteen` identifies the smallest
  displayed `2,3,5` kernel minor as exactly `-1/15`. This rules out the
  displayed rank-one route only; it does not imply irrationality and does not
  supply the missing rationality-to-irrationality bridge.
- Open: any three-prime case; the rationality-to-carry bridge and the
  cofinal window escape.

**#1041 — short connections inside polynomial lemniscates?**

- Checked: quantitative root retention under constant perturbation
  (`constant_perturbation_roots_in_unitDisk`,
  `ErdosProblems/Erdos1041/NewtonFlowRaySeparation.lean:287`) and arbitrarily
  small translations separating all pairwise ray arguments. More precisely,
  `exists_small_translation_separating_arguments` says that every finite
  injective complex family admits, for each `ε > 0`, a common shift of norm
  `< ε` making every value nonzero and every pair of positive-ray arguments
  distinct (`ErdosProblems/Erdos1041/NewtonFlowRaySeparation.lean:197`). The
  ray-separation exclusion is checked in consumer form only: the
  exponential-decay connection equation is its hypothesis, not a theorem
  (`ErdosProblems/Erdos1041/NewtonFlowRaySeparation.lean:315`). Registry: none.
- The note's main independent contribution is prose, not Lean: a specific
  invalid three-ended local block at an interior Morse saddle in a recent
  manuscript's load-bearing Proposition 12 — identified as a proof gap, not
  a counterexample.
- Open: repair or refute that decomposition; the planar topology and length
  bookkeeping.

- Current-source boundary: the committed [`research_corpus/Erdos1041/FRONTIER.md`](../research_corpus/Erdos1041/FRONTIER.md)
  is the dated route for later source-only research evidence. Read it before
  the generated `STRONGEST_RESULTS.json`: it records certified refutations of
  several proposed strategies, surviving carriers, and exact open gaps while
  leaving the unrestricted endpoint open. These rows are not reviewed claim
  entries, peer review, priority, novelty, or significance findings; the
  frontier itself flags priority/novelty as unchecked for named new rows.

**#1049 — Lambert series at rational bases, beginning with `3/2`?**

- Checked exclusions at `3/2`, each of one named mechanism only: the
  coordinatewise clearing scheme is impossible for all parameters
  (`threeHalves_no_coordinatewiseCorridor`,
  `ErdosProblems/Erdos1049/RationalBaseLambert.lean:155`), scalar content is
  neutral for the local-to-Archimedean balance, and unit endpoints exclude
  both `2` and `3` from a common divisor
  (`ErdosProblems/Erdos1049/ZudilinConeArithmetic.lean:293`). Registry: none.
- The elementary height inequality used by Bundschuh–Väänänen's external
  irrationality criterion at `7/2` is checked
  (`ErdosProblems/Erdos1049/RationalBaseLambert.lean:83`);
  the analytic theorem itself remains external. Formalisation of known
  inputs.
- A separate exact rational-base state recurrence is checked under `r ≠ 0`:
  `rationalBaseClearedTailQ_succ` gives
  `Q(N+1) = r·Q(N) − B·coeff(N+1)·s^(N+1)` for the denominator-cleared tail
  state (`ErdosProblems/Erdos1049/RationalBaseLambert.lean`). The
  `s^(N+1)` forcing term records the denominator-base tax; this recurrence is
  not itself a rationality contradiction, so it yields no #1049 endpoint.
- The Van Assche moving diagonal fails the Amdeberhan–Zeilberger scalar
  recurrence already at `n=0`: its exact residual is
  `-p(p-1)^2(p+1)(p^5+2p^4+2p^3+2p^2+2)`, strictly negative for every real
  `p>1`
  (`ErdosProblems/Erdos1049/QAperyDiagonalNonEquivalence.lean:67,94`). This finite obstruction
  proves only non-transfer of that recurrence; it supplies no general
  recurrence, endpoint, lattice, valuation, denominator, or irrationality
  theorem. Registry: none.
- Open: irrationality at `3/2`; the primitive noncollapsed construction;
  analytic remainder control. The note proves no irrationality result and
  says so.

The semantic corpus marks exactly eight statements `candidate_new_statement` —
the only machine novelty marks in this release, against 5,505 of 6,089
statement nodes still `not_assessed`. They concentrate in the #249/#257 core
(the totient Möbius-numerator normal form, a rank-one overshoot barrier, and
the `1/2` tail-escape and middle-producer family). Reproduce the list from
`docs/semantic_corpus.json` (`statement_nodes[].prior_art_state`); candidate
status is a search outcome recorded for triage, not a novelty claim.

## What is proved

### Settled support families for Problem 257

The universal problem is open, but several infinite supports are settled.
The formal source proves irrationality in every integer base `b≥2` for the
full support, factorials, powers of two, multiples of a fixed positive integer,
residue classes, the odd numbers, eventually periodic supports, and pairwise
coprime supports with summable reciprocals. The relevant declarations include:

- `irrational_erdosSum_full_support`;
- `erdos257_family_factorial_instance` and
  `erdos257_family_two_pow_instance`;
- `irrational_erdosSupportSeries_multiples`,
  `irrational_erdosSupportSeries_residueClass`, and
  `irrational_erdosSupportSeries_odd`;
- `irrational_erdosSupportSeries_eventuallyPeriodic`; and
- `irrational_erdosSupportSeries_pairwise_coprime`.

These declarations are in `Erdos249257/CertificateKernel.lean`. The prime and
prime-power supports are literature results cited by the repository, not
formalised here.

The squarefree support remains open. Its divisor incidence is proved to be
`2^ω(n)-1`, hence odd at every `n≥2`. The certificate engines in this
development begin by selecting an even-incidence block, so they cannot act on
that support at any block position. The checked declarations
`card_squarefreeDivisors`, `squarefreeIncidence_eq`, and
`odd_squarefreeIncidence` are in
`ErdosProblems/Erdos257/SquarefreeSupportIncidence.lean`. This is a limitation
of the named engines, not evidence that the squarefree-support value is
rational or irrational.

### The reduction chain for the one-half test case of Problem 257

The Mersenne achievement set consists of subsums of
`1/(2^n-1)`. If `1/2` belongs to it, its support gives an infinite set with a
rational subseries, which would refute the universal statement in Problem 257.
The repository does not prove this membership.

The checked chain includes:

- `half_mem_mersenneAchievementSet_iff_greedySkippedSupport_infinite` in
  `Erdos249257/GreedyAchievementSet.lean`: membership of `1/2` is equivalent to
  infinitely many skips in its greedy expansion.
- `half_mem_mersenneAchievementSet_iff_unboundedTerminalFalse` in
  `Erdos249257/HalfCylinderHalfMembershipClassification.lean`: the same
  membership is equivalent to terminal false bits beyond every bound.
- `half_mem_iff_unboundedLargestSkipLate` in
  `ErdosProblems/Skip/D2.lean`: membership is equivalent to late largest skips
  beyond every bound.
- `exists_largestSkipLateAt_of_remainder_le_two_pow` in
  `ErdosProblems/Bit/R2.lean`: a row with remainder at most `2^N` produces a
  late largest skip in the explicit interval `[N+1,2N+1]`.
- `half_mem_of_remainderReachesHalfPointCofinally` in
  `ErdosProblems/Bit/R2.lean`: remainders at most `2^s` cofinally are sufficient
  for membership.

The final two bullets are one-way sufficient criteria. They are not
equivalences and are not known to hold cofinally.

The proposed universal `hlow` side condition is false:
`not_hlow_seven_five` in `ErdosProblems/Decl/D4.lean` and
`not_hlow_of_hhigh` in `ErdosProblems/Hlow/H1.lean` give the counterexample
`(s,d) = (7,5)`. Its failure is useful rather than obstructive:
`seamRemainder_lt_two_pow_of_not_hlow` and
`seven_is_a_hit_from_failure` in `ErdosProblems/Hlow/H2.lean` convert that
failure into a hit certificate.

### Exact ranks for dyadic sections of Euler's totient

For `j ≥ 0` and `0 ≤ r < 2^j`, let
`φ_(j,r)(n) = φ(2^j n + r)`. The family consisting of `φ_(0,0)`,
`φ_(1,0)`, and all `φ_(j,r)` with odd `r` is a rational basis for the span of
all dyadic sections. At level `e`, the span has dimension exactly `2^e + 1`.

Lean names and sources:

- `linearIndependent_oddCoreTotientKernelFamily`,
  `span_range_fullTotientKernel_eq_span_range_oddCore`, and
  `totientDyadicSectionBasis` in
  `Erdos249257/TotientMahlerDefect.lean`;
- `finrank_canonicalTotientKernel_eq` in the same file.

These are theorems about the coefficient sequence `φ`. They do not prove that
`∑ φ(n)/2^n` is irrational.

### A finite diagonal certificate band for Problem 249

Let `periodLcm t = lcm(1,…,t)`. The predicate
`certifiedKill h N L` is a finite modular-arithmetic certificate showing that a
specific binary totient-tail difference at shift `h` and position `N` is not an
integer.

`exists_diagonalKill_le_82` proves

```text
for every t ≤ 82, there is an L such that
certifiedKill (periodLcm t) (periodLcm t) L.
```

Lean name and source:

- `exists_diagonalKill_le_82` —
  `ErdosProblems/Skip/LadderT67.lean`

The exact least depths at the new boundary scales are:

| Scale `t` | Least depth `L` | Lean name | File |
|---:|---:|---|---|
| 67 | 100 | `t67_minimal_depth` | `ErdosProblems/Lift/Recon67.lean` |
| 71 | 105 | `t71_minimal_depth` | `ErdosProblems/Lift/CertT67.lean` |
| 73 | 113 | `t73_minimal_depth` | `ErdosProblems/Skip/LadderT67.lean` |
| 79 | 120 | `t79_minimal_depth` | `ErdosProblems/Skip/LadderT67.lean` |
| 81 | 120 | `t81_minimal_depth` | `ErdosProblems/Skip/LadderT67.lean` |

The same file proves

```text
periodLcm 79 = 32433859254793982911622772305630400,
```

a 35-digit modulus, as `periodLcm_79_value`.

The source-backed
[`checked_diagonal_depth_roster.json`](measurements/checked_diagonal_depth_roster.json)
covers all 33 distinct `periodLcm` scales whose plateaux fill the positive band
`t≤82`. Every recorded working depth lies `0…4` above the arithmetic
admissibility floor (median `1`, mean `40/33`). Only the five boundary scales
`t=67,71,73,79,81` have separate theorems proving their recorded depths least;
for the other 28 scales, the excess is only an upper bound on the least-depth
excess. Reproduce the roster with:

```sh
python3 scripts/build_checked_diagonal_depth_roster.py --check
```

This is a bounded result. The reduction for Problem 249 requires certificates
at arbitrarily large scales. The theorem says nothing at `t = 83`.

### Finite off-diagonal certificates

The historical audit selects 125 verified log rows at positions not constrained
to equal `periodLcm t`. Two pairs of rows repeat the same `(h,N,L)` triple, so
the roster contains 123 distinct certificates matched to 123 public Lean
theorems across 122 files. The largest position in that audited set is:

```text
freeKill_64OneHundredFifteenDI :
  certifiedKill 1 135960691671824579163806583999 101
```

Source:
`ErdosProblems/FreePosition/FreeKill64OneHundredFifteenDI.lean`.

The generated
[`off_diagonal_certificate_roster.json`](measurements/off_diagonal_certificate_roster.json)
retains all selected source rows and their hashes, identifies both duplicate
groups, and binds each distinct triple to its exact theorem, line, and source
hash. Reproduce it with:

```sh
python3 scripts/build_off_diagonal_certificate_roster.py --check
```

The source log also contains 54 later verified certificate triples above the
historical position cutoff. The roster exposes that excluded census without
silently changing the historical result.

The relevant sufficient theorem for Problem 249 is
`irrational_totient_series_of_multiple_window_kill_supply` in
`Erdos249257/CertificateKernel.lean`. Its hypothesis requires, for every
positive base shift and every lower bound on the position, a later certificate
at some positive multiple of that shift. A finite list of 123 instances does
not establish that quantified supply.

### Direct Farey comparison

The denominator exclusion is exactly the standard Farey/mediant bound for the
two committed finite windows. The arithmetic below was recomputed from

```text
V_K = (∑_{r=1}^K φ(r+1) 2^(K-r)) mod 2^K
```

and from the explicit neighbouring fractions in
`Erdos249257/GapFareyBound.lean`.

| `K` | Interval width | Delta |
|---:|---:|---:|
| 120 | `123/2^120` | `0` |
| 240 | `243/2^240` | `0` |

The exact denominators of each window are:

```text
K = 120
  Farey neighbour denominators b, d   41326538792622579
                                      207345787569745331
  b+d-1                               248672326362367909
  formal exclusion bound              248672326362367909
  first failing denominator           248672326362367910

K = 240
  Farey neighbour denominators b, d   66013429300517684370587633721421187
                                      13626217346183690952768141154409867
  b+d-1                               79639646646701375323355774875831053
  formal exclusion bound              79639646646701375323355774875831053
  first failing denominator           79639646646701375323355774875831054
```

For each window, the recomputation gives determinant `1` for the two neighbours,
verifies both interval brackets, verifies the displayed bound, and verifies
failure at the next denominator. The corresponding proved declarations are
`farey_gap`, `gap_check_window_1_120_le_248672326362367909`,
`gap_check_window_1_120_first_failure`,
`gap_check_window_1_240_le_79639646646701375323355774875831053`, and
`gap_check_window_1_240_first_failure`.

The division of credit is exact: Farey supplies the bound directly;
formalisation supplies a checked arithmetic instance and proves it is sharp
for that window. Neither finite window proves that the exclusion bounds are
unbounded, so neither proves Erdős #249.

The magnitude is also a tunable window output, not an invariant measure of
progress. `scripts/check_farey_denominator_scaling.py` independently reproduces
the two formalised constants and cross-checks the producer by brute force on
six small windows. On this run, choosing `K=16000` produced a 2,406-digit bound
in `0.08` seconds for the scaling row (`0.18` seconds for the complete script).
Every fixed `K` still gives only a finite exclusion, and increasing `K` does
not supply the unbounded theorem required by #249.

### Scoped no-go theorems

These theorems rule out particular proof mechanisms. They do not rule out other
arguments.

- `no_lift_from_lower_totient_data`, `ErdosProblems/Lift/AngleA5.lean` — no
  universal lift of the displayed form can follow only from the stated lower
  totient data, pointwise bound, and a lower certificate.
- `no_window_local_lift`, `ErdosProblems/Lift/InduceLaw.lean` — for prime
  multipliers `p ≥ 3`, agreement on the lower diagonal window does not force
  any certificate in the lifted window.
- `exists_certifiedKill_antitone`, `ErdosProblems/Lift/AngleA4.lean` — a
  certificate at a larger position gives one at a smaller position; the
  implication runs opposite to a forward lift.
- `consecutiveFail_iff`, `ErdosProblems/Half/FreeWalk2.lean` — under its
  explicit depth inequality, a run of `K` failures at depth `L` is equivalent
  to failure at depth `L+K` at the base position.
- `no_absolute_bound_on_consecutive_failures`,
  `ErdosProblems/Half/FreeWalk1.lean` — the abstract admissible-run model
  permits arbitrarily long failure runs under its stated budget.
- `exists_persistent_surplus_model`, `ErdosProblems/Rem/C1.lean` — the listed
  row recurrence and ceiling inequalities admit a sequence that stays above the
  target forever.
- `rowLaw_blind_at_16`, `ErdosProblems/Rem/C1.lean` — at one concrete row,
  every listed row-level trigger is silent although the next row has a late
  skip.
- `IntervalCeiling.four_pow_le`, `ErdosProblems/Three/T1.lean` — every ceiling
  satisfying the stated branch-blind rank-recursion obligations must grow on
  the `4^s` scale.
- `two_pow_mul_y`, `ErdosProblems/Three/T2.lean` — the normalised state used in
  the doubling route is dyadic at every finite row.
- `exists_persistent_odd_surplus_model`, `ErdosProblems/Three/T3.lean` — adding
  parity to the listed row-level constraints still admits a persistent surplus
  model.
- `PairCeiling.terminal_ge_of_splits`, `ErdosProblems/Decl/D1.lean` — in the
  stated two-sided abstraction, a failed branch prediction forces the terminal
  upper bound above the target scale.

### Other standalone exact obstructions

These five registry claims are not restatements of either endpoint. Each has a
separate limitation, and none settles an Erdős problem.

- `totient_carry_kernel_anti_compression` — if `S` were rational, one
  rationality-supplied tempered integral carry would have canonical
  carry-section span dimension at least `2^e-1` for every `e`.
  Boundary: no finite-rank upper bound for such carries is known, so this does
  not contradict rationality.
- `primitive_coordinate_index_obstruction` — clearing `(φ*μ)(n)/n` through
  level `N` forces a two-tier primorial divisor; no fixed positive index clears
  every level.
  Boundary: finite Euler-coordinate obstruction, not an irrationality
  criterion.
- `lcm_factor_ideal_anchor_pulse_no_go` — for every `t≥3`, a synthetic survivor
  satisfies the factor-ideal and whole-ray-anchor constraints and survives
  every finite integer shift polynomial.
  Boundary: its letters need not be actual totient differences; nonlinear
  fresh-divisor arguments remain possible.
- `reciprocal_mass_bound` — a rational support value with odd denominator part
  `v` forces reciprocal mass at least `1/ord_v(2)`, or divergence; a
  dyadic-rational infinite support forces divergence or mass greater than one.
  Boundary: does not exclude every rational value.
- `unbounded_carry_states` — every infinite support with rational series value
  has an unbounded positive carry state.
  Boundary: rules out finite-state interpretations, not rationality itself.

Retrieve their declarations and current source coordinates with
`python3 scripts/query_corpus.py --claim <registry-id>`.

### Demand ledger

A demand is an unproved hypothesis extracted from a conditional theorem and
stored as a named Lean proposition. `ErdosProblems/DemandLedger/Basic.lean`
contains 101 named closed propositions; 23 are labelled substantive and the
rest are side conditions. The current prose frontier contains 52 entries.

The extraction snapshot in the audit log records 144 proved implication edges
among the 23 substantive demands, producing seven equivalence classes.
Seventeen substantive demands collapse to restatements of an open target rather
than smaller subproblems. For example:

- `G103_iff_erdos249` in
  `ErdosProblems/DemandLedger/edges/Discharge3_G103.lean` proves that the
  general lcm-window supply `G103` is equivalent to Problem 249 itself.
- `G103_iff_G097` in the same file identifies two supply formulations.
- `e_G083_G084` in `edges/ClusterE.lean` records one implication in the
  Problem 257 chain.

The ledger classifies obligations. It does not discharge an obligation merely
by naming it or proving it equivalent to the target.

## What is measured, not proved

Only measurements with an explicit tested range and explicit exception set are
listed here. Counts without preserved sample identities are not promoted to
release results.

| Measurement | Exact range | Exact failures or mismatches | Status |
|---|---|---|---|
| `Recon257.seamExcess s = 2` | `s = 5,…,102` (two overlapping scans, `5…64` and `58…102`) | No occurrence. | MEASURED. This makes the audited uses at `s=D+1`, `D≥60`, unobserved. |
| Three-row `hcof` on the seven audited survivor values | `D = {101,122,164,314,545,629,1112}` | Fails at all seven values. | MEASURED; every audited case satisfying `hcof` already died by depth 3. |
| Residual invariant | `s = 6,…,3000`, `d = 2,…,s-1` | Exactly `(s,d)=(13,7)`; residual `524419`, bound `524288`. | The exception is also PROVED by `Three/T1.not_residualInvariant`. |
| `hlow` and `hhigh` at late pairs | all late pairs with `s = 5,…,600` | `hlow` fails exactly at `(7,5)`; `hhigh` fails exactly at `(5,4)`. | The `hlow` exception is PROVED in `Decl/D4` and `Hlow/H1`. |
| Remainder-hit/greedy-support correspondence | `s = 5,…,900` | Zero mismatches. | MEASURED. It does not prove infinitely many hits. |
| `UnboundedLargestSkipLate` row event | `s = 5,…,1500` | Fails exactly at `s = 5,11,12,13`. | MEASURED. A finite interval does not prove eventual or unbounded behaviour. |
| Residual invariant on adjacent control rows | every rank of rows `s=12` and `s=14` | No failures. | MEASURED anti-vacuity check for the isolated `(13,7)` counterexample. |
| Diophantine height at one scale | `d=1000` | Denominator bit length `253815`; comparison value `d²/4=250000`. | MEASURED single-scale size check, not an asymptotic theorem. |
| Relative-margin scan | `d = 2,…,2000` | Record low `1.13×10^-4` at `d=1136`; no danger-zone instance. | MEASURED. It does not establish a positive lower bound. |

For the residual invariant, the maximum ratio away from the exception was
`0.9999807` at `(606,602)`.

The rows above are carried from a dated audit log whose raw run logs and
executable scan owners are not preserved in this release. Their stated finite
domains and exception sets are therefore historical measurement records, not
independently reproducible artifacts. A reported late-bit scan of about 14,000
ranks over `s=14,…,400` is omitted from the table because neither its exact
sample count nor its sample identities were preserved.

The audit also records a selection-biased certificate sample: at depth excess
`c=2`, 15 of 154 samples failed; at `c=3`, 601 of 5987 failed. The sample
identities are not preserved in the log, so these counts are not independently
reconstructible from the release and are not evidence for an equidistribution
law.

The remaining two measurements are source-backed and reproducible from this
release.

### Exact endpoint-certificate probe

Exact range: all `960` pairs `1≤N≤120`, `1≤h≤8`, searching `1≤L≤400`;
additional `h=1` probes at `N=200,500,1000,2000,5000`; exact LCM-diagonal pairs
`(N,h)=(lcm(1,…,t),lcm(1,…,t))` for `1≤t≤16`.

Exact failures or mismatches: no failures. Relative to the least arithmetically
admissible depth `L₀=min{L≥1:2ᴸ>2(N+h+L+2)}`, the rectangle's first
certificates have excess `0…11` (median `1`, mean `727/480`); the 16 indexed
diagonal rows have excess `0…4` (median `1`, mean `5/4`), and the 11 distinct
diagonal scales have mean `14/11`.

Status: MEASURED by exact integer arithmetic. Raw depth must grow with scale
because the certificate interval is empty below `L₀`; the finite excess
distributions prove no asymptotic law, equidistribution, bounded-excess
theorem, or cofinal supply. Reproduce with:

```sh
python3 scripts/probe_certificate_supply.py --check
```

### Source-backed checked diagonal depths

Exact range: all 33 distinct `periodLcm` scales covering positive `t≤82`.

Exact failures or mismatches: every checked working depth has excess `0…4` over
`L₀` (median `1`, mean `40/33`). Five rows have proved least depths, with exact
excess `0…3`; the other 28 values are upper bounds on least-depth excess.

Status: FINITE SOURCE EXTRACTION from explicit Lean theorem signatures. It
establishes no bounded-excess law at untested scales and no cofinal supply.
Reproduce with:

```sh
python3 scripts/build_checked_diagonal_depth_roster.py --check
```

## What was retracted

The detailed file-by-file record is in
[`TRUTH_AUDIT.md`](TRUTH_AUDIT.md). The main corrections are:

- `Lift/AngleB2.lean` no longer says that the survivor set is empty. Its theorem
  is conditional on a false `hcof` instance at each surviving class and on an
  unobserved `seamExcess = 2` hypothesis.
- `Lift/AngleB3.lean` no longer presents
  `ratchetOrbit_above_universal_barrier` as a live universal barrier. Its
  intended hypothesis fails at the initial row, and the proved nonrecurrence
  result covers only offsets `b ≥ Q+2`, not offsets `1,…,9`. The file now uses
  an actual Lean bridge to `Recon257`.
- `Skip/D1.lean` and `Skip/Wire1-3.lean` no longer claim to exclude residue
  classes. Their existential threshold exceeds every case admitted by their
  own hypotheses, and the same unobserved seam-excess premise remains.
- `Rem/C6.lean` no longer says the residual invariant is empirically true on
  `s = 6,…,3000`. It is false at `(13,7)`.
- `Rem/C3.lean` now distinguishes the branch it proved from the branch it only
  measured at the time, and points to `Three/T2.lean`, where the latter branch
  was subsequently proved.
- `Bit/R2.lean` labels `badRun_pins_remainder` as a conditional statement with
  no observed instance: it needs at least 12 consecutive bad rows, while the
  measured maximum was 3.
- `Three/T4.lean` and `Bit/Corr1.lean` no longer call `hlow` open. It is false
  at `(7,5)`, and that failure supplies a hit certificate.

No theorem was weakened or removed to make these corrections. The claims were
narrowed to the theorem types and the recorded counterexamples.

## What is open

### Exact questions for a human expert

The command

```sh
python3 scripts/query_semantic.py expert-questions
```

returns a bounded index of the validated handoffs. Open one complete packet
with, for example,

```sh
python3 scripts/query_semantic.py expert-questions XQ249-pivot-decorrelation
```

Each requested input is `OPEN`; the consumer named under each question is a
checked theorem. The classification matters: the first question is the endpoint
in exact normal form, the next two are sufficient analytic producers for #249,
and the last two would produce a counterexample to universal #257 rather than
prove its positive statement.

No checked strictly weaker handoff currently implies the universal positive
statement of #257 for every infinite support. Named support families,
half-value analysis, reciprocal-mass bounds, and sublogarithmic zero-window
constraints are partial; treating any one as a universal proof route would
overstate what its checked consumer establishes.

The packet does not make an expert start cold. Every ask also carries a
low-confidence current hypothesis, enumerated alternatives, current evidence,
and the observation or theorem that would distinguish them; both are recorded
with each question below.

#### `XQ249-lcm-diagonal-supply` — diagonal supply

Exact `OPEN` input: for every `t₀`, find `t ≥ t₀` and `L` with a diagonal
certificate at `(lcm(1,…,t), lcm(1,…,t))`.

Payoff and boundary: equivalent to #249. A proof closes #249; until then this
is a restatement, not intermediate progress.

Current working guess: certificates occur beyond every scale, equivalently #249
is true.

Evidence that would change the guess: a rational representation or an
eventual-failure theorem decides the opposite branch. The exact rectangle has
first-depth excess `0…11`; across all 33 distinct checked diagonal scales
covering `t≤82`, working-depth excess is `0…4` (median `1`, mean `40/33`). Only
five diagonal depths are proved least, and finite low upper bounds neither
prove bounded excess nor decide the cofinal quantifier.

`PROVED` consumer:

```text
irrational_totient_series_iff_lcm_diagonal_certificate_supply
```

#### `XQ249-pivot-decorrelation` — pivot decorrelation

Exact `OPEN` input: cofinally supply the exact four pivot budgets: centred real
correlation `≤14X/25`, supplier mean and bad-supplier norms `≤X/100` each, and
non-supplier norm `≤8X/25`, with overlap `h≤L-s` and room
`16(2X+h+L+2)≤2^L`.

Payoff and boundary: sufficient for #249. The missing input is a
prime-distribution or residual-decorrelation estimate, not another certificate
reformulation.

Current working guess: for every shift, fixed `s,η` permit cofinally many
blocks satisfying overlap, room, and all four budgets; the centred real term is
likely the hard budget.

Evidence that would change the guess: exact failure requires one shift for
which every `s,η` eventually loses at least one clause. Infinitely many bad
blocks do not suffice. An exact four-budget producer proves #249.

`PROVED` consumer:

```text
irrational_totient_series_of_pivotResidualDecorrelation
```

#### `XQ249-adjacent-phase-separation` — adjacent phases

Exact `OPEN` input: for every `h>0` and `X₀`, find `X≥max(X₀,1)`, a depth `L`,
and adjacent `N,N+1∈[X,2X)` such that `16(2X+h+L+2)≤2^L` and their
first-harmonic phases have squared chordal separation at least `19/25`.

Payoff and boundary: sufficient for #249. Finite scans or average separation do
not meet the cofinal quantifiers.

Current working guess: qualifying adjacent separation occurs cofinally for
every shift.

Evidence that would change the guess: one shift and a cutoff beyond which no
admissible block, depth and adjacent pair reaches `19/25` kill this route;
infinitely many bad blocks alone do not. A cofinal adjacent-discrepancy theorem
at that threshold proves #249.

`PROVED` consumer:

```text
irrational_totient_series_of_adjacentPhaseSeparation
```

#### `XQ257-second-channel-separation` — second channel

Exact `OPEN` input: prove `HalfSecondChannelSeparatedRat n` for every `n≥7`,
i.e. that the exact rational second-channel phase stays at least
`1/6+(37/56)2^{-n}` from `1/3`; Lean checks `1,…,6`, and an independent exact
probe finds no failure through `n=1000`.

Payoff and boundary: proves `1/2` attainable. The finite-support exclusion then
forces the witness to be infinite, giving a rational counterexample to
universal #257. The finite probe does not move the quantifier; failure of this
route would not prove universal #257.

Current working guess: the separation continues for all `n≥7`; confidence
remains low despite an empty exact failure set on `1≤n≤1000`.

Evidence that would change the guess: the least measured margin on the open
range is `1033253069/8193024` at `n=7`, but `n=1001` onward is unmeasured. One
failed level closes only this socket; a global reachability invariant or
uniform sign estimate proves membership and, with finite-support exclusion, a
counterexample.

`PROVED` consumers:

```text
half_mem_mersenneAchievementSet_of_secondChannelSeparationRat_from_seven
positiveMersenneSupportValue_coe_finset_ne_half
positiveMersenneSupportValue_eq_erdosSupportSeries
```

The second-channel measurement is source-bound and reproducible:

```sh
python3 scripts/probe_second_channel_separation.py --check
```

It re-evaluates the rational greedy recurrence and the complete failure set
for `1≤n≤1000` from the definitions in
`Erdos249257/GreedyAchievementSet.lean`. The generated artifact is
[`docs/measurements/second_channel_separation_probe.json`](measurements/second_channel_separation_probe.json).
Its status is `MEASURED`, not `PROVED`; in particular, the empty finite failure
set does not establish the all-`n` hypothesis consumed by the Lean theorem.

#### `XQ257-middle-producer-tail-escape` — middle producer

Exact `OPEN` input: at every actual middle transition from rank `13`, write `C`
for the checked producer carry and `Θ` for its nonnegative coefficient tail.
Prove `C=-3` or `(1≤C and Θ<C)`.

Payoff and boundary: also proves `1/2` attainable; at the putative last-false
row the checked `-3` theorem removes the first disjunct, and the
finite-support exclusion then forces an infinite witness. The socket must
exclude every actual `C≤0`, `C≠-3`, and control `Θ<C` for every positive cell.

Current working guess: every actual middle row lies in the `C=-3` branch or has
`1≤C` and `Θ<C`.

Evidence that would change the guess: one actual nonpositive cell other than
`-3`, or one positive cell with `Θ≥C`, refutes this socket. A proof of the
displayed disjunction at every actual row proves membership; the final `-2`
sieve alone does not.

`PROVED` consumers:

```text
half_mem_mersenneAchievementSet_of_middleProducerTailEscapeExceptNegThree
positiveMersenneSupportValue_coe_finset_ne_half
positiveMersenneSupportValue_eq_erdosSupportSeries
```

### Exact systems-review handoff

The repository cannot certify its own human legibility. It therefore exposes a
second `OPEN` question: can an independent reader, starting from a fresh clone,
recover the calibrated verdict in at most ten minutes? The request is exact,
including the response schema, its consumer, payoff, and boundary:

The low-confidence working guess is that a reader will recover both open
boundaries and the zero Farey delta, but may still underweight the concrete
non-restatement results. The protocol distinguishes that failure from the
opposite error—mistaking finite or conditional results for a near-solution.

```sh
python3 scripts/query_expert_handoffs.py --domain systems
python3 scripts/query_expert_handoffs.py --question XQ249-pivot-decorrelation
python3 scripts/query_expert_handoffs.py --template XQSYS-ten-minute-hostile-reader
python3 scripts/query_expert_handoffs.py --response RESPONSE.json
python3 scripts/query_expert_handoffs.py --review-template XQSYS-ten-minute-hostile-reader
python3 scripts/query_expert_handoffs.py --review RESPONSE.json REVIEW.json
```

A structurally accepted response from an identified independent reader returns
an explicit rubric for its result summaries, evidence paths and verdict. A
second identified evaluator binds a final review to the response digest. The
validator cannot authenticate either person or the elapsed time, and does not
pretend to judge free prose by itself. Neither receipt validates the mathematics
or establishes priority or novelty. The same query without a domain filter
returns this systems question beside the five theorem-connected mathematical
questions; respondent-facing output omits the evaluator's scalar answer key.

### Erdős Problem 249

The irrationality of

```text
∑_{n≥1} φ(n)/2^n
```

is open. The finite band through `t=82` and the 123 distinct certificates in
the bounded historical off-diagonal roster do not provide the quantified,
unbounded certificate supply required by the reduction.

### Erdős Problem 257

The statement that

```text
∑_{n∈A} 1/(2^n-1)
```

is irrational for every infinite `A` is open. In particular, membership of
`1/2` in the Mersenne achievement set is not proved.

At level `d`, the rational compared with the remaining tail changes with `d`.
A naive common-denominator construction gives an upper height bound of the
form `2^O(d^2)`, but the repository proves neither a matching lower bound nor a
`Theta(d^2)` law for the reduced denominator along the actual greedy support.
The displayed separation boundary has an explicit correction proportional to
`2^{-d}`. No registered theorem controls the required sign uniformly at this
moving boundary, and there is no fixed rational approximation target to which
a fixed-number theorem applies directly.

Irrationality alone is insufficient because the open branch asks for the sign
of a nonzero tail difference, not merely for non-equality.

## How to verify

Install the pinned Lean toolchain and Mathlib cache, then run:

```sh
lake exe cache get
lake build
python3 scripts/build_declaration_atlas.py --check
python3 scripts/build_semantic_corpus.py --check
python3 scripts/check_semantic_corpus.py
python3 scripts/build_corpus_descriptor.py --check
python3 scripts/test_declaration_head_contract.py
python3 scripts/test_projection_checkout_independence.py
python3 scripts/check_cold_clone_comprehension.py
python3 scripts/check_release.py
```

Focused checks for the headline Lean files are:

```sh
# These dependency chains are not imported by the root build. Install their
# `.olean` files before running the direct checks downstream.
lake build ErdosProblems.Lift.Recon67 ErdosProblems.Lift.CertT67
lake build ErdosProblems.Three.T1 ErdosProblems.Decl.D4
lake env lean ErdosProblems/Skip/LadderT67.lean
lake env lean ErdosProblems/FreePosition/FreeKill64OneHundredFifteenDI.lean
lake env lean ErdosProblems/Three/T1.lean
lake env lean ErdosProblems/Decl/D4.lean
lake env lean ErdosProblems/Hlow/H2.lean
```

The `lake build` step emits build progress and kernel-dependency reports. An exit status of
zero and empty output is expected from each subsequent `lake env lean` check.

### Isolated-tree reproduction record

Measured on 2026-07-26 on an Apple M4 host (`arm64`, 10 logical CPUs, 24 GiB
memory). The source was copied without version-control metadata or a prior
`.lake` directory:

```sh
# Run from anywhere inside a clone of this repository.
repo_root=$(git rev-parse --show-toplevel)
repro_dir=$(mktemp -d)
rsync -a --exclude '.git/' --exclude '.lake/' "$repo_root"/ "$repro_dir"/
cd "$repro_dir"
lake exe cache get
lake build
```

The cache fetch exited zero in `109.73` seconds. The root build completed all
`8,914` jobs and exited zero:

```text
real 4194.17
user 15939.05
sys  4778.79
```

The build printed ordinary dependency reports and linter warnings. It did not
install every object needed by the focused expansion files. The following
dependency builds supplied the two missing chains:

| Command | Exit | Wall time |
|---|---:|---:|
| `lake build ErdosProblems.Lift.Recon67 ErdosProblems.Lift.CertT67` | 0 | `195.37 s` |
| `lake build ErdosProblems.Three.T1 ErdosProblems.Decl.D4` | 0 | `126.47 s` |

With those objects installed, every direct focused check exited zero with empty
Lean output. The directories and files below are relative to `ErdosProblems/`.

| Directory | File | Wall time |
|---|---|---:|
| `Lift` | `Recon67.lean` | `69.24 s` |
| `Lift` | `CertT67.lean` | `98.81 s` |
| `Skip` | `LadderT67.lean` | `682.69 s` |
| `FreePosition` | `FreeKill64OneHundredFifteenDI.lean` | `53.05 s` |
| `Three` | `T1.lean` | `8.83 s` |
| `Decl` | `D4.lean` | `6.76 s` |
| `Hlow` | `H2.lean` | `5.27 s` |

Two commands did not reproduce in the original advertised order. Immediately
after the root build, checking `LadderT67.lean` failed in `1.74` seconds because
the `Recon67` object was absent. Directly checking `Recon67.lean` and
`CertT67.lean` did not install their objects, so a second `LadderT67.lean`
attempt failed in `2.02` seconds for the same reason. The first direct
`T1.lean` attempt likewise failed in `1.93` seconds because the `Rem.C6` object
was absent. The focused recipe above now uses `lake build` for both dependency
chains before the direct checks.

The repository also contains a source-bound receipt runner:

```sh
python3 scripts/run_source_bound_reproduction.py plan
python3 scripts/test_source_bound_reproduction.py
```

It hashes the declared source tree, executes the complete command plan in an
isolated copy, records command vectors, UTC bounds, exit codes, wall/user/system
times, output digests and bounded tails, and validates the resulting receipt
against the source identity. The release-check row is explicitly marked as
requiring version-control metadata; a default run refuses that capability
unless it is separately authorised. No complete receipt is shipped at
`docs/measurements/source_bound_reproduction_receipt.json` yet. Accordingly,
the timings above remain a dated manual record rather than a
machine-revalidated receipt for the present source tree.
