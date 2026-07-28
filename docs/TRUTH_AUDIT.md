# Truth audit

This report records corrections made before public release.  It is written for
a reader who has not seen the development history.

The Lean declarations were not weakened or removed.  The corrections are to
module descriptions, section headings, and theorem documentation that said
more than the checked declarations establish.  Each edited Lean file was
checked separately with:

```text
lake env lean <file>
```

For every edited Lean file, the command exited successfully and produced no
output.

The audit scope was all 122 Lean files in the nine requested programme
families: `DemandLedger` (14), `Lift` (28), `Skip` (20), `Half` (14), `Bit`
(12), `Rem` (12), `Three` (8), `Decl` (8), and `Hlow` (6).  The tables below
list every claim in that scope that required correction; files absent from the
tables had no overstated public claim identified by the audit.

The central distinction used below is:

- **PROVED** means the cited Lean declaration has the stated conclusion.
- **MEASURED** means a finite computation produced the stated data.  It is not
  an assertion about all rows or all scales.
- **CONDITIONAL** means the Lean implication is proved, but one or more
  hypotheses have no known instance or are known to fail in the intended use.

## Census populations are not interchangeable

The corpus-shape queries and the demand lattice answer different questions.
At this checkpoint the 705 semantic statement nodes yield three disjoint
diagnostic views: 196 mechanically nonrecurring candidates (59 for #249, 121
for #257, and 16 shared), 25 bare open-problem equivalences, and 70
classical/prior-art formalisations. The first count is not a novelty claim: 184 candidates have no
completed prior-art assessment, and the reviewed frontier shortlist contains
11 nodes, five for #249 and six for #257.

The `17/23` count is a narrower kernel-checked audit. It starts from 259
conditional declarations, extracts 101 distinct closed hypothesis Props, and
classifies 23 as substantial; 17 of those 23 are endpoint-equivalent. The
prose-level `open-antecedents` query currently lists 52 entries, 10 marked
endpoint-equivalent. Repetition, refinement, and side-condition filtering
explain why those populations have different denominators. The `17/23` result
diagnoses conditional routes; it is not a summary of the repository's
independent theorem content.

## Retractions affecting the claimed mathematical status

| File | Claim before correction | Corrected claim | Evidence forcing the correction |
|---|---|---|---|
| `ErdosProblems/Lift/AngleB2.lean` | The survivor set is empty; no residue classes remain. | The displayed contradiction is conditional on `hcof` and on `Recon257.seamExcess (D+1) = 2`.  It closes no additional class in the audited range. | `Lift/verify/Check7.lean`; `hcof` fails at `D = 101, 122, 164, 314, 545, 629, 1112`; every audited `hcof` case already dies by depth `3`; direct evaluation finds no `s ∈ [5,102]` with `seamExcess s = 2`. |
| `ErdosProblems/Lift/AngleB3.lean` | The concrete ratchet crosses a universal barrier, so periodic orbits are excluded. | `ratchetOrbit_above_universal_barrier` has an impossible hypothesis at `s = 0`.  The recurrence no-go applies only for `b ≥ Q+2`; it says nothing about the live finite region `1,…,9`.  The concrete connection is now made through an import and explicit bridges. | `Lift/verify/Check8.lean::barrier_theorem_is_vacuous`; the hypothesis would require `P 0 + 4 ≤ 0`. |
| `ErdosProblems/Skip/D1.lean` | `exists_bound_allRight_landingExcess_two_impossible` excludes the surviving classes. | The existential bound exceeds every `D` admitted by the same hypotheses, so it excludes zero classes.  Its landing premise is also unobserved. | `Skip/verify/V1.lean`; the bound comparison is proved from the theorem’s hypotheses. |
| `ErdosProblems/Skip/Wire1.lean` | The all-right branch is resolved. | The result is a conditional equivalence.  The all-right hypothesis is the open endpoint condition, and the landing condition has no observed instance. | `Skip/verify/V7.lean`; `allRight_branch_resolved_iff_false`; the finite landing scan. |
| `ErdosProblems/Skip/Wire2.lean` | Scale arguments exclude the remaining all-right classes. | The exclusions are conditional scale inequalities.  They do not produce the global all-right hypothesis or a live landing instance. | The theorem signatures in `Wire2.lean` and the corresponding finite witnesses. |
| `ErdosProblems/Skip/Wire3.lean` | Cofactor-floor, modulo-`3`, and residue arguments close the frozen right tail. | Each displayed branch retains the all-right and landing hypotheses; in the intended landing configuration the branches are vacuous. | `Skip/verify/V9.lean::cofFloor_branch_vacuous`, `mod_three_branch_vacuous`, and `residue_branch_vacuous`. |
| `ErdosProblems/Rem/C6.lean` | The residual invariant is empirically true on `s ∈ [6,3000]`, with maximum ratio `0.99989`. | The invariant is false inside that range.  The file now cites the counterexample and treats its unconditional remainder bound separately. | `Three/T1.not_residualInvariant`: at `(s,d) = (13,7)`, the residual is `524419 > 2^19 = 524288`. |
| `ErdosProblems/Rem/C3.lean` | One doubling branch is exact and the other is only measured; the resulting conjugacy is exact enough to settle the tail. | The middle and upper branch formulas were later proved in `Three/T2`, with explicit perturbations.  The global shadowing conclusions remain conditional on open hypotheses, and the finite pin-gap measurement does not prove a uniform bound. | `Three/T2.middleBranch_remainder_succ_eq`, `upperBranch_remainder_succ_eq`; `Three/verify/T2.lean`; `Rem/verify/C3.lean`. |
| `ErdosProblems/Bit/R2.lean` | `badRun_pins_remainder` provides a live pinning mechanism for long bad runs. | The theorem is a valid conditional implication, but its antecedent requires at least `12` consecutive bad rows.  The measured bad set is `{5,11,12,13}`, with maximum run length `3`; no instance is observed. | `Bit/verify/B5.lean`; the explicit bad-row computation. |
| `ErdosProblems/Three/T4.lean` | `hlow` is an open side condition, and the long bad-run contrapositive describes a live obstruction. | Universal `hlow` is false.  Its failure is a hit certificate, not an obstruction.  The long bad-run antecedent has no instance on rows `4,…,300`. | `DeclD4.Seven.not_hlow_seven_five`; `HlowH1.not_hlow_of_hhigh`; `HlowH2.seamRemainder_lt_two_pow_of_not_hlow`; `Three/verify/T4.lean`. |
| `ErdosProblems/Bit/Corr1.lean` | The bit correspondence applies subject only to an open technical condition. | The correspondence is conditional on `hlow`, which is false at `(7,5)`.  The file now presents its concrete rows as local witnesses, not a universal route. | `Decl/D4.lean`, `Hlow/H1.lean`, and `Hlow/H2.lean`. |
| `ErdosProblems/Hlow/H1.lean` | Proving `hlow` is the remaining route to the half-point bound. | `hlow` is false, and only one half of the trapping estimate needs it.  The failure at `(7,5)` is compatible with, and certifies, a hit. | `not_hlow_of_hhigh`, `hlow_fails_seven_five`, `lateGreedy_lower`, and `upper_trap_needs_hlow`. |
| `ErdosProblems/Hlow/H2.lean` | The tightest surviving margin is `52` at `(14,10)`, and `(7,5)` is the only equal-binary-length pair. | At first late ranks the smallest surviving margin is `30` at `(6,5)`; across all late ranks it is `3` at `(7,6)`.  Equal binary length also occurs at `(7,6)`.  The hit theorem is a quantitative sharpening of a route already available from `Decl/D4`. | `Hlow/verify/V2.lean`, including kernel proofs for the two counterexamples. |

## Corrections to scope, novelty, and logical strength

| File | Claim before correction | Corrected claim | Evidence forcing the correction |
|---|---|---|---|
| `ErdosProblems/Lift/AngleA1.lean` | Coordinate `j` needs at least `j+1` bits; the `4851`-bit and `12%` figures are certificate lower bounds; higher rungs are strictly stronger. | The theorem proves single-coordinate residue sensitivity.  The figures are arithmetic benchmarks, not certificate lower bounds.  The ladder implication is downward; strictness is not proved. | `Lift/verify/Check1.lean`, especially probes C–H. |
| `ErdosProblems/Lift/AngleA2.lean` | `t = 67` is the first open frontier, and the measured valuation deficit rules out the valuation route. | `t = 67` is a historical frontier; it is now certified at minimal depth `100`, and the finite band reaches `t ≤ 82`.  The valuation data rule out only the displayed sufficient criterion on the measured samples. | `Lift/Recon67.t67_minimal_depth`; `Skip/LadderT67.exists_diagonalKill_le_82`; `certifiedKill_of_far_end_valuation`. |
| `ErdosProblems/Lift/AngleA3.lean` | The residue criterion closes the relevant middle branch. | The criterion is conditional.  In the audited configuration its arc hypotheses are mutually contradictory, so the theorem does not act on a live class. | `Lift/verify/Check3.lean` and the explicit arithmetic contradiction in the corrected header. |
| `ErdosProblems/Lift/AngleA4.lean` | An arbitrary-real counterexample at `t = 67` shows the seed contains no frontier information, and localisation imposes a universal depth near `7.8·10^28`. | The counterexample shows only that lower-rung period-kill facts do not imply the next one for an arbitrary real number.  The localisation estimate is a no-go for that strategy, not a lower bound on every proof or on the concrete totient series. | `Lift/verify/Check4.lean::probe_reduction_is_an_iff`; `frontierWitness_fails_at_67`; the current depth-`100` certificate. |
| `ErdosProblems/Lift/AngleA5.lean` | A general no-lift theorem blocks all reuse from lower depths. | The no-go applies to the stated bounded-data and surrogate schemas.  It does not rule out every lift.  At `t = 67`, depth `98` is only a floor; the actual minimal certificate depth is `100`. | `Lift/verify/Check5.lean`; `Recon67.t67_minimal_depth`. |
| `ErdosProblems/Lift/AngleB1.lean` | The auxiliary phases and pulse floors describe the concrete seam ratchet. | They are auxiliary transported quantities.  Any statement about the concrete ratchet is conditional on the explicit bridge hypotheses. | `Lift/verify/Check6.lean` and the corrected import/bridge boundaries. |
| `ErdosProblems/Lift/AngleB4.lean` | Transported phase exclusions directly remove concrete survivor classes. | The phase exclusions are proved for auxiliary transported phases.  Concrete soundness remains conditional. | `Lift/verify/Check9.lean`; theorem signatures in `AngleB4.lean`. |
| `ErdosProblems/Lift/InduceLaw.lean` | The induction no-go excludes every lift strategy. | It excludes only arbitrary sequences and window data satisfying the stated recurrence schema.  It is not a no-go for every argument using the concrete totient function. | The quantified types of the no-go declarations in `InduceLaw.lean`. |
| `ErdosProblems/Lift/Recon249.lean` | Coefficient congruence is necessary and sufficient for lifting; coefficient scaling transfers certificates; depth `98` is an existence result. | The congruence is a sufficient coefficient identity under stated divisibility conditions.  The transfer theorem runs toward a no-larger radius and cannot implement `H → pH`; scaling need not preserve the excluded arc.  Depth `98` is a necessary floor, while `t = 67` fires at `100`. | `Lift/verify/Check12.lean::transfer_direction_blocks_lift`, `transfer_unusable_at_67`, `scaling_does_not_preserve_the_arc`; `Recon67.t67_minimal_depth`. |
| `ErdosProblems/Lift/Recon257.lean` | The finite ratchet reconstruction describes a live all-right landing. | The finite-core identities are proved, but connection to the concrete landing is conditional on `seamExcess (D+1) = 2`, which has no observed instance in the audited range. | Direct evaluation recorded in `NIGHT_LOG.md`; the corrected hypothesis-status section. |
| `ErdosProblems/Skip/D2.lean` | The finite row analysis yields an unconditional eventual late-skip result. | Finite scans are measured.  The proved global result is an eventual logical disjunction; it does not establish which branch occurs. | The quantified conclusions in `D2.lean`. |
| `ErdosProblems/Skip/D3.lean` | The finite checker closes the cofinal late-skip supply. | It certifies finite blocks and spot rows.  Cofinality is not proved. | `largestSkipLateAt_of_rowChk` and the finite table bounds. |
| `ErdosProblems/Skip/D4.lean` | The cofactor-rank premise is a plausible unresolved route. | The proposed universal premise is false.  The remaining theorems are unconditional dichotomies or conditional implications; no disjunction alternative is selected. | Counterexamples proved in `D4.lean`; finite selection data. |
| `ErdosProblems/Skip/D5.lean` | Cofactor ranks themselves supply the largest false rank. | A skipped late rank implies that the row’s actual largest false rank is late; the cofactor rank need not itself be maximal.  Landing consequences remain conditional. | `largestSkipLateAt_of_lateSkip`; measured cofactor selection data. |
| `ErdosProblems/Skip/D6.lean` | Measured cofactor selection rates support the all-right landing route. | The selection data are finite measurements.  The all-right and landing hypotheses remain unavailable, and no cofinal conclusion follows. | The conditional theorem signatures and the `[5,20000]` scan recorded in the file. |
| `ErdosProblems/Half/H1.lean` | The half-zone gap identity constrains the live `seamExcess = 2` landing. | The gap identities are unconditional, but the landing specialization has no observed instance and is presented only as a consistency statement. | The finite landing scan and the conditional hypothesis of `twentyOne_mul_overshoot_add_fortyTwo_eq_skipHalfGap`. |
| `ErdosProblems/Half/H3.lean` | The two-adic analysis proves that no finer two-adic obstruction exists. | The file rules out only the modulo-`2` and modulo-`4` shadows.  It computes the higher-modulus term but does not prove that the low support absorbs it. | `Half/verify/W3.lean`; `truncatedMersenneWeight_mod_twoPow_of_late`. |
| `ErdosProblems/Half/H4.lean` | The landing-row hypotheses are merely difficult to discharge. | The landing premise is false throughout the audited range, so the landing specializations are vacuous there.  The finite late-skip certificates remain valid. | `Half/verify/W4.lean::audit_skipD1_landingRow_premise_is_false` and its bounded extension. |
| `ErdosProblems/Half/FreeWalk1.lean` | The model proves no absolute bound for actual totient failure runs; its thresholds are unit-sharp; `coverage_fraction_tends_to_zero` proves a limit. | `AdmissibleRun` is a coarse interval model and omits evenness of genuine totient differences.  Its permanent walks are not totient orbits.  The coverage theorem proves one existential base point per multiplier, not a limit or eventual statement. | `Half/verify/W5.lean::probe_headline_equiv`, `probe_walkStep_even`, and `probe_coverage_is_only_an_existential`. |
| `ErdosProblems/Half/FreeWalk2.lean` | The walk gives an unconditional equivalence and the displayed long run is extremal. | The equivalence holds under its exact threshold hypotheses.  The numerical run is a finite certificate, not an extremal theorem. | `Half/verify/W6.lean` and the theorem signatures in `FreeWalk2.lean`. |
| `ErdosProblems/Half/FreeWalk3.lean` | `failure_zone_step_invariant` constrains totient differences; the seven-run is a minimal or extremal obstruction; `evenFloor` models the full arithmetic input. | The invariant is an arithmetic-free cancellation.  `evenFloor` models only crude size/parity data and fails stronger totient facts.  Longer runs already exist, including an eight-run at the same parameters. | `Half/verify/W7.lean`, especially sections 4, 5, and 7. |
| `ErdosProblems/Bit/Corr3.lean` | Finite top-run data prove `O(log s)` behaviour and a geometric law; row `5` is not explained by the top-run equivalence. | The finite data show a maximum of `12` on `[5,3000]`; they prove no asymptotic law.  At row `5`, the top run has length `1 = K`, so the proved equivalence is correct; only the separate remainder-bit interpretation fails there. | `Bit/verify/B3.lean` finite probes and the row-`5` tuple `(5,3,1,1,true)`. |
| `ErdosProblems/Bit/R1.lean` | Rows `1500,1501` extend the corpus’s reach without inspecting greedy words. | The theorem interface uses two scalar remainders, but those are computed through the greedy words.  `Skip/D3` already certifies those rows and row `3000`; this is a route comparison, not extra reach. | `Bit/verify/B4.lean`; definitions of `remOf` and `SkipD3.gb`. |
| `ErdosProblems/Bit/R3.lean` | The dichotomy exactly classifies the row, a success buys a whole window of good rows, and the seam gap is a universal factor-four wall. | The dichotomy is inclusive; the escape theorem yields at least one late-skip row in the interval.  The gap theorem proves the displayed `GapDominates` parameter, not its optimality or a universal no-go. | `RemC1.rowLaw_blind_at_16`; `exists_largestSkipLateAt_of_deficit`; the type of `gap_is_two_pow_succ`. |
| `ErdosProblems/Bit/R4.lean` | The threshold is half the new top weight; `2^s+1` is the exact fixed point; all global hypotheses have witnesses. | The proved threshold is `2^(s-1)` while the new weight is `2^(s+2)+4`.  The rational offset fixed point is `4/3`; `+1` is the largest integer below it.  Only local one-row hypotheses have witnesses; cofinal and endpoint hypotheses remain open. | `topWeight_eq`; the translated recurrence; the corrected §6/§8 witness audit. |
| `ErdosProblems/Rem/C1.lean` | The row recurrence plus any ceiling can never recover lower-rank information. | The no-go covers the listed row inequalities and ceiling classes.  It is not a theorem about every possible auxiliary invariant. | `le_of_descent_of_quadrupling`, `surplusModel_constraints`, and `rowLaw_blind_at_16`. |
| `ErdosProblems/Rem/C2.lean` | Every unconditional `O(2^s)` bound must use growing certificate depth. | The conclusion applies to the encoded fixed finite subset-certificate method.  It is not a no-go for every proof method. | `certificate_exceeds_half_point` and `certificate_lt_half_iff`. |
| `ErdosProblems/Rem/C4.lean` | The theorem supplies a new global refinement. | The result is a genuine conditional `13/6` refinement but does not establish the global hypothesis and overlaps earlier machinery. | `Rem/verify/C4.lean` redundancy and satisfiability audit. |
| `ErdosProblems/Rem/C5.lean` | The weight-word argument is the universal source of remainder bounds. | It is a generic bound from a supplied admissible word.  `Rem/C6` later proves a stronger unconditional numerical bound; neither statement covers every possible method. | `seamIntegerGreedyRemainder_add_tail_le`, `eight_mul_remainder_le`, and the later `C6` theorem. |
| `ErdosProblems/Three/T2.lean` | Every theorem hypothesis except `CarryCofinally` has a concrete instance; row `13` is the sharp carry defect. | Two global hypotheses are uninstantiated: `CarryCofinally` and `1/2 ∉ mersenneAchievementSet`.  Row `13` is a proved large witness, not a maximum; row `5` has a larger normalized defect. | `Three/verify/T2.lean` sections 7b and 8. |
| `ErdosProblems/Three/T3.lean` | Finite valuation counts establish a geometric fair-bit law and a new global route. | The histogram is finite measured data with no distribution theorem.  The Lean results are conditional sufficient criteria plus finite witnesses. | `Three/verify/T3.lean`; the explicit open-hypothesis list in `T3.lean`. |
| `ErdosProblems/Decl/D1.lean` | The declined-rank condition discharges the full side condition used by `Three/T4`. | It proves `hhigh` at declined ranks, a strictly narrower input.  It does not prove `hlow`, which is false in general. | `Decl/verify/D1.lean` section 7; `DeclD4.Seven.not_hlow_seven_five`. |
| `ErdosProblems/Decl/D2.lean` | Decline blocks have an exact full-weight ratio, their length is anti-correlated with invariant failure, and the block no-go describes reachable corpus residuals. | The exact identity is only between leading powers; the full-weight result is an inequality.  The no-go uses the artificial residual `w d - 1`, whose reachability is not proved.  The finite examples do not establish correlation, asymptotic run length, or universal-word stabilization. | `Decl/verify/D2.lean`; `declineBlock_gain`, `run_collapse_twenty`, `not_blockMethod_sound`, and `T1.not_residualInvariant`. |
| `ErdosProblems/Decl/D3.lean` | The first-late-rank route makes the remainder bound unconditional. | The branch that would remove `hhigh` already assumes enough to imply the target, and no late-rank failure of `hhigh` is observed.  The route remains conditional. | `Decl/verify/D3.lean` sections 3–5. |
| `ErdosProblems/Decl/D4.lean` | The cited terminal-rank interval theorem proves that no interval induction can establish `hhigh` at an earlier late rank. | That citation was a non sequitur.  The verifier supplies a correctly indexed theorem ruling out the stated `IntervalCeiling` method.  This is not a no-go for every proof of `hhigh`. | `Decl/verify/D4.lean::IntervalCeiling.four_pow_le_at` and `no_intervalCeiling_certifies_hhigh`. |
| `ErdosProblems/Hlow/W1.lean` | Finite pulse data establish subpolynomial behaviour, a cofinal supply, and a global identification with the real greedy state. | The divisor-count inequality is proved; the asymptotic description is background, not formalized.  The selected-pulse hits and real-greedy correspondence are finite measurements and imply no cofinality or limiting law. | `wordPulse_le_divisorPulseBudget`; the explicitly bounded scans in `W1.lean`. |
| `ErdosProblems/Hlow/W3.lean` | Finite histograms are geometric/equidistributed, all row words form one infinite word, and `1/2` is typical. | The file records finite measurements only: five sampled row words, bounded histograms, and a small target sample.  No distribution, asymptotic, or typicality theorem is proved. | The exact finite ranges stated in `W3.lean`. |

## Corrections to repository status and historical snapshots

| File | Claim before correction | Corrected claim | Evidence forcing the correction |
|---|---|---|---|
| `ErdosProblems/DemandLedger/Basic.lean` | The current semantic corpus has `259` conditional declarations and the Lean ledger has `105` named propositions. | Those numbers described the extraction snapshot.  The checked-in file currently exposes `101` named propositions, `23` labelled substantial; current semantic-corpus totals are generated separately. | Direct declaration count in `Basic.lean`; current `docs/semantic_corpus.json`. |
| `ErdosProblems/DemandLedger/edges/ClusterB.lean` | The survivor gaps form a strict one-way chain and the reverse edges are unproved. | This file proves a direct chain only.  `Bridge1.lean` later proves reverse implications through the irrationality hub, making the gaps equivalent. | The edge theorems in `Bridge1.lean`. |
| `ErdosProblems/DemandLedger/edges/ClusterD.lean` | Five logical implications remain open. | Five direct finite-certificate conversions are not proved in this file.  `Bridge2.lean` later proves the gap statements equivalent by a different route. | The cross-edge theorems in `Bridge2.lean`. |
| `ErdosProblems/DemandLedger/edges/ClusterF.lean` and `Bridge3.lean` | The block demands are strictly ordered. | The stated implications are proved; strict non-implications are not. | The files contain implication theorems but no separation countermodels. |
| `ErdosProblems/DemandLedger/edges/Discharge1_G097.lean` | The corpus stops at `t = 66`; `t = 67` is the first untouched diagonal cell. | This is a historical snapshot.  `t = 67` is certified at minimal depth `100`, and the current finite diagonal band reaches `t ≤ 82`. | `Lift/Recon67.lean`; `Skip/LadderT67.lean`. |
| `ErdosProblems/DemandLedger/edges/Discharge2_G100.lean` | The proved supply stops at `67`, and the deepest corpus certificate is depth `94`. | Those are imported-snapshot facts for this module.  The repository now has exact minimal depths `100,105,113,120,120` at later jump cells and a band through `82`.  The cofinal demand remains open. | `Lift/Recon67.lean`, `Lift/CertT67.lean`, `Skip/LadderT67.lean`. |
| `paper/erdos249-257-main-paper.tex` (read-only during this audit) | Farey was framed as historical terminology rather than as the source of the denominator bound. | The classical neighbouring-fraction/mediant argument directly gives `b+d-1`, exactly equal to the formal exclusion bound. The numerical improvement over Farey is `0`; the formal source checks the arithmetic instance and its sharp first failure. The publication owner has now applied this correction to the protected source as well as `README.md`, `docs/RESULTS.md`, `docs/PRIOR_ART.md`, and the curated authority `docs/claims.json`. The generated full-text paper projection remains stale until its owner exporter is run against a stable manuscript/PDF pair. | Independent recomputation at `K=120` and `K=240`; `GapFareyBound.farey_gap` and both `gap_check_window_*_first_failure` declarations. |

## Protected systems-paper status

`paper/claim-faithful-publication-systems-paper.tex` was read end to end but
remained read-only in this lane. The publication owner has since updated the
worked example to the current bounded theorem—one checked certificate at every
lcm-diagonal scale `t ≤ 82`, with nothing asserted at `t = 83`—while retaining
the older 28-point aggregator only as historical provenance. The source is
currently 901 lines, so the requested aggressive compression remains open even
though the mathematical snapshot is current.

A claim-preserving revision can fit within 462 lines by keeping each argument
once:

| Revised block | Maximum lines | Claim that must remain |
|---|---:|---|
| Front matter and abstract | 45 | Lean checks formal statements; it does not interpret unrestricted public prose. |
| Publication gap and one workflow figure | 70 | A reviewed claim record plus a release checker preserves named relationships; human review remains authoritative. |
| One current worked example | 90 | The finite band is now `t≤82`; the unbounded supply remains open and endpoint-equivalent to #249. |
| Trust boundary and escaped mutation | 90 | One of ten historical edits escaped; the repaired witness covers that one fault and supplies no detection rate. |
| Limits, reuse, related work, conclusion | 85 | Unregistered wording, coordinated wrong changes, and mistaken review remain outside the guarantee. |
| Reproduction and bibliography | 82 | Exact artifacts and commands remain recoverable. |

Compression should remove repeated explanation, not any claim in the rightmost
column. The generated full-text projection and publication digests must be
refreshed only after the protected source and rendered PDF stabilize.

## Statements that remain open

The audit found no proof of either Erdős problem.

- Erdős #249 remains open.  The finite diagonal band `t ≤ 82` and the
  off-diagonal certificates are finite results, not a cofinal supply.
- Erdős #257 remains open.  The residue, carry, bit, and late-skip criteria are
  reductions or finite certificates.  None proves the required cofinal event.

The absence of a correction for a theorem statement means only that its Lean
type checked.  It does not promote a finite measurement to a theorem.
