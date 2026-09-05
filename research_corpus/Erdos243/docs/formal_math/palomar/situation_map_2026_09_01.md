# The situation: private mathematics versus its public mapping, 2026-09-01

Written while the first three Palomar canaries were passing mechanical verification. Corrected the same evening by `longitudinal_truth_2026_09_01.md` §6 (the #68 row in section 4, the #1049 Step 1 claim, the #1041 phantom file). Every number
below was computed this evening by scripts over the live tree; the boundary section says what each
number can and cannot mean. Sources of authority: `docs/formal_math/palomar/launch_selection_v1.json`
(what is public), the 72 `ExternalVerification*/` directories (what is packaged), the Lean source
libraries (what is proved), the four `.tex` papers plus seven unapplied `.patch` files (what is
written), and the per-problem `FRONTIER.md` files (what is current).

## 1. What is public today

| Surface | State |
|---|---|
| Public repository | `wcook04/plectis-erdos-lean`, fresh root, `main` = `c39cea6a976747d132a848d26f110b9c608d5a45` |
| Entries in it | 19, across all eight problems; full-strength abstracts rewritten today |
| Palomar mechanical verification | 3 of 3 canaries passed (`#257 ReciprocalSupport`, `#1041 SolvedFamilies`, `#251 PolynomialShiftCountermodel`); remaining 16 draining serially |
| Palomar editorial review | none seen yet; registration is a separate, operator-consented step per entry |
| Three systemic defects found and fixed on the way | metadata path must be sent explicitly; Mathlib pin must be a `master` ancestor (`v4.29.0`, not the `v4.29.1` tag); a Solution must not share the Challenge's module prefix (`Solutions/<Entry>.lean`) |

Palomar allows a **new version** of a registered entry through `existing_id` on intake, and any
number of **new entries** at the same repository and commit. So the public mapping can be improved
continuously: rewrite or extend an entry, re-export, push, submit. Nothing about the registry stops
us from moving the public claim to wherever the private mathematics actually is. The vehicle rule:
a new version is right only where the *same* statement is widened; a different theorem with a
different mechanism is a new entry.

The lag is not an oversight but a recorded state. Each problem's `research_packet.json` carries a
`public_projection.state`: #251, #269 and #1049 read `withheld_pending_human_mathematical_review`;
#249 and #257 read `kernel_checked_private_ready_for_public_projection_and_human_mathematical_review`;
#1041 has none. The packets hold 632 recorded exact results across the eight problems
(68:108, 243:72, 249:47, 251:27, 257:57, 269:60, 1041:177, 1049:84); the 19 public entries compare
83 theorem names.

## 2. The corpus, in numbers

| Measure | Value |
|---|---|
| Lean modules / lines / theorem+lemma declarations | 1,239 / 954,703 / 16,772 |
| Machine-emitted certificate mass (`DiagonalPincerPrimeCertificates`, `GeneratedCertificates`, `ClosureT64`) | 501 files, 727k lines (76%), 6,762 declarations (40%) |
| Hand-written source theorems | 9,506 |
| `ExternalVerification*` entries | 72 (19 launched, 52 reserve, 1 held) |
| Source theorems wrapped by any entry | 236 (2.4% of hand-written) |
| Source theorems reached by the 19 public entries | 96 (1.0%) |
| Reserve entries that are sorry-free with metadata present | 53 of 53 |
| `sorry` outside `Challenge.lean` / `NegativeSolution.lean`; `axiom` declarations | 0; 0 |
| Unwrapped hand-written theorems whose docstring calls itself a main theorem or an Erdős closure | 113 |
| Unwrapped hand-written theorems with proofs of 50+ lines | 539 |

The corpus is not short of formalisation. It is short of *packaging and publication*: the launch
took roughly one entry per mechanism family and left the equivalences and frontier statements in
reserve directories that are already built.

## 3. The dominant gap class: Lean-proved, packaged, not launched

Four of the eight problems have their canonical frontier statement Lean-checked, packaged in a
reserve directory, and absent from the public release.

| Problem | Frontier result sitting in reserve | Directory | What the public entry carries instead |
|---|---|---|---|
| #68 | Exact carry characterisation: an equivalence to #68 itself | `ExternalVerification68StrictSuccessorCarry` | a conditional radius floor |
| #249 | `FullMersenneCanonicalBasepointResidueGapSupply`, Lean-equivalent to irrationality | `ExternalVerification249CanonicalMersenneFrontier` | anchors and a sharp floor |
| #257 | Complete unconditional achievement-set classification (measure `2^-|F|`, nowhere dense) and the `1/21` fatal-branch dichotomy, the live frontier | `ExternalVerification257AchievementSetGeometry`, `ExternalVerification257TwentyOneFatalBranch` | three supporting theorems |
| #269 | Actual infinite dyadic-shell orbit: summability, exact recurrence, integer-or-cofinal-`1/31` dichotomy | `ExternalVerification269ActualShellOrbit` | seven finite-structure theorems |

Further reserve directories that are complete and unlaunched at zero authoring cost: #251
`AffineCircularity`, `LcmDiagonalCriterion`, `PrimeGapIdentity` (would take #251 from 2 to 5 public
entries); #243 `BoundedNegativePartRigidity` (a strict superset of the launched theorem, with no
periodicity hypothesis); #68 `PrimeUnitTranslator`, `MovingFactorScaleSplit`; #257
`ScaledGreedyTrap` (general-q normal forms subsuming the ad hoc `1/2` and `1/21` cases),
`BooleanMobiusCarry`, `PositiveSkipEquivalence`; #249 `FullDepthRayAmplifier`, `CarryRankFrontier`,
`DyadicTotientKernel`; #1041 `FirstMergeCriticalValueSeparation` (the all-degree critical-value
separation theorem, stronger in kind than every launched #1041 entry, gated on an unapplied paper
patch).

## 4. Public entries that understate their own source file

| Entry | Ships | Sits unshipped in the same source module |
|---|---|---|
| `ExternalVerification68ChannelRadius` | `3t^3 < 2(R+1)` at threshold `2^32`, which is the stronger of the two cubic constants (the second pass corrected the first: `t^3 < 8(R+1)` at `4096` is weaker and already consumed by the shipped little-o theorem) | the method's own ceiling `sharp_radius_satisfies_square_log_constraint` (`ChannelIntegralCongruence.lean:764`): the log constraint is already met at `9(R+1) = 16 t^3`, so the one-kernel method cannot reach its sharp constant |
| `ExternalVerification1049AdelicHeightBridge` | the rank-41 four-jet collision | `exists_distinct_binary_selectors_same_fourJet_of_power_certificate`: the general power-certificate compiler |
| `ExternalVerification1049RationalBaseBarrier` | the coordinatewise corridor no-go | the exact homogenisation ceiling `a > b^2` with its deficit formula (computation, `HomogenisationCeilingProof.md`) |
| `ExternalVerification269ThreePrimeStructure` | seven finite-structure theorems | the dyadic radix-alphabet identity `{2,6,10,30}` (`threePrimeHeight_dyadicBlock_succ`) |

These are the cases where a Palomar **new version** of the existing entry is the right vehicle.

## 5. Unwrapped and non-trivial: the deepest of the 9,399

The proxy is proof length plus a summit-docstring signal; it is a reading list, not a ranking of
importance. Top items: `Erdos68/PrimeZeroBranch.lean:7032`
`irrational_factorialGapSeries_of_cofinal_prime_lower_endpoint_escape` (308 lines);
`Erdos257PeriodNoncollapse/HalfCylinderMiddleCarryLowerBound.lean:5614`
`half_mem_mersenneAchievementSet_of_upperResetDyadicBandEscape` (134 lines, final fan-in to the
`1/2` endpoint); three exact `iff` characterisations of #68
(`PrimeThresholdParity.lean:407`, `ShrinkingTargetNormalForm.lean:82`, `PrimeThresholdParity.lean:169`)
and one of #249 (`TotientTailCarryPeriod.lean:875`,
`irrational_totientSeries_iff_cofinalDirectedLcmCertificateSupply`), none wrapped by any entry.
Every conditional closure of #249 in `CyclotomicAnchoredKill.lean` (lines 2037, 2109, 3373) is
likewise unwrapped. Full list of forty: see the inventory receipt referenced at the end.

## 6. Paper side: written but unbound

| Paper | Theorem environments | Lean-bound (ledger or `\pdecl`) | Unbound |
|---|---|---|---|
| `erdos-1041-lemniscate-newton-flow.tex` | 22 | 7 | 15 |
| `erdos-257-mersenne-support-subseries.tex` | 23 | 3 | 20 |
| `erdos-68-factorial-denominator-irrationality.tex` | 9 | 6 | 3 |
| `contributions-digest.tex` | 0 (114 `\pdecl` references) | | |

The #257 paper uses no `\pdecl` macro at all, so its 20 unbound results include several that
have live Lean entries (`res:one-over-twenty-one`, `res:scaled-greedy-trap`). That is a labelling
gap, not a formalisation gap. There is no `.tex` for #243 or #251. Seven `.patch` files under
`papers/` carry staged theorem text that is in none of the counts above, including the #1041
critical-value separation theorem and the #68 companion-orbit equivalence.

Genuinely paper-only or computation-only results with no Lean vehicle, in rough order of what
formalising them would earn: #1041 `FP_4` proved completely and the all-degree bridge
`FP_{n-1} ⇒ (S)_n` (together they give `(S)` in degrees 4 and 5), the star kernel as a theorem at
every degree, the two-root area constant `Θ_{5,2} ≥ 0.940354223795` by exact-rational certificate;
#1049 Step 1 (`J_5 = {4,20,24}` finite, so `5 | B_j` for every `j ≥ 50`), which is **conditional** on the all-level monodromy premise `(M)/(C5)` certified only at `N ≤ 3`; the packet's statement field is stale in the unconditional form, the Casoratian block-structure theorem, the all-`d` first-appearance
non-cancellation, the all-rank `q`-order `N(N-1)(2N-1)/6` with leading coefficient
`(N!)²(N+1)!/2^N`; #249 all-rung strict log-concavity `Θ_r Θ_{r+2} < Θ_{r+1}²` for every `r ≥ 1`
and the exact closed form `Σ_{gcd(a,b)=1} r^{a+b}/(1-r^{a+b}) = (r/(1-r))²` (both Lean-checked,
neither in any entry); #251 the free-pair reduction; #269 the torus-Fourier representation and the
general bounded-radix dichotomy (Lean-checked, used only instantiated). Certified continued-fraction
exclusions: #249 `q ≥ 2^39990 > 10^12039` unrestricted; #251 has a certified exclusion whose
constant the two passes did not agree on, so it is not quoted here. The #1041 gap is the largest
paper-versus-Lean gap in the corpus and the selection file's `paper_only_summits` rule is the reason
its five public entries are narrow; the fix there is formalisation, never re-description.

## 7. One public claim that is badly stale

The older public repository's v0.5.0 release notes advertise the #249 denominator exclusion
"through 79639646646701375323355774875831053" (about `8 × 10^34`). The private certified exclusion
is unrestricted and reaches `10^12039`. Nothing needs proving; the public statement needs updating,
and the older repository is no longer the release root.

## 8. Housekeeping surfaced along the way

- `ExternalVerification1041CyclicTetranomialCoefficient` and `...SignedMomentTetranomial` are verbatim
  duplicates of the launched `TetranomialSpokes` (now marked `superseded_by`).
- `ExternalVerification269AllScaleLattice` has seven unstaged modified files.
- `ErdosProblems/Erdos1049/AdelicHeightBridge.lean` has an uncommitted new theorem
  (`coeff_zudilinTransformedNormalizedMoment_two_zero_first = 18`) reflected in no entry.
- `ErdosProblems/Erdos1041/STRONGEST_RESULTS.json` does not exist and never did; `FRONTIER.md` line 3
  warns readers off a phantom file.
- `ExternalVerification257TwentyOneFatalBranch`'s comparator omits its own base case
  `finiteErdosSum_ne_one_div_twenty_one`.
- Every launch entry's private `palomar_qualification` block still reads pre-submission; the public
  projection strips it, so nothing leaks, but the private metadata is behind the truth.
- `submission_framing_audit.md` and `publication_worklist.md` are dated 2026-07-23 and measure
  against the older paper repository; their "#251 may have no qualifying result" verdict is stale,
  since `p_n ≤ 1250(n+1)^4` and gap-unboundedness are unconditional Lean theorems.
- The older public repository's release notes and the packets disagree on #68's projection state
  (`released` versus `withheld`).

## 9. What follows, in order of value per hour

1. Promote the four canonical-frontier reserve directories (#68 carry characterisation, #249
   canonical Mersenne frontier, #257 achievement geometry and `1/21` branch, #269 actual shell
   orbit). Each is built and sorry-free; the cost is the full-strength abstract and a replay.
2. Ship the zero-cost complete reserves: three at #251, `BoundedNegativePartRigidity` at #243,
   `PrimeUnitTranslator` at #68, `ScaledGreedyTrap` at #257.
3. Issue new versions of the four understated entries in section 4.
4. Apply the seven paper patches, add `\pdecl` bindings to the #257 paper, and write the missing
   #243 and #251 manuscripts, so the paper claim and the Lean claim stop diverging.
5. Only then decide which paper-only results deserve Lean; the corpus already has more proved
   than published.

## Evidence boundary

Declaration counts are a column-0 regex cross-checked against a plain grep (16,661 vs 16,772);
"wrapped" is syntactic reachability from `Solution.lean` and undercounts transitive dependencies,
so "unwrapped" means "not named by any comparator entry", never "unimportant". "Sorry-free" is a
comment-stripped grep, not a build, although the 19 launch entries did build and replay today.
Paper counts are a regex over `\begin{theorem|proposition|corollary}` in the four `.tex` files and
exclude the patches. Prior-art boundaries (#269 two-prime is Steve Fan; #249 affine-totient is
Martin 2006; #257 `{k^s}` is Duverney and Tachiya) are carried from earlier audits and were not
re-verified against arXiv tonight. The full per-problem gap tables and the forty-item reading list
are in the two agent reports from session `22e9a3b6` on 2026-09-01; this document is their
synthesis.
