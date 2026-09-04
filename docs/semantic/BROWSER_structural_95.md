# structural_95: Exact source-structural proposition families

[All problems and zones](BROWSER.md)

<a id="node-ffdc862b1d266b4b"></a>
## HalfCarryReachability

SOURCE-STRUCTURAL FAMILY: 1 theorem/lemma declaration(s) in `Erdos249257/HalfCarryReachability.lean` share the normalized Lean proposition schema `{L M N : ℕ} (hLM : L ≤ M) (hMN : M ≤ N) (a : HalfWord N) : restrictWord hLM (restrictWord hMN a) = restrictWord (hLM.trans hMN) a`.

Class: infrastructure. Interpretation: source_structural_family. Prior-art assessment: not_assessed.

Scope: This machine-derived family proves exact source linkage and shared proposition shape only. It is not a reviewed mathematical paraphrase, a novelty claim, or evidence that different family members are logically equivalent.

- Lean declaration: [restrictWord_trans](../../Erdos249257/HalfCarryReachability.lean#L114)


<a id="node-53c4afb0f3b41738"></a>
## R3

SOURCE-DOCUMENTED: Carry-free form of the escape step: `carryTaken s ≤ 2 * (s - 2)` always, so `2 ^ (s+1) + 2 * s + 4 ≤ 4 * r s` is enough to trigger it.

Class: infrastructure. Interpretation: source_structural_family. Prior-art assessment: not_assessed.

Scope: This machine-derived family proves exact source linkage and shared proposition shape only. It is not a reviewed mathematical paraphrase, a novelty claim, or evidence that different family members are logically equivalent.

- Lean declaration: [remainder_succ_le_of_large'](../../ErdosProblems/Bit/R3.lean#L430)


<a id="node-1f719c8cd9ebe5fe"></a>
## TwentyOneQuotientGreedy

SOURCE-DOCUMENTED: **No first divergence.** Start quotient greedy at the exact quotient defect left by an already agreed prefix `P`. If its completed support is still below `1/21`, then every remaining quotient decision agrees with the exact rational greedy decision from the corresponding rational residual.

Class: infrastructure. Interpretation: source_structural_family. Prior-art assessment: not_assessed.

Scope: This machine-derived family proves exact source linkage and shared proposition shape only. It is not a reviewed mathematical paraphrase, a novelty claim, or evidence that different family members are logically equivalent.

- Lean declaration: [localQuotientGreedyBits_eq_rationalGreedyBitsFrom_of_safe](../../Erdos249257/TwentyOneQuotientGreedy.lean#L1063)


<a id="node-69cee4d57e433b08"></a>
## R2

SOURCE-DOCUMENTED: **Surplus step.** On a right branch a surplus of at least `2 * s` above the half point at least triples.

Class: infrastructure. Interpretation: source_structural_family. Prior-art assessment: not_assessed.

Scope: This machine-derived family proves exact source linkage and shared proposition shape only. It is not a reviewed mathematical paraphrase, a novelty claim, or evidence that different family members are logically equivalent.

- Lean declaration: [surplus_step](../../ErdosProblems/Bit/R2.lean#L320)


<a id="node-5de9881a6b628786"></a>
## LcmFactorIdealPulseObstruction

SOURCE-DOCUMENTED: The synthetic state remains strictly inside every diagonal carry strip.

Class: infrastructure. Interpretation: source_structural_family. Prior-art assessment: not_assessed.

Scope: This machine-derived family proves exact source linkage and shared proposition shape only. It is not a reviewed mathematical paraphrase, a novelty claim, or evidence that different family members are logically equivalent.

- Lean declaration: [lcmAnchorPulse_strict_survivor](../../Erdos249257/LcmFactorIdealPulseObstruction.lean#L771)


<a id="node-1d064180097ce3f5"></a>
## SupportSunflowerDichotomy

SOURCE-STRUCTURAL FAMILY: 1 theorem/lemma declaration(s) in `Erdos249257/SupportSunflowerDichotomy.lean` share the normalized Lean proposition schema `(P : ℕ → Prop) [DecidablePred P] (e : ℕ) : ((Finset.range (e + <num>)).filter P).card = ((Finset.range e).filter P).card + if P e then <num> else <num>`.

Class: infrastructure. Interpretation: source_structural_family. Prior-art assessment: not_assessed.

Scope: This machine-derived family proves exact source linkage and shared proposition shape only. It is not a reviewed mathematical paraphrase, a novelty claim, or evidence that different family members are logically equivalent.

- Lean declaration: [filter_range_succ_card](../../Erdos249257/SupportSunflowerDichotomy.lean#L643)


<a id="node-7af568675dd537a4"></a>
## D5

SOURCE-DOCUMENTED: **PROVED for the auxiliary budget.** For every phase outside `D ≡ 20 (mod 21)`, `cof3Run D 6 = 0`; this covers `2600` of the `2730` joint phases using no half rank. It does not by itself empty any concrete survivor class: the connection to the seam orbit additionally requires `hright`, `hlanding`, and a finite support hypothesis.

Class: infrastructure. Interpretation: source_structural_family. Prior-art assessment: not_assessed.

Scope: This machine-derived family proves exact source linkage and shared proposition shape only. It is not a reviewed mathematical paraphrase, a novelty claim, or evidence that different family members are logically equivalent.

- Lean declaration: [cof3Ratchet_finite_core](../../ErdosProblems/Skip/D5.lean#L500)


<a id="node-46fe2bef553a8053"></a>
## D4

SOURCE-STRUCTURAL FAMILY: 1 theorem/lemma declaration(s) in `ErdosProblems/Skip/D4.lean` share the normalized Lean proposition schema `{s d : ℕ} (hd : d ∈ cof5Rank s) : <num> * s ≤ <num> * d + <num>`.

Class: infrastructure. Interpretation: source_structural_family. Prior-art assessment: not_assessed.

Scope: This machine-derived family proves exact source linkage and shared proposition shape only. It is not a reviewed mathematical paraphrase, a novelty claim, or evidence that different family members are logically equivalent.

- Lean declaration: [cof5Rank_lower](../../ErdosProblems/Skip/D4.lean#L292)


<a id="node-c78fd3aef35c8b96"></a>
## Wire2

SOURCE-DOCUMENTED: **Sharpness of the exponent `3/2`.** No rank certifiable from divisibility alone ever exceeds `2 s / 3`: a divisor `d` of `2s+1` or `2s+2` with `d < s` has cofactor at least `3`. So a block starting at `S` can contain a certified rank of row `s` only when `3 * S ≤ 2 * s + 2`, and the method below cannot be pushed past that.

Class: infrastructure. Interpretation: source_structural_family. Prior-art assessment: not_assessed.

Scope: This machine-derived family proves exact source linkage and shared proposition shape only. It is not a reviewed mathematical paraphrase, a novelty claim, or evidence that different family members are logically equivalent.

- Lean declaration: [largestCertifiableRank_le](../../ErdosProblems/Skip/Wire2.lean#L185)


<a id="node-853fa6fb0431df7b"></a>
## BooleanMobiusLocalRepair

SOURCE-DOCUMENTED: Conditional block realization of the endpoint repair integer. The fractional-part theorem supplies nonnegativity. The only remaining local feasibility input is the genuine capacity bound `H < 2^(n-⌊n/2⌋)`.

Class: infrastructure. Interpretation: source_structural_family. Prior-art assessment: not_assessed.

Scope: This machine-derived family proves exact source linkage and shared proposition shape only. It is not a reviewed mathematical paraphrase, a novelty claim, or evidence that different family members are logically equivalent.

- Lean declaration: [exists_upperHalf_boolean_word_for_localRepairInteger](../../Erdos249257/BooleanMobiusLocalRepair.lean#L699)


<a id="node-ff6d93d17457332a"></a>
## LadderT67

SOURCE-STRUCTURAL FAMILY: 3 theorem/lemma declaration(s) in `ErdosProblems/Skip/LadderT67.lean` share the normalized Lean proposition schema `: certifiedKill (periodLcm <num>) (periodLcm <num>) <num>`.

Class: infrastructure. Interpretation: source_structural_family. Prior-art assessment: not_assessed.

Scope: This machine-derived family proves exact source linkage and shared proposition shape only. It is not a reviewed mathematical paraphrase, a novelty claim, or evidence that different family members are logically equivalent.

- Lean declaration: [certifiedKill_diagonal_t73](../../ErdosProblems/Skip/LadderT67.lean#L71100)
- Lean declaration: [certifiedKill_diagonal_t79](../../ErdosProblems/Skip/LadderT67.lean#L71177)
- Lean declaration: [certifiedKill_diagonal_t81](../../ErdosProblems/Skip/LadderT67.lean#L71242)


<a id="node-9a7291583277d599"></a>
## SuffixCylinderFiniteGap

SOURCE-STRUCTURAL FAMILY: 1 theorem/lemma declaration(s) in `Erdos249257/SuffixCylinderFiniteGap.lean` share the normalized Lean proposition schema `{N L U L' U' C : ℕ} (hN : <num> ≤ N) (W : SelectedHalfInterval N L U) (hL'pos : <num> ≤ L') (hU'strip : U' ≤ halfStripBound (N + <num>)) (hparentLo : ∀ q : ℕ, L' ≤ q → q ≤ U' → L ≤ parent C q) (hparentHi : ∀ q : ℕ, L' ≤ q → q ≤ U' → parent C q ≤ U) (hcoeff : ∀ k : ℕ, ∀ hkL : L ≤ k, ∀ hkU : k ≤ U, supportCoeff (wordSupport (W.word k hkL hkU)) (N + <num>) = C) (q : ℕ) (hqL : L' ≤ q) (hqU : q ≤ U') : (selectedHalfIntervalStepExplicit hN W hL'pos hU'strip hparentLo hparentHi hcoeff).word q hqL hqU = extendHalfWord (W.word (parent C q) (hparentLo q hqL hqU)`.

Class: infrastructure. Interpretation: source_structural_family. Prior-art assessment: not_assessed.

Scope: This machine-derived family proves exact source linkage and shared proposition shape only. It is not a reviewed mathematical paraphrase, a novelty claim, or evidence that different family members are logically equivalent.

- Lean declaration: [selectedHalfIntervalWord_stepExplicit](../../Erdos249257/SuffixCylinderFiniteGap.lean#L122)


<a id="node-267fb9673c82a8b2"></a>
## FreeKill64FiftyFourAZ

SOURCE-STRUCTURAL FAMILY: 1 theorem/lemma declaration(s) in `ErdosProblems/FreePosition/FreeKill64FiftyFourAZ.lean` share the normalized Lean proposition schema `{M : Type*} [Monoid M] (a : M) (n : ℕ) : fiftyFourAZFastPow a n = a ^ n`.

Class: infrastructure. Interpretation: source_structural_family. Prior-art assessment: not_assessed.

Scope: This machine-derived family proves exact source linkage and shared proposition shape only. It is not a reviewed mathematical paraphrase, a novelty claim, or evidence that different family members are logically equivalent.

- Lean declaration: [fiftyFourAZFastPow_eq_pow](../../ErdosProblems/FreePosition/FreeKill64FiftyFourAZ.lean#L15)


<a id="node-4207b7f6df8dfb17"></a>
## GreedyAchievementSet

SOURCE-STRUCTURAL FAMILY: 1 theorem/lemma declaration(s) in `Erdos249257/GreedyAchievementSet.lean` share the normalized Lean proposition schema `@[simp] theorem positiveMersenneSupportSuffix_zero_index (A : Set ℕ) : positiveMersenneSupportSuffix A <num> = positiveMersenneSupportValue A`.

Class: infrastructure. Interpretation: source_structural_family. Prior-art assessment: not_assessed.

Scope: This machine-derived family proves exact source linkage and shared proposition shape only. It is not a reviewed mathematical paraphrase, a novelty claim, or evidence that different family members are logically equivalent.

- Lean declaration: [positiveMersenneSupportSuffix_zero_index](../../Erdos249257/GreedyAchievementSet.lean#L753)


<a id="node-200c6152f7e8e389"></a>
## H2

SOURCE-STRUCTURAL FAMILY: 1 theorem/lemma declaration(s) in `ErdosProblems/Hlow/H2.lean` share the normalized Lean proposition schema `(s C d : ℕ) : skipCorrection s C d ≤ lateCorrection s d`.

Class: infrastructure. Interpretation: source_structural_family. Prior-art assessment: not_assessed.

Scope: This machine-derived family proves exact source linkage and shared proposition shape only. It is not a reviewed mathematical paraphrase, a novelty claim, or evidence that different family members are logically equivalent.

- Lean declaration: [skipCorrection_le_lateCorrection](../../ErdosProblems/Hlow/H2.lean#L265)


<a id="node-a8923f7bd4ae4b71"></a>
## C6

SOURCE-DOCUMENTED: **Two-bit closed form.** Past two thirds of the row the truncated Mersenne weight is exactly a sum of two powers of two.

Class: infrastructure. Interpretation: source_structural_family. Prior-art assessment: not_assessed.

Scope: This machine-derived family proves exact source linkage and shared proposition shape only. It is not a reviewed mathematical paraphrase, a novelty claim, or evidence that different family members are logically equivalent.

- Lean declaration: [truncatedMersenneWeight_late](../../ErdosProblems/Rem/C6.lean#L159)


<a id="node-19b7c586fa69dede"></a>
## T1

SOURCE-STRUCTURAL FAMILY: 1 theorem/lemma declaration(s) in `ErdosProblems/Three/T1.lean` share the normalized Lean proposition schema `{s : ℕ} (hs : <num> ≤ s) : <num> * seamSubsetTarget s + <num> * <num> ^ s = <num> ^ s`.

Class: infrastructure. Interpretation: source_structural_family. Prior-art assessment: not_assessed.

Scope: This machine-derived family proves exact source linkage and shared proposition shape only. It is not a reviewed mathematical paraphrase, a novelty claim, or evidence that different family members are logically equivalent.

- Lean declaration: [two_mul_seamSubsetTarget](../../ErdosProblems/Three/T1.lean#L300)


<a id="node-31ab2547112660e9"></a>
## D4

SOURCE-DOCUMENTED: **PROVED CONDITIONAL.** The `{3,5}` auxiliary ratchet gives a contradiction from `hright`, `hlanding`, and the stated finite support hypothesis, without using the parity rank. Direct evaluation finds no `hlanding` instance in `s ∈ [5,102]`, so this theorem excludes no audited class.

Class: infrastructure. Interpretation: source_structural_family. Prior-art assessment: not_assessed.

Scope: This machine-derived family proves exact source linkage and shared proposition shape only. It is not a reviewed mathematical paraphrase, a novelty claim, or evidence that different family members are logically equivalent.

- Lean declaration: [cof35_allRight_landingExcess_two_impossible](../../ErdosProblems/Skip/D4.lean#L578)


<a id="node-7d7dc4dabbeb89d9"></a>
## EndpointWeightedPrivateSupport

SOURCE-DOCUMENTED: Adding that complementary projection advances the Euclidean quotient by exactly one. This is the natural-number form of the distance from `T / R` to its next integer.

Class: infrastructure. Interpretation: source_structural_family. Prior-art assessment: not_assessed.

Scope: This machine-derived family proves exact source linkage and shared proposition shape only. It is not a reviewed mathematical paraphrase, a novelty claim, or evidence that different family members are logically equivalent.

- Lean declaration: [add_complementaryProjectedResidue_eq_succ_div_mul](../../ErdosProblems/Erdos68/EndpointWeightedPrivateSupport.lean#L1928)


<a id="node-519361900d76ef21"></a>
## H1

SOURCE-DOCUMENTED: The half-zone correction is a multiple of `21`, so the gap identity does divide exactly. Consequently **no contradiction can be extracted from divisibility by `21`** (or by `3`, or by `7`): the correction is congruent to zero for every half-zone rank, unconditionally.

Class: infrastructure. Interpretation: source_structural_family. Prior-art assessment: not_assessed.

Scope: This machine-derived family proves exact source linkage and shared proposition shape only. It is not a reviewed mathematical paraphrase, a novelty claim, or evidence that different family members are logically equivalent.

- Lean declaration: [twentyOne_dvd_halfGapCorrection](../../ErdosProblems/Half/H1.lean#L439)


<a id="node-59ed416f8b7f1d3e"></a>
## HalfCylinderIntegerGreedy

SOURCE-STRUCTURAL FAMILY: 1 theorem/lemma declaration(s) in `Erdos249257/HalfCylinderIntegerGreedy.lean` share the normalized Lean proposition schema `{s : ℕ} {P : Finset ℕ} (hbelow : ∀ d ∈ P, <num> ≤ d ∧ d < s) : stemTruncatedSum s P = ∑ d ∈ P, truncatedMersenneWeight s d`.

Class: infrastructure. Interpretation: source_structural_family. Prior-art assessment: not_assessed.

Scope: This machine-derived family proves exact source linkage and shared proposition shape only. It is not a reviewed mathematical paraphrase, a novelty claim, or evidence that different family members are logically equivalent.

- Lean declaration: [stemTruncatedSum_eq_sum_support](../../Erdos249257/HalfCylinderIntegerGreedy.lean#L769)


<a id="node-072d9f517d90409b"></a>
## PrimeZeroBranch

SOURCE-DOCUMENTED: The complete canonical prime-power modulus survives at both consecutive reduced-denominator endpoints.

Class: infrastructure. Interpretation: source_structural_family. Prior-art assessment: not_assessed.

Scope: This machine-derived family proves exact source linkage and shared proposition shape only. It is not a reviewed mathematical paraphrase, a novelty claim, or evidence that different family members are logically equivalent.

- Lean declaration: [factorialGapLargePrefixPrivatePowerModulus_two_step_den_anchors](../../ErdosProblems/Erdos68/PrimeZeroBranch.lean#L1723)


<a id="node-448684ffeb420891"></a>
## AngleB1

SOURCE-STRUCTURAL FAMILY: 1 theorem/lemma declaration(s) in `ErdosProblems/Lift/AngleB1.lean` share the normalized Lean proposition schema `(s : ℕ) : pulseFloor2<num> (s + <num>) = pulseFloor2<num> s`.

Class: infrastructure. Interpretation: source_structural_family. Prior-art assessment: not_assessed.

Scope: This machine-derived family proves exact source linkage and shared proposition shape only. It is not a reviewed mathematical paraphrase, a novelty claim, or evidence that different family members are logically equivalent.

- Lean declaration: [pulseFloor26_add_period](../../ErdosProblems/Lift/AngleB1.lean#L765)


<a id="node-2e1ee9e14cdff670"></a>
## C6

SOURCE-DOCUMENTED: The greedy never increases the capacity.

Class: infrastructure. Interpretation: source_structural_family. Prior-art assessment: not_assessed.

Scope: This machine-derived family proves exact source linkage and shared proposition shape only. It is not a reviewed mathematical paraphrase, a novelty claim, or evidence that different family members are logically equivalent.

- Lean declaration: [integerGreedyRemainder_le](../../ErdosProblems/Rem/C6.lean#L82)


<a id="node-58f4c5a706671683"></a>
## AngleA1

SOURCE-STRUCTURAL FAMILY: 1 theorem/lemma declaration(s) in `ErdosProblems/Lift/AngleA1.lean` share the normalized Lean proposition schema `(L : ℕ) : ∑ j ∈ Finset.range L, (<num> : ℤ) ^ j = <num> ^ L - <num>`.

Class: infrastructure. Interpretation: source_structural_family. Prior-art assessment: not_assessed.

Scope: This machine-derived family proves exact source linkage and shared proposition shape only. It is not a reviewed mathematical paraphrase, a novelty claim, or evidence that different family members are logically equivalent.

- Lean declaration: [sum_two_pow](../../ErdosProblems/Lift/AngleA1.lean#L440)


<a id="node-213caae63a0cf7f7"></a>
## SuffixCylinderThreshold

SOURCE-STRUCTURAL FAMILY: 8 theorem/lemma declaration(s) in `Erdos249257/SuffixCylinderThreshold.lean` share the normalized Lean proposition schema `: HasDepth13BasePrefix stage2<num>`.

Class: infrastructure. Interpretation: source_structural_family. Prior-art assessment: not_assessed.

Scope: This machine-derived family proves exact source linkage and shared proposition shape only. It is not a reviewed mathematical paraphrase, a novelty claim, or evidence that different family members are logically equivalent.

- Lean declaration: [stage20_hasDepth13BasePrefix](../../Erdos249257/SuffixCylinderThreshold.lean#L301)
- Lean declaration: [stage21_hasDepth13BasePrefix](../../Erdos249257/SuffixCylinderThreshold.lean#L306)
- Lean declaration: [stage22_hasDepth13BasePrefix](../../Erdos249257/SuffixCylinderThreshold.lean#L311)
- Lean declaration: [stage23_hasDepth13BasePrefix](../../Erdos249257/SuffixCylinderThreshold.lean#L316)
- Lean declaration: [stage24_hasDepth13BasePrefix](../../Erdos249257/SuffixCylinderThreshold.lean#L321)
- Lean declaration: [stage25_hasDepth13BasePrefix](../../Erdos249257/SuffixCylinderThreshold.lean#L326)
- Lean declaration: [stage26_hasDepth13BasePrefix](../../Erdos249257/SuffixCylinderThreshold.lean#L331)
- Lean declaration: [stage27_hasDepth13BasePrefix](../../Erdos249257/SuffixCylinderThreshold.lean#L336)


<a id="node-9eaad7885bca5df9"></a>
## CampbellShiftSynchronization

SOURCE-DOCUMENTED: The shifted-zero producer forces infinitely many actual skips.

Class: infrastructure. Interpretation: source_structural_family. Prior-art assessment: not_assessed.

Scope: This machine-derived family proves exact source linkage and shared proposition shape only. It is not a reviewed mathematical paraphrase, a novelty claim, or evidence that different family members are logically equivalent.

- Lean declaration: [greedyMersenneSkippedSupport_infinite_of_shiftWindowZero](../../Erdos249257/CampbellShiftSynchronization.lean#L428)


<a id="node-883bba7aaf684ce5"></a>
## BooleanMobiusGlobalRepair

SOURCE-STRUCTURAL FAMILY: 1 theorem/lemma declaration(s) in `Erdos249257/BooleanMobiusGlobalRepair.lean` share the normalized Lean proposition schema `{M d : ℕ} (hd : <num> ≤ d) : localMersenneFraction M d < <num>`.

Class: infrastructure. Interpretation: source_structural_family. Prior-art assessment: not_assessed.

Scope: This machine-derived family proves exact source linkage and shared proposition shape only. It is not a reviewed mathematical paraphrase, a novelty claim, or evidence that different family members are logically equivalent.

- Lean declaration: [localMersenneFraction_lt_one](../../Erdos249257/BooleanMobiusGlobalRepair.lean#L202)


<a id="node-47a47e0647cbbd99"></a>
## EndpointWeightedPrivateSupport

SOURCE-DOCUMENTED: The private modulus divides the common-denominator multiplier of the distinguished base.

Class: infrastructure. Interpretation: source_structural_family. Prior-art assessment: not_assessed.

Scope: This machine-derived family proves exact source linkage and shared proposition shape only. It is not a reviewed mathematical paraphrase, a novelty claim, or evidence that different family members are logically equivalent.

- Lean declaration: [privateModulus_dvd_endpointDenominatorLcm_div_base](../../ErdosProblems/Erdos68/EndpointWeightedPrivateSupport.lean#L1564)


<a id="node-05a29823d05cdd68"></a>
## H1

SOURCE-DOCUMENTED: The half-zone correction is strictly smaller than one further scaled dyadic gap. This is the analogue of `exactLateGap_correction_lt_three_mul_gap`.

Class: infrastructure. Interpretation: source_structural_family. Prior-art assessment: not_assessed.

Scope: This machine-derived family proves exact source linkage and shared proposition shape only. It is not a reviewed mathematical paraphrase, a novelty claim, or evidence that different family members are logically equivalent.

- Lean declaration: [halfGapCorrection_lt_twentyOne_mul_gap](../../ErdosProblems/Half/H1.lean#L284)


<a id="node-a312e70016a7f7ca"></a>
## TotientParityCoboundaryCountermodel

SOURCE-DOCUMENTED: The countermodel's dyadic value is rational.

Class: infrastructure. Interpretation: source_structural_family. Prior-art assessment: not_assessed.

Scope: This machine-derived family proves exact source linkage and shared proposition shape only. It is not a reviewed mathematical paraphrase, a novelty claim, or evidence that different family members are logically equivalent.

- Lean declaration: [parityCoboundaryWeight_not_irrational](../../Erdos249257/TotientParityCoboundaryCountermodel.lean#L541)


<a id="node-99d2c62875b895a0"></a>
## AngleA1

SOURCE-DOCUMENTED: **PROVED historical-frontier corollary.** A diagonal certificate at `t = 67` implies one at every `t ≤ 67`. The name records the former frontier; the current finite band extends through `t = 82`.

Class: infrastructure. Interpretation: source_structural_family. Prior-art assessment: not_assessed.

Scope: This machine-derived family proves exact source linkage and shared proposition shape only. It is not a reviewed mathematical paraphrase, a novelty claim, or evidence that different family members are logically equivalent.

- Lean declaration: [frontier_certificate_implies_all_seed](../../ErdosProblems/Lift/AngleA1.lean#L732)


