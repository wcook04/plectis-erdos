# structural_112: Exact source-structural proposition families

[All problems and zones](BROWSER.md)

<a id="node-2872c67a5dc77035"></a>
## structural::adfb5f0fd2a43a0fb4bf

SOURCE-DOCUMENTED: **The `k`-fold decomposition.** A cell at the multiplied shift `k·h` is the sum of `k` cells at the certified shift `h`, at the consecutive base points `N, N+h, …, N+(k-1)h`. This is the base-point counterpart of the offset dilation `diagCoeff_lift_coprime` of `Recon249`. That law covers `⌊L'/p⌋` of the `L'` offsets exactly; this one covers all of them, at the price of `k` unknown summands instead of one.

Class: infrastructure. Interpretation: source_structural_family. Prior-art assessment: not_assessed.

Scope: This machine-derived family proves exact source linkage and shared proposition shape only. It is not a reviewed mathematical paraphrase, a novelty claim, or evidence that different family members are logically equivalent.

- Lean declaration: [windowDiscrepancy_mul_shift](../../ErdosProblems/Lift/AngleA3.lean#L178)


<a id="node-56f550cd93243d90"></a>
## structural::ae0d260e4cf9b548516c

SOURCE-DOCUMENTED: The residual `T1` refutes the ceiling with, one rank later. `524419` at rank `7` becomes `261247` at rank `8`, and `2 ^ 18 = 262144`.

Class: infrastructure. Interpretation: source_structural_family. Prior-art assessment: not_assessed.

Scope: This machine-derived family proves exact source linkage and shared proposition shape only. It is not a reviewed mathematical paraphrase, a novelty claim, or evidence that different family members are logically equivalent.

- Lean declaration: [seamResidualUpto_thirteen_eight](../../ErdosProblems/Decl/D4.lean#L779)


<a id="node-a03f337edacd7f53"></a>
## structural::ae20b2a81ead88b42efe

SOURCE-DOCUMENTED: **No third category for an old prime-power.** A modulus surviving exact denominator deletion still divides the later primitive denominator, so any overlap between the survivor and the later Sylvester factor `a - 1` is forced into the later centred error. Either an old factor is deleted — and paid for quadratically by the conservation law above — or it stays visible.

Class: infrastructure. Interpretation: source_structural_family. Prior-art assessment: not_assessed.

Scope: This machine-derived family proves exact source linkage and shared proposition shape only. It is not a reviewed mathematical paraphrase, a novelty claim, or evidence that different family members are logically equivalent.

- Lean declaration: [survivor_overlap_dvd_centeredError](../../ErdosProblems/Erdos243/RepairEntropy.lean#L138)


<a id="node-43f8b621d0c0ba6b"></a>
## structural::ae2e6ea15d91692ca9f5

SOURCE-DOCUMENTED: **One canonical residue gap excludes a full divisor class.** If the reduced denominator of `r` divides `2^c * v` and one full-Mersenne factorization at the canonical basepoint `c` has a centered residue gap, then the totient series is not `r`. This turns any certified pointwise gap into a genuine finite denominator exclusion; it makes no cofinal or irrationality claim.

Class: infrastructure. Interpretation: source_structural_family. Prior-art assessment: not_assessed.

Scope: This machine-derived family proves exact source linkage and shared proposition shape only. It is not a reviewed mathematical paraphrase, a novelty claim, or evidence that different family members are logically equivalent.

- Lean declaration: [totient_series_ne_rat_of_fullMersenneCanonicalBasepointResidueGap_of_den_dvd](../../ErdosProblems/Erdos249/CyclotomicAnchoredKill.lean#L2898)


<a id="node-eee48844ca9c3df4"></a>
## structural::ae4215ae9901ff91e6db

SOURCE-STRUCTURAL FAMILY: 1 theorem/lemma declaration(s) in `Erdos249257/HalfCylinderFloorErrorReset.lean` share the normalized Lean proposition schema `{s : ℕ} (hs : <num> ≤ s) (b : SeamRowWord s) : seamWordSupport (b.extend true) = insert s (seamWordSupport b)`.

Class: infrastructure. Interpretation: source_structural_family. Prior-art assessment: not_assessed.

Scope: This machine-derived family proves exact source linkage and shared proposition shape only. It is not a reviewed mathematical paraphrase, a novelty claim, or evidence that different family members are logically equivalent.

- Lean declaration: [seamWordSupport_extend_true](../../Erdos249257/HalfCylinderFloorErrorReset.lean#L85)


<a id="node-a72554c7451d2734"></a>
## structural::ae54056c98dab9049080

SOURCE-DOCUMENTED: **Coverage theorem.** The body of `G100` fires at *every* scale `1 ≤ t ≤ 66`, not merely at the 29 scales where a certificate is recorded. The 37 scales `10, 12, 14, 15, 18, 20, 21, 22, 24, 26, 28, 30, 33, …, 65, 66` carry no certificate anywhere in the corpus and are nonetheless instances.

Class: infrastructure. Interpretation: source_structural_family. Prior-art assessment: not_assessed.

Scope: This machine-derived family proves exact source linkage and shared proposition shape only. It is not a reviewed mathematical paraphrase, a novelty claim, or evidence that different family members are logically equivalent.

- Lean declaration: [coneCell_of_le_66](../../ErdosProblems/DemandLedger/edges/Discharge2_G100.lean#L212)


<a id="node-f9b47b05769180df"></a>
## structural::ae5aa09f87f4657a9caf

SOURCE-DOCUMENTED: Exact shift law for the multiplicative rational control.

Class: infrastructure. Interpretation: source_structural_family. Prior-art assessment: not_assessed.

Scope: This machine-derived family proves exact source linkage and shared proposition shape only. It is not a reviewed mathematical paraphrase, a novelty claim, or evidence that different family members are logically equivalent.

- Lean declaration: [idCoeff_binaryCoeffTail_sub](../../Erdos249257/TotientTailCarryPeriod.lean#L328)


<a id="node-4bd3536cd7300c58"></a>
## structural::ae6190bf3829dc7b9b38

SOURCE-STRUCTURAL FAMILY: 2 theorem/lemma declaration(s) in `ErdosProblems/Skip/D4.lean` share the normalized Lean proposition schema `: (<num> / <num> : ℝ) ∈ mersenneAchievementSet ∨ ∃ S : ℕ, <num> ≤ S ∧ ∀ D : ℕ, S ≤ D → (∀ s : ℕ, D + <num> ≤ s → seamGreedyWord (s + <num>) = (seamGreedyWord s).extend true) → Recon2<num>.seamExcess (D + <num>) = <num> → False`.

Class: infrastructure. Interpretation: source_structural_family. Prior-art assessment: not_assessed.

Scope: This machine-derived family proves exact source linkage and shared proposition shape only. It is not a reviewed mathematical paraphrase, a novelty claim, or evidence that different family members are logically equivalent.

- Lean declaration: [half_mem_or_allRight_landingExcess_two_impossible](../../ErdosProblems/Skip/D4.lean#L207)
- Lean declaration: [cof35_half_mem_or_allRight_impossible](../../ErdosProblems/Skip/D4.lean#L676)


<a id="node-a30478fd74565349"></a>
## structural::ae683b8d42210d1fade1

SOURCE-STRUCTURAL FAMILY: 1 theorem/lemma declaration(s) in `Erdos249257/PrimePowerJumpDynamics.lean` share the normalized Lean proposition schema `{r p m : ℕ} (hpr : ¬ p ∣ r) (hm : m ∣ r) : ¬ p ∣ m`.

Class: infrastructure. Interpretation: source_structural_family. Prior-art assessment: not_assessed.

Scope: This machine-derived family proves exact source linkage and shared proposition shape only. It is not a reviewed mathematical paraphrase, a novelty claim, or evidence that different family members are logically equivalent.

- Lean declaration: [prime_not_dvd_divisor](../../Erdos249257/PrimePowerJumpDynamics.lean#L246)


<a id="node-851bccbb19c3f8c9"></a>
## structural::ae69c2b6f7ba57b62446

SOURCE-DOCUMENTED: Hence the Möbius transform of every exact carry quotient is Boolean.

Class: infrastructure. Interpretation: source_structural_family. Prior-art assessment: not_assessed.

Scope: This machine-derived family proves exact source linkage and shared proposition shape only. It is not a reviewed mathematical paraphrase, a novelty claim, or evidence that different family members are logically equivalent.

- Lean declaration: [mobius_carryQuotient_boolean](../../Erdos249257/BooleanMobiusCarry.lean#L814)


<a id="node-3e388aad184798d1"></a>
## structural::ae7d3cfde8c11f9ecdfc

SOURCE-STRUCTURAL FAMILY: 1 theorem/lemma declaration(s) in `ErdosProblems/FreePosition/FreeKill64FortyThreeAO.lean` share the normalized Lean proposition schema `{M : Type*} [Monoid M] (a : M) (n : ℕ) : fortyThreeAOFastPow a n = a ^ n`.

Class: infrastructure. Interpretation: source_structural_family. Prior-art assessment: not_assessed.

Scope: This machine-derived family proves exact source linkage and shared proposition shape only. It is not a reviewed mathematical paraphrase, a novelty claim, or evidence that different family members are logically equivalent.

- Lean declaration: [fortyThreeAOFastPow_eq_pow](../../ErdosProblems/FreePosition/FreeKill64FortyThreeAO.lean#L16)


<a id="node-fa2e22dd439f88e1"></a>
## structural::ae95ce03b3189c932b71

SOURCE-DOCUMENTED: All distinct killed prime labels lie in the common killed/transition factor. Any nontrivial defect therefore records excess multiplicity, not an entirely missed killed support prime.

Class: infrastructure. Interpretation: source_structural_family. Prior-art assessment: not_assessed.

Scope: This machine-derived family proves exact source linkage and shared proposition shape only. It is not a reviewed mathematical paraphrase, a novelty claim, or evidence that different family members are logically equivalent.

- Lean declaration: [factorialGapKilledPrivatePrimeModulus_dvd_killedTransitionGcd](../../ErdosProblems/Erdos68/PrimeZeroBranch.lean#L4082)


<a id="node-e55ea33171c92061"></a>
## structural::ae9bb7a4a89a9a2c57a7

SOURCE-DOCUMENTED: The sharpened form of the edge: `G093` supplies a cone kill at **every** scale, not merely at cofinally many. (Immediate from `e_G093_G101` and `G101_iff_forall_scale`; recorded because it is the statement one actually wants when feeding the cone machinery.)

Class: infrastructure. Interpretation: source_structural_family. Prior-art assessment: not_assessed.

Scope: This machine-derived family proves exact source linkage and shared proposition shape only. It is not a reviewed mathematical paraphrase, a novelty claim, or evidence that different family members are logically equivalent.

- Lean declaration: [G093_gives_cone_kill_at_every_scale](../../ErdosProblems/DemandLedger/edges/ClusterC.lean#L73)


<a id="node-3b0ae96dd4c42488"></a>
## structural::ae9e5c3c0b7c7aeb2b1d

SOURCE-DOCUMENTED: Collapsed: `ρ s < 2 ^ (s+1) + 2 ^ (2*s-2*b+1)` where `b` is the last declined rank. (This is the rank-level analogue of `RemC6`'s `seamIntegerGreedyRemainder_lt_of_largest_skip`, obtained here without splitting the weight word and without any lateness hypothesis.)

Class: infrastructure. Interpretation: source_structural_family. Prior-art assessment: not_assessed.

Scope: This machine-derived family proves exact source linkage and shared proposition shape only. It is not a reviewed mathematical paraphrase, a novelty claim, or evidence that different family members are logically equivalent.

- Lean declaration: [seamRemainder_lt_two_pow_succ_add](../../ErdosProblems/Decl/D2.lean#L273)


<a id="node-0b51dc7d93d7c7a9"></a>
## structural::aea852e1580e3243fca9

SOURCE-DOCUMENTED: The greedy word, computed from the actual truncated Mersenne weights.

Class: infrastructure. Interpretation: source_structural_family. Prior-art assessment: not_assessed.

Scope: This machine-derived family proves exact source linkage and shared proposition shape only. It is not a reviewed mathematical paraphrase, a novelty claim, or evidence that different family members are logically equivalent.

- Lean declaration: [greedy_word](../../ErdosProblems/Bit/Corr1.lean#L545)


<a id="node-a969c8d7be5d12fc"></a>
## structural::aeb67d1c2028c5102934

SOURCE-DOCUMENTED: A uniform `89/100` block gap for the infinite orbit yields the finite `9/10` gap after choosing one truncation depth for the whole block.

Class: infrastructure. Interpretation: source_structural_family. Prior-art assessment: not_assessed.

Scope: This machine-derived family proves exact source linkage and shared proposition shape only. It is not a reviewed mathematical paraphrase, a novelty claim, or evidence that different family members are logically equivalent.

- Lean declaration: [irrational_totient_series_of_tailOrbitBlockGap](../../ErdosProblems/Erdos249/TotientStrictPrimeEscape.lean#L96)


<a id="node-94121ef5145c993b"></a>
## structural::aeb798288999700101f2

SOURCE-DOCUMENTED: The seam subset target is even.

Class: infrastructure. Interpretation: source_structural_family. Prior-art assessment: not_assessed.

Scope: This machine-derived family proves exact source linkage and shared proposition shape only. It is not a reviewed mathematical paraphrase, a novelty claim, or evidence that different family members are logically equivalent.

- Lean declaration: [seamSubsetTarget_mod_two](../../ErdosProblems/Half/H3.lean#L218)


<a id="node-0e46a97ddf52c196"></a>
## structural::aecfe68c4f08f2a6a449

SOURCE-STRUCTURAL FAMILY: 2 theorem/lemma declaration(s) in `ErdosProblems/Bit/Corr2.lean` share the normalized Lean proposition schema `{s d : ℕ} (hd : <num> ≤ d) (h : d ∣ <num> * s + <num>) : rowCarry s d = <num>`.

Class: infrastructure. Interpretation: source_structural_family. Prior-art assessment: not_assessed.

Scope: This machine-derived family proves exact source linkage and shared proposition shape only. It is not a reviewed mathematical paraphrase, a novelty claim, or evidence that different family members are logically equivalent.

- Lean declaration: [rowCarry_eq_two](../../ErdosProblems/Bit/Corr2.lean#L234)
- Lean declaration: [rowCarry_eq_one](../../ErdosProblems/Bit/Corr2.lean#L248)


<a id="node-c75a01655f569011"></a>
## structural::aed2c8563604336a2f6a

SOURCE-DOCUMENTED: Exhaustive asymptotic split. Either the empty-block branch already proves membership, or every sufficiently large doubling block is hit. Thus the correction route never needs the formerly stated all-depth hit hypothesis.

Class: infrastructure. Interpretation: source_structural_family. Prior-art assessment: not_assessed.

Scope: This machine-derived family proves exact source linkage and shared proposition shape only. It is not a reviewed mathematical paraphrase, a novelty claim, or evidence that different family members are logically equivalent.

- Lean declaration: [one_div_twenty_one_mem_or_eventually_hits_doublingBlocks](../../Erdos249257/BooleanMobiusCarry.lean#L3474)


<a id="node-f3b56c4b7a2d3342"></a>
## structural::aed362fd39d398e9a07d

SOURCE-DOCUMENTED: `K` really is of order `s / 3`.

Class: infrastructure. Interpretation: source_structural_family. Prior-art assessment: not_assessed.

Scope: This machine-derived family proves exact source linkage and shared proposition shape only. It is not a reviewed mathematical paraphrase, a novelty claim, or evidence that different family members are logically equivalent.

- Lean declaration: [runNeeded_lower_bound](../../ErdosProblems/Bit/Corr3.lean#L140)


<a id="node-a60c6f8b7e245a30"></a>
## structural::aed74137004261fe5db7

SOURCE-DOCUMENTED: Any polynomial upper bound on the `n`th prime implies convergence of the normalized prime series.

Class: infrastructure. Interpretation: source_structural_family. Prior-art assessment: not_assessed.

Scope: This machine-derived family proves exact source linkage and shared proposition shape only. It is not a reviewed mathematical paraphrase, a novelty claim, or evidence that different family members are logically equivalent.

- Lean declaration: [summable_primeDyadicTerm_of_polynomial_growth](../../ErdosProblems/Erdos251/PrimeGapDyadicTail.lean#L214)


<a id="node-18a21c421cbe7410"></a>
## structural::aed9edd9f71acff01eac

SOURCE-DOCUMENTED: Finite coefficient windows converge to the complete normalized coefficient tail.

Class: infrastructure. Interpretation: source_structural_family. Prior-art assessment: not_assessed.

Scope: This machine-derived family proves exact source linkage and shared proposition shape only. It is not a reviewed mathematical paraphrase, a novelty claim, or evidence that different family members are logically equivalent.

- Lean declaration: [tendsto_finiteCoeffWindow_atTop](../../Erdos249257/HalfCylinderFiniteShadow.lean#L1167)


<a id="node-2f8d2b33a93dd046"></a>
## structural::aeeef8497f5de73e2229

SOURCE-DOCUMENTED: **Sharpness.** The capacity `527` satisfies `hhigh` at `(s, d) = (7, 5)`, yet the late greedy leaves `267 > 2 ^ 8 = 2 ^ (s + 1)`. It sits inside the slack `4 ^ (s - d) = 16` that `lateGreedy_lt_of_high` allows, and it fails `hlow` (`527 % 2 ^ 8 = 15 < 20`), as it must.

Class: infrastructure. Interpretation: source_structural_family. Prior-art assessment: not_assessed.

Scope: This machine-derived family proves exact source linkage and shared proposition shape only. It is not a reviewed mathematical paraphrase, a novelty claim, or evidence that different family members are logically equivalent.

- Lean declaration: [sharpness_seven_five](../../ErdosProblems/Decl/D4.lean#L426)


<a id="node-82975ac0ff6e1ca9"></a>
## structural::aeff9f800f928206c325

SOURCE-STRUCTURAL FAMILY: 1 theorem/lemma declaration(s) in `Erdos249257/CertificateKernel.lean` share the normalized Lean proposition schema `(d L A B Q b : Nat) (M C q : Nat → Nat) (hLpos : <num> < L) (hA : A ≠ <num>) (h_dvd : d ∣ L) (hQpos : <num> < Q) (hQ : Q = B / Nat.gcd A B) (hpow : <num> ≤ b ^ d) (hmod : b ^ d ≡ <num> [MOD Q]) (h_component_factor : ∀ p, Nat.Prime p → p ∣ L → B = M p * C p) (h_component_eq : ∀ p, Nat.Prime p → p ∣ L → C p = b ^ (L / p) - <num>)`.

Class: infrastructure. Interpretation: source_structural_family. Prior-art assessment: not_assessed.

Scope: This machine-derived family proves exact source linkage and shared proposition shape only. It is not a reviewed mathematical paraphrase, a novelty claim, or evidence that different family members are logically equivalent.

- Lean declaration: [modEq_certificate_implies_no_prime_drop](../../Erdos249257/CertificateKernel.lean#L264)


<a id="node-770349103dcc49ea"></a>
## structural::af0231a806b0487af222

SOURCE-STRUCTURAL FAMILY: 1 theorem/lemma declaration(s) in `Erdos249257/GreedyAchievementSet.lean` share the normalized Lean proposition schema `@[simp] theorem greedyMersenneRemainderRat_zero (x : ℚ) : greedyMersenneRemainderRat x <num> = x`.

Class: infrastructure. Interpretation: source_structural_family. Prior-art assessment: not_assessed.

Scope: This machine-derived family proves exact source linkage and shared proposition shape only. It is not a reviewed mathematical paraphrase, a novelty claim, or evidence that different family members are logically equivalent.

- Lean declaration: [greedyMersenneRemainderRat_zero](../../Erdos249257/GreedyAchievementSet.lean#L1048)


<a id="node-63747bc6b9dd7e23"></a>
## structural::af3708f503cce3d12f80

SOURCE-DOCUMENTED: Selecting one new exponent adds exactly its weight.

Class: infrastructure. Interpretation: source_structural_family. Prior-art assessment: not_assessed.

Scope: This machine-derived family proves exact source linkage and shared proposition shape only. It is not a reviewed mathematical paraphrase, a novelty claim, or evidence that different family members are logically equivalent.

- Lean declaration: [positiveMersenneSupportValue_insert](../../Erdos249257/HalfCutLocator.lean#L144)


<a id="node-3c51eff7a4c402ea"></a>
## structural::af49c8a58938b41ab852

SOURCE-DOCUMENTED: A root-free Euclidean coefficient disk implies the L2 selector whenever all moment vectors lie in the closed unit disk.

Class: infrastructure. Interpretation: source_structural_family. Prior-art assessment: not_assessed.

Scope: This machine-derived family proves exact source linkage and shared proposition shape only. It is not a reviewed mathematical paraphrase, a novelty claim, or evidence that different family members are logically equivalent.

- Lean declaration: [exists_two_tails_norm_lt_one_of_coeff_L2_budget](../../ErdosProblems/Erdos1041/TetranomialL2Selector.lean#L159)


<a id="node-af56d397f188e6ae"></a>
## structural::af64df4429431b259b8b

SOURCE-STRUCTURAL FAMILY: 1 theorem/lemma declaration(s) in `Erdos249257/CertificateKernel.lean` share the normalized Lean proposition schema `(b L e : Nat) (heL : e ∣ L) : b ^ L - <num> = ((b ^ L - <num>) / (b ^ e - <num>)) * (b ^ e - <num>)`.

Class: infrastructure. Interpretation: source_structural_family. Prior-art assessment: not_assessed.

Scope: This machine-derived family proves exact source linkage and shared proposition shape only. It is not a reviewed mathematical paraphrase, a novelty claim, or evidence that different family members are logically equivalent.

- Lean declaration: [pow_sub_one_component_factor](../../Erdos249257/CertificateKernel.lean#L414)


<a id="node-723de4b64edc69da"></a>
## structural::af6b3a97c652389bc537

SOURCE-DOCUMENTED: A nonzero affine slope has a root modulo any larger prime.

Class: infrastructure. Interpretation: source_structural_family. Prior-art assessment: not_assessed.

Scope: This machine-derived family proves exact source linkage and shared proposition shape only. It is not a reviewed mathematical paraphrase, a novelty claim, or evidence that different family members are logically equivalent.

- Lean declaration: [exists_affine_root_mod_prime](../../Erdos249257/TotientMahlerDefect.lean#L457)


<a id="node-a596cd1c7fb56376"></a>
## structural::af90ba7cf6518554246d

SOURCE-DOCUMENTED: **Iterated spend of the odd boundary channel.** The odd-boundary arm of `infinite_coeff_channel_dichotomy_of_producerCarry_eq_neg_one` contributes at least two distinct weight-two coefficients to the same complete dyadic tail, at the first two positive multiples of its selected divisor. The even arm retains the two distinct divisor channels already forced by the residual pulse. Thus neither arm is reduced to a single isolated coefficient bump.

Class: infrastructure. Interpretation: source_structural_family. Prior-art assessment: not_assessed.

Scope: This machine-derived family proves exact source linkage and shared proposition shape only. It is not a reviewed mathematical paraphrase, a novelty claim, or evidence that different family members are logically equivalent.

- Lean declaration: [iterated_weighted_tail_channel_dichotomy_of_producerCarry_eq_neg_one](../../Erdos249257/HalfCylinderMiddleCarryLowerBound.lean#L1284)


<a id="node-2b8aa4ea7c4a1c7f"></a>
## structural::af94343def5c44087f7e

SOURCE-STRUCTURAL FAMILY: 1 theorem/lemma declaration(s) in `Erdos249257/HalfCylinderResetDeficitEscape.lean` share the normalized Lean proposition schema `{s : ℕ} (hs : <num> ≤ s) : (seamAdjacentCut s hs).belowPulse ≤ <num> * (s - <num>)`.

Class: infrastructure. Interpretation: source_structural_family. Prior-art assessment: not_assessed.

Scope: This machine-derived family proves exact source linkage and shared proposition shape only. It is not a reviewed mathematical paraphrase, a novelty claim, or evidence that different family members are logically equivalent.

- Lean declaration: [seamAdjacentCut_belowPulse_le](../../Erdos249257/HalfCylinderResetDeficitEscape.lean#L59)


<a id="node-d3ee65eeaf6b1e83"></a>
## structural::af96bb2371f6ff5eaa63

SOURCE-DOCUMENTED: **PROVED (finite auxiliary calculation).** Each of the `2730` joint phases has `cofRun D 3 = 0`. This is a statement about the budget formed by treating `cofRanks` as certified support. It does not prove that the concrete greedy support contains those ranks or that the concrete survivor set is empty.

Class: infrastructure. Interpretation: source_structural_family. Prior-art assessment: not_assessed.

Scope: This machine-derived family proves exact source linkage and shared proposition shape only. It is not a reviewed mathematical paraphrase, a novelty claim, or evidence that different family members are logically equivalent.

- Lean declaration: [cofRatchet_finite_core](../../ErdosProblems/Lift/AngleB2.lean#L309)


