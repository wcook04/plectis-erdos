import Erdos257PeriodNoncollapse.BooleanMobiusCarry
import Erdos257PeriodNoncollapse.HalfCutLocator

/-!
# End-to-end conjunctions in the long-record catalogue

Uncompiled R7 candidates. These reuse proved source declarations, but the new
combined statements have not been elaborated here. Their exact status and
remaining nonmathematical/numerical clauses are recorded per paper environment
in theorem_coverage.json. No source theorem is promoted past its hypotheses.
-/

noncomputable section
namespace ErdosProblems.Erdos257.PaperCompleteR7
open Erdos257PeriodNoncollapse

/-- Long thm:bmc, including the reconstruction of the particular input
support, not merely existence of some unrelated rational representation. -/
theorem long_boolean_mobius_correspondence (p : ℤ) (q : ℕ) (hq : 0 < q) :
    ((∃ A : Set ℕ, 0 ∉ A ∧ (∃ a : ℕ, 0 < a ∧ a ∈ A) ∧
       erdosSupportSeries 2 A = (p : ℝ) / (q : ℝ)) ↔
      ∃ U : ℕ → ℤ, BooleanMobiusCarryCertificate p q U) ∧
    (∀ A : Set ℕ, 0 ∉ A → (∃ a : ℕ, 0 < a ∧ a ∈ A) →
      erdosSupportSeries 2 A = (p : ℝ) / (q : ℝ) →
      ∃ U : ℕ → ℤ, BooleanMobiusCarryCertificate p q U ∧
        {n : ℕ | (ArithmeticFunction.moebius * carryQuotientAF q U) n = 1} = A) ∧
    (∀ U : ℕ → ℤ, BooleanMobiusCarryCertificate p q U →
      let A := booleanMobiusSupport (carryQuotientAF q U)
      0 ∉ A ∧ carryQuotientAF q U = supportCoeffAF A ∧
        IsTemperedBinaryOrbit (supportCoeff A) q U ∧
        {n : ℕ | (ArithmeticFunction.moebius * carryQuotientAF q U) n = 1} = A ∧
        erdosSupportSeries 2 A = (p : ℝ) / (q : ℝ)) := by
  exact ⟨exists_normalized_support_fraction_iff_exists_booleanMobiusCarry p q hq,
    fun A h0 hpos hvalue =>
      exists_booleanMobiusCarry_of_support_fraction A h0 hpos p q hq hvalue,
    fun U cert => cert.reconstructsSupport hq⟩

/-- Long thm:greedy-survival: the arbitrary-target iff, the half dichotomy,
and its exact complement, in one proposition. -/
theorem long_greedy_survival_and_fatal_dichotomy (x : ℝ) :
    (x ∈ mersenneAchievementSet ↔ 0 ≤ x ∧
      ∀ n : ℕ, greedyMersenneRemainder x n ≤ mersenneTail n) ∧
    ((1 / 2 : ℝ) ∈ mersenneAchievementSet ∨ ExistsFatalHalfGap) ∧
    (ExistsFatalHalfGap ↔ (1 / 2 : ℝ) ∉ mersenneAchievementSet) := by
  exact ⟨mem_mersenneAchievementSet_iff_greedy_survival x,
    half_mem_mersenneAchievementSet_or_exists_fatal_gap,
    existsFatalHalfGap_iff_half_not_mem_mersenneAchievementSet⟩

/-- Long thm:one-sided: both directions of both claimed tests. -/
theorem long_half_one_sided :
    ((1 / 2 : ℝ) ∉ mersenneAchievementSet ↔ ExistsFatalHalfGap) ∧
    ((1 / 2 : ℝ) ∈ mersenneAchievementSet ↔
      ∀ n : ℕ, greedyMersenneRemainder (1 / 2 : ℝ) n ≤ mersenneTail n) := by
  refine ⟨existsFatalHalfGap_iff_half_not_mem_mersenneAchievementSet.symm, ?_⟩
  simpa using mem_mersenneAchievementSet_iff_greedy_survival (1 / 2 : ℝ)

/-- Long obs:half-controls-universal: only the conditional consequence.
No half-membership witness is asserted or postulated as an axiom. -/
theorem half_membership_requires_infinite_support
    (hhalf : (1 / 2 : ℝ) ∈ mersenneAchievementSet) :
    ∃ A : Set ℕ, A.Infinite ∧ 0 ∉ A ∧
      erdosSupportSeries 2 A = (1 / 2 : ℝ) := by
  classical
  rcases hhalf with ⟨A, h0, hvalue⟩
  have hinf : A.Infinite := by
    by_contra hnot
    have hfin : A.Finite := Set.not_infinite.mp hnot
    have hF0 : 0 ∉ hfin.toFinset := by simpa using h0
    have hne := positiveMersenneSupportValue_coe_finset_ne_half hF0
    have hv : positiveMersenneSupportValue (↑hfin.toFinset : Set ℕ) =
        (1 / 2 : ℝ) := by simpa using hvalue.symm
    exact hne hv
  refine ⟨A, hinf, h0, ?_⟩
  rw [← positiveMersenneSupportValue_eq_erdosSupportSeries A]
  exact hvalue.symm

/-- Long thm:fatal-absorbing: propagation, forced later takes and the
contrapositive membership consumer, with the actual greedy recurrence. -/
theorem long_fatal_absorption (x : ℝ) (hx : 0 ≤ x) :
    (∀ n : ℕ, GreedyMersenneFatalAt x n →
      ∀ k : ℕ, GreedyMersenneFatalAt x (n + k) ∧
        mersenneWeight (n + k + 1) ≤ greedyMersenneRemainder x (n + k)) ∧
    (∀ n : ℕ, GreedyMersenneFatalAt x n →
      (greedyMersenneSkippedSupport x).Finite) ∧
    ((greedyMersenneSkippedSupport x).Infinite → x ∈ mersenneAchievementSet) := by
  constructor
  · intro n hfatal k
    have hk := greedyMersenneFatalAt_add hfatal k
    exact ⟨hk, (greedyMersenneFatalAt_succ hk).1⟩
  · exact ⟨fun n hfatal => finite_greedyMersenneSkippedSupport_of_fatalAt hfatal,
      mem_mersenneAchievementSet_of_greedySkippedSupport_infinite hx⟩

/-- Long thm:two-channel-cap: the two distinct sufficient conditions. -/
theorem long_two_channel_and_dyadic_caps :
    ((∀ n : ℕ, ¬ mersenneWeight (n + 1) ≤
        greedyMersenneRemainder (1 / 2 : ℝ) n →
      greedyMersenneRemainder (1 / 2 : ℝ) n ≤ halfTwoChannelCap (n + 1)) →
      (1 / 2 : ℝ) ∈ mersenneAchievementSet) ∧
    ((∀ n : ℕ, ¬ mersenneWeight (n + 1) ≤
        greedyMersenneRemainder (1 / 2 : ℝ) n →
      greedyMersenneRemainder (1 / 2 : ℝ) n ≤ halfDyadicCap (n + 1)) →
      (1 / 2 : ℝ) ∈ mersenneAchievementSet) := by
  exact ⟨half_mem_mersenneAchievementSet_of_skipped_twoChannelCap,
    half_mem_mersenneAchievementSet_of_skipped_dyadicCap⟩

/-- Long thm:second-channel: real separation and the exact rational
from-seven consumer; this does not supply separation at the remaining ranks. -/
theorem long_second_channel_consumers :
    ((∀ n : ℕ, 0 < n →
      (1 / 6 : ℝ) + (37 / 56 : ℝ) * ((1 : ℝ) / 2) ^ n ≤
        |greedyMersenneSecondChannelPhase n - 1 / 3|) →
      (1 / 2 : ℝ) ∈ mersenneAchievementSet) ∧
    ((∀ n : ℕ, 7 ≤ n → HalfSecondChannelSeparatedRat n) →
      (1 / 2 : ℝ) ∈ mersenneAchievementSet) := by
  exact ⟨half_mem_mersenneAchievementSet_of_secondChannelSeparation,
    half_mem_mersenneAchievementSet_of_secondChannelSeparationRat_from_seven⟩

/-- Long thm:factorial-twopow-support: both all-base families. -/
theorem long_factorial_and_geometric (b : ℕ) (hb : 2 ≤ b) :
    Irrational (∑' k : ℕ, (1 : ℝ) / ((b : ℝ) ^ (Nat.factorial (k + 1)) - 1)) ∧
    Irrational (∑' k : ℕ, (1 : ℝ) / ((b : ℝ) ^ (2 ^ k) - 1)) := by
  exact ⟨irrational_erdosSum_factorial_support b hb,
    irrational_erdosSum_two_pow_support b hb⟩

/-- Long thm:multiples-support: both the exact identity and its irrationality. -/
theorem long_multiples (b d : ℕ) (hb : 2 ≤ b) (hd : 1 ≤ d) :
    erdosSupportSeries b {n : ℕ | d ∣ n} =
      (∑' k : ℕ, (1 : ℝ) / (((b : ℝ) ^ d) ^ (k + 1) - 1)) ∧
    Irrational (erdosSupportSeries b {n : ℕ | d ∣ n}) := by
  exact ⟨erdosSupportSeries_multiples_eq_pow_base_full_support b d hb hd,
    irrational_erdosSupportSeries_multiples b d hb hd⟩

/-- Mathematical assertions of long thm:residue-odd. The narrative claim
about which class was first released is not a mathematical theorem. -/
theorem long_residue_and_odd (b m c : ℕ) (hb : 2 ≤ b) (hm : 0 < m) :
    Irrational (erdosSupportSeries b {n : ℕ | n % m = c % m}) ∧
    Irrational (erdosSupportSeries b {n : ℕ | Odd n}) := by
  exact ⟨irrational_erdosSupportSeries_residueClass b m c hb hm,
    irrational_erdosSupportSeries_odd b hb⟩

/-- Long thm:signed-periodic: the dichotomy and both one-sided closures.
The period is positive; periodicity alone permits the terminating branch. -/
theorem long_signed_periodic (b m : ℕ) (w : ℕ → ℤ)
    (hb : 2 ≤ b) (hm : 0 < m) (hper : ∀ n : ℕ, w (n + m) = w n) :
    (Irrational (intWeightedErdosSeries b w) ∨
      ∃ (k : ℕ) (z : ℤ), (b : ℝ) ^ k * intWeightedErdosSeries b w = (z : ℝ)) ∧
    (((∀ n : ℕ, 0 < n → 0 ≤ intWeightedCoeff w n) ∨
      (∀ n : ℕ, 0 < n → intWeightedCoeff w n ≤ 0)) →
      (∀ N : ℕ, ∃ n : ℕ, N < n ∧ intWeightedCoeff w n ≠ 0) →
      Irrational (intWeightedErdosSeries b w)) := by
  refine ⟨irrational_or_bpow_mul_eq_intCast_intWeightedErdosSeries_periodic
    b m w hb hm hper, ?_⟩
  intro hsign hne
  rcases hsign with hnonneg | hnonpos
  · exact irrational_intWeightedErdosSeries_periodic_of_coeff_nonneg_of_frequently_ne_zero
      b m w hb hm hper hnonneg hne
  · exact irrational_intWeightedErdosSeries_periodic_of_coeff_nonpos_of_frequently_ne_zero
      b m w hb hm hper hnonpos hne

/-- Long obs:half-regression: all three exact rational/real checkpoints. -/
theorem long_half_regressions :
    (1 / 2 : ℚ) - finiteErdosSum ({2, 3, 6, 7} : Finset ℕ) 2 = 1 / 16002 ∧
    mersenneCorrectionTail 1 ≤ 5 / 42 ∧
    (3 / 8 : ℝ) < 1 / 2 - mersenneCorrectionTail 1 := by
  refine ⟨half_sub_four_term_prefix_eq, mersenneCorrectionTail_one_le, ?_⟩
  have h := mersenneCorrectionTail_one_le
  linarith

/-- Long lem:mersenne-tail-weight: definitions, recursion, strict tail
inequality and the displayed envelope, with the correct positive-rank guard. -/
theorem long_mersenne_tail_package (n : ℕ) :
    mersenneWeight n = 1 / ((2 : ℝ) ^ n - 1) ∧
    mersenneTail n = (∑' k : ℕ, mersenneWeight (n + k + 1)) ∧
    mersenneTail n = mersenneWeight (n + 1) + mersenneTail (n + 1) ∧
    (0 < n → mersenneTail n < mersenneWeight n) ∧
    mersenneTail n ≤ 2 * mersenneWeight (n + 1) := by
  exact ⟨rfl, rfl, mersenneTail_eq_weight_add n,
    fun hn => mersenneTail_lt_weight hn, mersenneTail_le_two_mul_weight n⟩

/-- Long lem:half-endpoint-kills: the two separate boundary exclusions. -/
theorem long_half_endpoint_exclusions (u : Finset ℕ) (d : ℕ) (h0 : 0 ∉ u) :
    positiveMersenneSupportValue (↑u : Set ℕ) ≠ (1 / 2 : ℝ) ∧
    positiveMersenneSupportValue (↑u : Set ℕ) + mersenneTail d ≠ (1 / 2 : ℝ) := by
  exact ⟨positiveMersenneSupportValue_coe_finset_ne_half h0,
    half_ne_coe_finset_add_mersenneTail u d⟩

end ErdosProblems.Erdos257.PaperCompleteR7
end
