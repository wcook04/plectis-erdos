import ErdosProblems.Erdos257.PaperCompleteR20.CarryCollapseCorrespondence
import Erdos249257.CofinalStripReturn
import Erdos249257.BooleanMobiusSkipRowCofinal
import Erdos249257.HalfCutLocator

namespace ErdosProblems.Erdos257.PaperCompleteR20
open Erdos249257 Erdos249257.HalfCarryReachability

private theorem greedy_half_value (hm : (1/2 : ℝ) ∈ mersenneAchievementSet) :
    erdosSupportSeries 2 (greedyMersenneSupport (1/2 : ℝ)) = (1/2 : ℝ) := by
  rcases hm with ⟨A, hA0, hv⟩
  rw [hv, greedySupport_supportValue_eq A hA0,
    positiveMersenneSupportValue_eq_erdosSupportSeries]

private theorem greedy_half_no_one : 1 ∉ greedyMersenneSupport (1/2 : ℝ) := by
  intro h
  have ht := (succ_mem_greedyMersenneSupport_iff (1/2 : ℝ) 0).mp (by simpa using h)
  norm_num [mersenneWeight, greedyMersenneRemainder] at ht

/-- The pointwise centered bound has the paper's constant four, including N=0. -/
theorem half_mem_iff_centered_bound :
    (1/2 : ℝ) ∈ mersenneAchievementSet ↔
      ∀ N : ℕ, (mobiusCenteredHalfCarry (greedyMersenneSupport (1/2 : ℝ)) N : ℝ) ≤
        2*Real.sqrt (N : ℝ)+4 := by
  constructor
  · intro hm N
    cases N with
    | zero => norm_num [mobiusCenteredHalfCarry, integerHalfCarry]
    | succ n =>
      have hv := greedy_half_value hm
      have hi := integerHalfCarry_eq_scaled_residual_add_tail
        (greedyMersenneSupport (1/2 : ℝ)) greedy_half_no_one (n+1)
      rw [hv, sub_self, mul_zero, zero_add] at hi
      have ht := binaryCoeffTail_supportCoeff_le_two_sqrt_add_four
        (greedyMersenneSupport (1/2 : ℝ)) (n+1+1)
      have hs1 := Real.sq_sqrt (show (0 : ℝ) ≤ (n : ℝ)+1 by positivity)
      have hs2 := Real.sq_sqrt (show (0 : ℝ) ≤ (n : ℝ)+1+1 by positivity)
      have hs0 := Real.sqrt_nonneg ((n : ℝ)+1)
      have hs0' := Real.sqrt_nonneg ((n : ℝ)+1+1)
      have hsge : 1 ≤ Real.sqrt ((n : ℝ)+1) := by
        have hn : (0 : ℝ) ≤ n := by positivity
        nlinarith
      have hstep : Real.sqrt ((n : ℝ)+1+1) ≤ Real.sqrt ((n : ℝ)+1)+1/2 := by
        nlinarith
      unfold mobiusCenteredHalfCarry
      push_cast
      push_cast at ht hi
      linarith
  · intro hb
    have hv := (greedy_half_infinite_of_mobiusCenteredHalfCarry_upperBound hb).2
    refine ⟨greedyMersenneSupport (1/2 : ℝ), zero_not_mem_greedyMersenneSupport _, ?_⟩
    rw [positiveMersenneSupportValue_eq_erdosSupportSeries]
    exact hv.symm

/-- No consistency is required between exact finite quotient rows. -/
theorem half_mem_iff_cofinal_exact_rows :
    (1/2 : ℝ) ∈ mersenneAchievementSet ↔ CofinalExactLocalMersenneHalfRows :=
  ⟨fun hm ↦ cofinalExactLocalMersenneHalfRows_of_positiveHalfGreedySkips
      (cofinalPositiveHalfGreedySkips_iff_half_mem.mpr hm),
    half_mem_mersenneAchievementSet_of_cofinalExactLocalRows⟩

theorem half_mem_iff_cofinal_greedy_strip :
    (1/2 : ℝ) ∈ mersenneAchievementSet ↔ GreedyHalfCarryCofinalStripReturn := by
  constructor
  · intro hm K
    obtain ⟨N, hKN, hN⟩ := achieving_support_cofinal_strip _ greedy_half_no_one (greedy_half_value hm) K
    refine ⟨N, hKN, ?_⟩
    exact_mod_cast hN
  · exact half_mem_mersenneAchievementSet_of_cofinalStripReturn

/-- Square truncations supply the original terminal-only strip, with no
compatibility assumption added to its converse. -/
theorem half_mem_iff_cofinal_terminal_strip :
    (1/2 : ℝ) ∈ mersenneAchievementSet ↔ HalfCarryCofinalTerminalOnlyStrip := by
  classical
  constructor
  · intro hm K
    let G := greedyMersenneSupport (1/2 : ℝ)
    let k := max K 1
    let M := k^2
    have hk : 1 ≤ k := le_max_right _ _
    have hM : max K 1 ≤ M := by dsimp [M, k] at *; nlinarith
    have hM1 : 1 ≤ M := hk.trans hM
    let w : HalfWord M := fun i ↦ decide (i.val ∈ G)
    have hw : wordSupport w = G ∩ Set.Iic M := by
      ext n
      simp only [wordSupport, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_Iic, w,
        decide_eq_true_eq]
      constructor
      · rintro ⟨hn, ha⟩; exact ⟨ha, by omega⟩
      · rintro ⟨ha, hn⟩; exact ⟨by omega, ha⟩
    refine ⟨M, hM, w, ?_, ?_, ?_⟩
    · simp [w, G]
    · intro hi
      simp only [w, decide_eq_false_iff_not]
      exact greedy_half_no_one
    · rw [hw, integerHalfCarry_inter_Iic_eq_of_succ_le G M (M-1)
        (by omega)]
      have hs := square_depth_witness G greedy_half_no_one (greedy_half_value hm) k hk
      have ht := binaryCoeffTail_nonneg (supportCoeff G) M
      change |(integerHalfCarry G (k^2-1) : ℝ)| ≤ (halfStripBound (k^2) : ℝ)
      rw [hs.1, abs_of_nonneg ht, hs.2.2]
      exact hs.2.1
  · exact half_mem_mersenneAchievementSet_of_cofinalTerminalOnlyStrip

/-- Literal positive omitted-exponent formulation used in the paper. -/
theorem half_mem_iff_cofinal_omitted_exponents :
    (1/2 : ℝ) ∈ mersenneAchievementSet ↔
      ∀ K : ℕ, ∃ n : ℕ, K ≤ n ∧ 0 < n ∧ n ∉ greedyMersenneSupport (1/2 : ℝ) := by
  rw [half_mem_mersenneAchievementSet_iff_greedySkippedSupport_infinite]
  constructor
  · intro h K
    obtain ⟨n, hn, hKn⟩ := Set.infinite_iff_exists_gt.mp h K
    exact ⟨n, hKn.le, Nat.pos_of_ne_zero hn.1, hn.2⟩
  · intro h
    apply Set.infinite_iff_exists_gt.mpr
    intro K
    obtain ⟨n, hn, hp, hs⟩ := h (K+1)
    exact ⟨n, ⟨Nat.ne_of_gt hp, hs⟩, by omega⟩

/-- All six assertions in long `prop:collapsed-list`, retaining the literal
remainder inequality and its no-fatal-gap formulation in the final clause. -/
theorem six_membership_conditions :
    ((1/2 : ℝ) ∈ mersenneAchievementSet ↔
      ∀ N : ℕ, (mobiusCenteredHalfCarry (greedyMersenneSupport (1/2 : ℝ)) N : ℝ) ≤
        2*Real.sqrt (N : ℝ)+4) ∧
    ((1/2 : ℝ) ∈ mersenneAchievementSet ↔
      ∀ K : ℕ, ∃ n : ℕ, K ≤ n ∧ 0 < n ∧ n ∉ greedyMersenneSupport (1/2 : ℝ)) ∧
    ((1/2 : ℝ) ∈ mersenneAchievementSet ↔ CofinalExactLocalMersenneHalfRows) ∧
    ((1/2 : ℝ) ∈ mersenneAchievementSet ↔ GreedyHalfCarryCofinalStripReturn) ∧
    ((1/2 : ℝ) ∈ mersenneAchievementSet ↔ HalfCarryCofinalTerminalOnlyStrip) ∧
    ((1/2 : ℝ) ∈ mersenneAchievementSet ↔
      (∀ n : ℕ, greedyMersenneRemainder (1/2 : ℝ) n ≤ mersenneTail n) ∧
        ¬ ExistsFatalHalfGap) := by
  refine ⟨half_mem_iff_centered_bound, half_mem_iff_cofinal_omitted_exponents,
    half_mem_iff_cofinal_exact_rows, half_mem_iff_cofinal_greedy_strip,
    half_mem_iff_cofinal_terminal_strip, ?_⟩
  constructor
  · intro hm
    exact ⟨((mem_mersenneAchievementSet_iff_greedy_survival _).mp hm).2,
      half_mem_mersenneAchievementSet_iff_no_existsFatalHalfGap.mp hm⟩
  · intro h
    exact half_mem_mersenneAchievementSet_iff_no_existsFatalHalfGap.mpr h.2

#print axioms six_membership_conditions
#print axioms half_mem_iff_centered_bound
#print axioms half_mem_iff_cofinal_terminal_strip
end ErdosProblems.Erdos257.PaperCompleteR20
