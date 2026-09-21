import Erdos249257.TerminalOnlyScaledVanishing

namespace ErdosProblems.Erdos257.PaperCompleteR20
open Erdos249257 Erdos249257.HalfCarryReachability
open Filter

/-- A fixed nonnegative exponential coefficient cannot have cofinally
many values below a fixed affine bound. -/
theorem zero_of_cofinal_linear_pow_bound (d a b : ℝ) (hd : 0 ≤ d)
    (h : ∀ K : ℕ, ∃ N : ℕ, K ≤ N ∧
      (2 : ℝ)^(N+1)*d ≤ a*(N : ℝ)+b) : d = 0 := by
  have hn : Tendsto (fun N : ℕ ↦ (N : ℝ)/(2 : ℝ)^N) atTop (nhds 0) := by
    simpa using tendsto_pow_const_div_const_pow_of_one_lt 1 (by norm_num : (1 : ℝ)<2)
  have h1 : Tendsto (fun N : ℕ ↦ (1 : ℝ)/(2 : ℝ)^N) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ)<2))
  have hu : Tendsto (fun N : ℕ ↦ (a*(N : ℝ)+b)/(2 : ℝ)^(N+1)) atTop (nhds 0) := by
    convert ((hn.const_mul a).add (h1.const_mul b)).div_const 2 using 1
    · funext N
      rw [pow_succ]
      ring
    · simp
  by_contra hne
  have hp : 0 < d := lt_of_le_of_ne hd (Ne.symm hne)
  obtain ⟨K, hK⟩ := eventually_atTop.1 (hu.eventually (gt_mem_nhds hp))
  obtain ⟨N, hKN, hN⟩ := h K
  have hdiv : d ≤ (a*(N : ℝ)+b)/(2 : ℝ)^(N+1) :=
    (le_div_iff₀ (by positivity)).2 (by nlinarith [hN])
  exact (not_lt_of_ge hdiv) (hK N hKN)

/-- The paper permits arbitrary real constants; absolute values provide a
nonnegative linear majorant without strengthening its hypotheses. -/
theorem sqrt_affine_majorant (C D : ℝ) (N : ℕ) :
    C*Real.sqrt ((N : ℝ)+1)+D ≤ |C| *((N : ℝ)+2)+|D| := by
  have hs : Real.sqrt ((N : ℝ)+1) ≤ (N : ℝ)+2 := by
    rw [Real.sqrt_le_iff]
    constructor
    · positivity
    · have : (0 : ℝ) ≤ N := by positivity
      nlinarith
  calc
    _ ≤ |C| *Real.sqrt ((N : ℝ)+1)+|D| :=
      add_le_add (mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity)) (le_abs_self D)
    _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left hs (abs_nonneg C)) le_rfl

/-- Full arbitrary-support clause of long `prop:collapse`. -/
theorem half_of_cofinal_absolute_carry (A : Set ℕ) (hone : 1 ∉ A)
    (C D : ℝ)
    (h : ∀ K : ℕ, ∃ N : ℕ, K ≤ N ∧
      |(integerHalfCarry A N : ℝ)| ≤ C*Real.sqrt ((N : ℝ)+1)+D) :
    erdosSupportSeries 2 A = (1 : ℝ)/2 := by
  have hz := zero_of_cofinal_linear_pow_bound
    |(1 : ℝ)/2-erdosSupportSeries 2 A| (|C|+1) (2*|C|+|D|+3)
    (abs_nonneg _) (by
      intro K
      obtain ⟨N, hKN, hN⟩ := h K
      refine ⟨N, hKN, ?_⟩
      have hi := integerHalfCarry_eq_scaled_residual_add_tail A hone N
      have ht := binaryCoeffTail_le (supportCoeff A) (supportCoeff_le_self A) (N+1)
      have ht0 := binaryCoeffTail_nonneg (supportCoeff A) (N+1)
      have hb := hN.trans (sqrt_affine_majorant C D N)
      have ha : (2 : ℝ)^(N+1)*|(1 : ℝ)/2-erdosSupportSeries 2 A| ≤
          |(integerHalfCarry A N : ℝ)|+binaryCoeffTail (supportCoeff A) (N+1) := by
        rw [← abs_of_nonneg (show (0 : ℝ) ≤ 2^(N+1) by positivity), ← abs_mul]
        have he : (2 : ℝ)^(N+1)*((1 : ℝ)/2-erdosSupportSeries 2 A) =
          (integerHalfCarry A N : ℝ)-binaryCoeffTail (supportCoeff A) (N+1) := by linarith
        rw [he]
        simpa only [sub_zero, zero_sub, abs_neg, abs_of_nonneg ht0] using abs_sub_le (integerHalfCarry A N : ℝ) 0 (binaryCoeffTail (supportCoeff A) (N+1))
      push_cast at ht
      nlinarith)
  have := abs_eq_zero.mp hz
  linarith

/-- One-sided bounds suffice whenever the support value does not overshoot. -/
theorem half_of_cofinal_upper_carry (A : Set ℕ) (hone : 1 ∉ A)
    (hle : erdosSupportSeries 2 A ≤ (1 : ℝ)/2) (C D : ℝ)
    (h : ∀ K : ℕ, ∃ N : ℕ, K ≤ N ∧
      (integerHalfCarry A N : ℝ) ≤ C*Real.sqrt ((N : ℝ)+1)+D) :
    erdosSupportSeries 2 A = (1 : ℝ)/2 := by
  apply half_of_cofinal_absolute_carry A hone C D
  intro K
  obtain ⟨N, hKN, hN⟩ := h K
  refine ⟨N, hKN, ?_⟩
  have hi := integerHalfCarry_eq_scaled_residual_add_tail A hone N
  have ht := binaryCoeffTail_nonneg (supportCoeff A) (N+1)
  have hn : (0 : ℝ) ≤ (integerHalfCarry A N : ℝ) := by
    rw [hi]
    exact add_nonneg (mul_nonneg (by positivity) (sub_nonneg.mpr hle)) ht
  rwa [abs_of_nonneg hn]

/-- Full greedy one-sided clause of long `prop:collapse`. -/
theorem greedy_half_of_cofinal_upper_carry (C D : ℝ)
    (h : ∀ K : ℕ, ∃ N : ℕ, K ≤ N ∧
      (integerHalfCarry (greedyMersenneSupport (1/2 : ℝ)) N : ℝ) ≤
        C*Real.sqrt ((N : ℝ)+1)+D) :
    erdosSupportSeries 2 (greedyMersenneSupport (1/2 : ℝ)) = (1 : ℝ)/2 := by
  apply half_of_cofinal_upper_carry _ _
    (erdosSupportSeries_greedyMersenneSupport_le (by norm_num)) C D h
  intro hm
  have ht := (succ_mem_greedyMersenneSupport_iff (1/2 : ℝ) 0).mp (by simpa using hm)
  norm_num [mersenneWeight, greedyMersenneRemainder] at ht

#print axioms half_of_cofinal_absolute_carry
#print axioms half_of_cofinal_upper_carry
#print axioms greedy_half_of_cofinal_upper_carry
end ErdosProblems.Erdos257.PaperCompleteR20
