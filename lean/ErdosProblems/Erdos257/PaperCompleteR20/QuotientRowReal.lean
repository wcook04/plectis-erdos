import ErdosProblems.Erdos257.PaperCompleteR20.QuotientRowIdentity
import ErdosProblems.Erdos257.PaperCompleteR20.QuotientRowRounding

namespace ErdosProblems.Erdos257.PaperCompleteR20
open Erdos249257 Erdos249257.HalfCylinderIntegerGreedy

noncomputable def rowRealError (n : ℕ) (D : Finset ℕ) : ℝ :=
  (4 : ℝ)^n*mersenneCorrectionTail (n-1)+rowRoundingError n D

private theorem scaled_correction_bounds {n : ℕ} (hn : 1 ≤ n) :
    0 < (4 : ℝ)^n*mersenneCorrectionTail (n-1) ∧
    (4 : ℝ)^n*mersenneCorrectionTail (n-1) < 8/3 := by
  have hu := mersenneCorrectionTail_le (n-1)
  have hc : ((1 : ℝ)/8)^(n-1) ≤ ((1 : ℝ)/4)^(n-1) :=
    pow_le_pow_left₀ (by norm_num) (by norm_num) _
  have hq : 0 < ((1 : ℝ)/4)^(n-1) := by positivity
  have hbound : mersenneCorrectionTail (n-1) < (2/3 : ℝ)*((1 : ℝ)/4)^(n-1) := by
    nlinarith
  have hp : (4 : ℝ)^n = 4^(n-1)*4 := by
    rw [← pow_succ, Nat.sub_add_cancel hn]
  have hscale : (4 : ℝ)^n*((1 : ℝ)/4)^(n-1) = 4 := by
    rw [hp]
    calc
      _ = 4 * ((4 : ℝ)^(n-1)*((1 : ℝ)/4)^(n-1)) := by ring
      _ = 4 := by rw [← mul_pow]; norm_num
  refine ⟨mul_pos (by positivity) (mersenneCorrectionTail_pos _), ?_⟩
  have hh := mul_lt_mul_of_pos_left hbound (show (0 : ℝ)<4^n by positivity)
  nlinarith

theorem row_real_error_bounds {n : ℕ} (hn : 6 ≤ n) (D : Finset ℕ)
    (hD : D ⊆ Finset.Ico 2 n) :
    0 < rowRealError n D ∧ rowRealError n D < (n : ℝ)+2/3 ∧
      |rowRealError n D| < 2*(n : ℝ)+2 := by
  have hs := scaled_correction_bounds (show 1 ≤ n by omega)
  have hr := row_rounding_error_bounds n D (by
    intro d hd; have := Finset.mem_Ico.mp (hD hd); omega)
  have hc : D.card ≤ n-2 := by
    have := Finset.card_le_card hD
    simpa using this
  have hcast : (D.card : ℝ) ≤ (n : ℝ)-2 := by
    have hcR : (D.card : ℝ) ≤ ((n-2 : ℕ) : ℝ) := by exact_mod_cast hc
    simpa only [Nat.cast_sub (show 2 ≤ n by omega), Nat.cast_ofNat] using hcR
  have hp : 0 < rowRealError n D := by unfold rowRealError; linarith [hr.1]
  have hu : rowRealError n D < (n : ℝ)+2/3 := by unfold rowRealError; linarith [hr.2.1]
  refine ⟨hp, hu, ?_⟩
  rw [abs_of_pos hp]
  have : (6 : ℝ) ≤ n := by exact_mod_cast hn
  linarith

private theorem constant_split {n : ℕ} (hn : 2 ≤ n) :
    erdosBorweinMersenneConstant = 1 + (∑ d ∈ Finset.Ico 2 n, mersenneWeight d) + mersenneTail (n-1) := by
  have hs := Finset.sum_Ico_consecutive mersenneWeight (show 1 ≤ 2 by omega) hn
  simp only [Nat.Ico_succ_singleton, Finset.sum_singleton] at hs
  have hp : (∑ d ∈ Finset.Ico 1 n, mersenneWeight d) = mersennePrefixMass (n-1) := by
    rw [Finset.sum_Ico_eq_sum_range]
    simp only [mersennePrefixMass, Nat.add_comm]
  rw [hp] at hs
  have hw : mersenneWeight 1 = 1 := by norm_num [mersenneWeight]
  rw [hw] at hs
  rw [erdosBorweinMersenneConstant_eq_prefix_add_tail (n-1), ← hs]

theorem row_real_decomposition {n : ℕ} (hn : 6 ≤ n) (D : Finset ℕ)
    (hD : D ⊆ Finset.Ico 2 n) :
    (rowDeviation n D : ℝ) = (4 : ℝ)^n *
      ((∑ d ∈ (Finset.Ico 2 n) \ D, mersenneWeight d) -
        (erdosBorweinMersenneConstant-3/2)) + rowRealError n D := by
  have hs := Finset.sum_sdiff hD (f := mersenneWeight)
  have hE := constant_split (show 2 ≤ n by omega)
  have hp : (2 : ℝ)^(2*n-1)*2 = (4 : ℝ)^n := by
    rw [← pow_succ, Nat.sub_add_cancel (show 1 ≤ 2*n by omega)]
    rw [pow_mul]
    norm_num
  have hb := four_pow_mul_half_pow_pred (show 1 ≤ n by omega)
  have hr : rowRoundingError n D = (4 : ℝ)^n*(∑ d ∈ D, mersenneWeight d) -
      ∑ d ∈ D, (truncatedMersenneWeight n d : ℝ) := by
    simp only [rowRoundingError, Finset.sum_sub_distrib, Finset.mul_sum]
  have hd : (rowDeviation n D : ℝ) = (2 : ℝ)^(2*n-1)-(2 : ℝ)^(n+1)-
      ∑ d ∈ D, (truncatedMersenneWeight n d : ℝ) := by
    simp [rowDeviation]
  rw [hd, rowRealError, hr, mersenneCorrectionTail, hE, ← hs]
  nlinarith [hp, hb]

/-- The decomposition, strict error bound and both error-retaining margins. -/
theorem paper_real_quotient_core {n : ℕ} (hn : 6 ≤ n) (D : Finset ℕ)
    (hD : D ⊆ Finset.Ico 2 n) :
    ∃ eta : ℝ,
      (rowDeviation n D : ℝ) = (4 : ℝ)^n *
        ((∑ d ∈ (Finset.Ico 2 n) \ D, mersenneWeight d) -
          (erdosBorweinMersenneConstant-3/2)) + eta ∧
      0 < eta ∧ eta < (n : ℝ)+2/3 ∧ |eta| < 2*(n : ℝ)+2 := by
  exact ⟨rowRealError n D, row_real_decomposition hn D hD, row_real_error_bounds hn D hD⟩

/-- The constant also has the paper's sum-from-rank-two definition. -/
theorem row_constant_eq_tail :
    erdosBorweinMersenneConstant-3/2 = mersenneTail 1-1/2 := by
  have h := mersenneTail_eq_weight_add 0
  have hw : mersenneWeight 1 = 1 := by norm_num [mersenneWeight]
  rw [hw] at h
  change mersenneTail 0-3/2 = mersenneTail 1-1/2
  linarith

/-- Literal sufficient and necessary thresholds from the paper. -/
theorem paper_real_quotient_margins {n : ℕ} (hn : 6 ≤ n) (D : Finset ℕ)
    (hD : D ⊆ Finset.Ico 2 n) (H : ℝ) :
    ((H+(2*(n : ℝ)+2))/(4 : ℝ)^n <
      |(∑ d ∈ (Finset.Ico 2 n) \ D, mersenneWeight d) - (erdosBorweinMersenneConstant-3/2)| →
      H < |(rowDeviation n D : ℝ)|) ∧
    (H < |(rowDeviation n D : ℝ)| →
      (H-(2*(n : ℝ)+2))/(4 : ℝ)^n <
      |(∑ d ∈ (Finset.Ico 2 n) \ D, mersenneWeight d) - (erdosBorweinMersenneConstant-3/2)|) := by
  have hm := deviation_error_margins _ _ _ H (2*(n : ℝ)+2)
    (row_real_decomposition hn D hD) (row_real_error_bounds hn D hD).2.2
  rw [abs_mul, abs_of_pos (show (0 : ℝ)<4^n by positivity)] at hm
  constructor
  · intro h
    apply hm.1
    have hh := (div_lt_iff₀ (show (0 : ℝ)<4^n by positivity)).mp h
    nlinarith
  · intro h
    apply (div_lt_iff₀ (show (0 : ℝ)<4^n by positivity)).mpr
    have hh := hm.2 h
    nlinarith

#print axioms row_constant_eq_tail
#print axioms paper_real_quotient_margins

#print axioms paper_real_quotient_core
end ErdosProblems.Erdos257.PaperCompleteR20
