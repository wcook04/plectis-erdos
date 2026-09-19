import ErdosProblems.Erdos257.PaperCompleteR8.PositiveCoverReturn

/-!
# Weighted mean + nonlinear cover test on ONE finite sampling scheme

The previous return's JointDyadicMeanSupply is a sufficient
condition, but is not the exact interface of the ordinary mixed proof: a small
fractional cover test need not give a small FIRST MOMENT of the displacement.
This module uses the correct nonlinear test. PositiveCoverData contributes no
remaining target. The concrete weighted finite-mean producer is isolated
here and proved, without additional premises, in WeightedReturn.
-/
noncomputable section
namespace ErdosProblems.Erdos257.PaperCompleteR8
open Erdos249257
open ErdosProblems.Erdos257.PaperCompleteR7

/-- Interface of the weighted analytic producer, proved in WeightedReturn.
Prefix divisibility and
scale control are quantitative inputs to the same actual finite mean. -/
def WeightedDyadicMeanTarget : Prop :=
  ∀ (b : ℕ) (E : Set ℕ), 2 ≤ b → 0 ∉ E → FinitePrimeWeighted b E →
    ∀ ε : ℝ, 0 < ε → ∀ L₀ : ℕ, 0 < L₀ →
      ∃ Q R M : ℕ, 0 < Q ∧ L₀ ∣ Q ∧ 4 * Q ≤ M ∧
        dyadicMean Q R M (displacement b E) < ε

theorem dyadicMean_div_const (L R M : ℕ) (f : ℕ → ℝ) (c : ℝ) :
    dyadicMean L R M (fun N => f N / c) = dyadicMean L R M f / c := by
  have hh := dyadicMean_const_mul L R M c⁻¹ f
  simpa only [div_eq_mul_inv, mul_comm] using hh

/-- Exact fixed-base irrationality from the concrete weighted mean producer. -/
theorem weighted_irrational_of_mean_target (htarget : WeightedDyadicMeanTarget)
    (b : ℕ) (E : Set ℕ) (hb : 2 ≤ b) (hE0 : 0 ∉ E)
    (hE : FinitePrimeWeighted b E) (hInf : E.Infinite) :
    Irrational (erdosSupportSeries b E) := by
  apply irrational_of_displacement_returns b E hb hInf
  intro ε hε
  obtain ⟨Q, R, M, hQ, _, hM, hsmall⟩ := htarget b E hb hE0 hE ε hε 1 (by decide)
  obtain ⟨j, m, _, _, _, hsample⟩ :=
    exists_sample_lt_of_dyadicMean_lt Q R M (by omega) (displacement b E) ε hsmall
  exact ⟨(m + 1) * Q, Nat.mul_pos (Nat.succ_pos m) hQ, hsample⟩

/-- Both clauses of the long record's actual weighted claim. -/
theorem divisibilityWeightedClaim_of_mean_target
    (htarget : WeightedDyadicMeanTarget) : DivisibilityWeightedClaim := by
  constructor
  · intro b E hb hE0 hInf hE
    exact weighted_irrational_of_mean_target htarget b E hb hE0 hE hInf
  · intro H hH0 hH
    apply all_base_hereditary_of_binary_returns H
    intro ε hε
    obtain ⟨Q, R, M, hQ, _, hM, hsmall⟩ := htarget 2 H (by norm_num) hH0 hH ε hε 1 (by decide)
    obtain ⟨j, m, _, _, _, hsample⟩ :=
      exists_sample_lt_of_dyadicMean_lt Q R M (by omega) (displacement 2 H) ε hsmall
    exact ⟨(m + 1) * Q, Nat.mul_pos (Nat.succ_pos m) hQ, hsample⟩

/-- Nonlinear mixed consumer. All cover estimates and interfaces are proved
in the preceding modules; no separate cover return, raw cover mean, or
irrationality premise is assumed. -/
theorem mixed_binary_returns_of_mean_target
    (htarget : WeightedDyadicMeanTarget) (E : Set ℕ) (hE0 : 0 ∉ E)
    (hE : FinitePrimeWeighted 2 E) (C : PositiveCoverData)
    (hC : C.StrengthenedCostSummable) :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, 0 < N ∧ displacement 2 (E ∪ C.host) N < ε := by
  intro ε hε
  let ρ : ℝ := ε / 2
  have hρ : 0 < ρ := div_pos hε (by norm_num)
  obtain ⟨J, hJ⟩ := exists_coverScaledCost_tail_lt C hC hρ (by norm_num : (0 : ℝ) < 1/8)
  obtain ⟨L₀, hL₀, hdiv⟩ := coverPrefix_common_multiple C J
  obtain ⟨Q, R, M, hQ, hLQ, hscale, hW⟩ :=
    htarget 2 E (by norm_num) hE0 hE (ρ / 4) (div_pos hρ (by norm_num)) L₀ hL₀
  have hM : 0 < M := by omega
  have hK := one_add_four_ratio_le_two Q M hM hscale
  have hcost0 : 0 ≤ ∑' k, coverScaledCost C ρ (k + J) :=
    tsum_nonneg (fun k => coverScaledCost_nonneg C hρ (k + J))
  have hbound := dyadicMean_coverTailTest_le C hC hρ J Q R M hQ hM
  have hprod := mul_le_mul_of_nonneg_right hK hcost0
  have htest : dyadicMean Q R M (coverTailTest C ρ J) < 1/4 := by
    nlinarith only [hbound, hprod, hJ]
  have hwsmall : dyadicMean Q R M (fun N => displacement 2 E N / ρ) < 1/4 := by
    rw [dyadicMean_div_const]
    apply (div_lt_iff₀ hρ).2
    simpa only [div_eq_mul_inv, one_mul, mul_comm] using hW
  have hmean : dyadicMean Q R M
      (fun N => displacement 2 E N / ρ + coverTailTest C ρ J N) < 1 := by
    rw [dyadicMean_add]
    linarith only [hwsmall, htest]
  obtain ⟨j, m, _, _, _, hsample⟩ := exists_sample_lt_of_dyadicMean_lt Q R M hM
    (fun N => displacement 2 E N / ρ + coverTailTest C ρ J N) 1 hmean
  let N := (m + 1) * Q
  have hN : 0 < N := Nat.mul_pos (Nat.succ_pos m) hQ
  have hQN : Q ∣ N := ⟨m + 1, by dsimp [N]; ring⟩
  have hW0 : 0 ≤ displacement 2 E N / ρ :=
    div_nonneg (displacement_nonneg 2 E N (by norm_num)) hρ.le
  have hT0 : 0 ≤ coverTailTest C ρ J N := coverTailTest_nonneg C hρ J N
  have hS : coverTailTest C ρ J N < 1 :=
    (le_add_of_nonneg_left hW0).trans_lt hsample
  have hW1 : displacement 2 E N / ρ < 1 :=
    (le_add_of_nonneg_right hT0).trans_lt hsample
  have hWE : displacement 2 E N < ρ := by
    have hh := (div_lt_iff₀ hρ).mp hW1
    simpa only [one_mul] using hh
  have hdN : ∀ d ∈ coverPrefix C J, d ∣ N :=
    fun d hd => ((hdiv d hd).trans hLQ).trans hQN
  have hCV := displacement_host_le_of_coverTailTest C hC hρ J N hdN hS
  have hUnion := displacement_union_le 2 E C.host N (by norm_num)
  refine ⟨N, hN, ?_⟩
  dsimp [ρ] at hWE hCV
  linarith only [hUnion, hWE, hCV]

/-- Full short-note mixed conclusion conditional on the weighted mean
producer. WeightedReturn supplies that producer and the premise-free endpoint. -/
theorem mixedSupportClaim_of_weighted_mean_target
    (htarget : WeightedDyadicMeanTarget) : MixedSupportClaim := by
  intro E V hE0 hE hV A hA hInf b hb
  obtain ⟨C, hVC, hC⟩ := hV
  have hsub : A ⊆ E ∪ C.host := by
    intro a ha
    rcases hA ha with hEa | hVa
    · exact Or.inl hEa
    · exact Or.inr (hVC hVa)
  exact all_base_hereditary_of_binary_returns (E ∪ C.host)
    (mixed_binary_returns_of_mean_target htarget E hE0 hE C hC)
    A hsub hInf b hb

end ErdosProblems.Erdos257.PaperCompleteR8
end
