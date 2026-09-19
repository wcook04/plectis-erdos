import ErdosProblems.Erdos257.PaperCompleteR8.ArbitraryWeightReturns
import ErdosProblems.Erdos257.PaperCompleteR8.WeightedHereditaryClaim

/-!
# Arbitrary-weight positive covers on the weighted common scale

`LogBudgetCover` carries the paper's arbitrary strictly positive weights of
total mass one.  This module combines its nonlinear threshold test with the
checked weighted finite mean, so both support classes use one actual sample.
-/
noncomputable section
namespace ErdosProblems.Erdos257.PaperCompleteR8
open Finset Filter
open Erdos249257
open ErdosProblems.Erdos257.PaperCompleteR7

/-- The paper's arbitrary positive-weight cover conclusion, exposed under
the data structure that records the weights and their sum-one hypothesis. -/
theorem arbitraryWeightPositiveCover_allBase_hereditary
    {V : Set ℕ} (D : LogBudgetCover V) :
    ∀ A : Set ℕ, A ⊆ V → A.Infinite → ∀ b : ℕ, 2 ≤ b →
      Irrational (erdosSupportSeries b A) :=
  logBudgetCover_allBase_hereditary D

/-- Weighted support and an arbitrary positive-weight logarithmic cover have
binary returns at a common sample.  No separate return times are combined. -/
theorem mixedLogBudget_binary_returns_of_mean_target
    (htarget : WeightedDyadicMeanTarget) (E V : Set ℕ) (hE0 : 0 ∉ E)
    (hE : FinitePrimeWeighted 2 E) (D : LogBudgetCover V) :
    ∀ ε : ℝ, 0 < ε →
      ∃ N : ℕ, 0 < N ∧ displacement 2 (E ∪ V) N < ε := by
  intro ε hε
  let C := D.toPositiveCoverData
  let ρ : ℝ := ε / 2
  let t : ℕ → ℝ := fun j => ρ * D.weight j
  have hρ : 0 < ρ := div_pos hε (by norm_num)
  have ht : ∀ j, 0 < t j := fun j => mul_pos hρ (D.weight_positive j)
  have htsum : HasSum t ρ := by
    simpa only [mul_one] using D.weight_sum.mul_left ρ
  have hs : Summable (thresholdCost C t) :=
    summable_logBudget_thresholdCost D hρ
  have htail := tendsto_sum_nat_add (thresholdCost C t)
  obtain ⟨J, hJ⟩ :=
    (htail.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 8))).exists
  obtain ⟨L₀, hL₀, hdiv⟩ := coverPrefix_common_multiple C J
  obtain ⟨Q, R, M, hQ, hLQ, hscale, hW⟩ :=
    htarget 2 E (by norm_num) hE0 hE (ρ / 4)
      (div_pos hρ (by norm_num)) L₀ hL₀
  have hM : 0 < M := by omega
  have hK := one_add_four_ratio_le_two Q M hM hscale
  have hcost0 : 0 ≤ ∑' k, thresholdCost C t (k + J) :=
    tsum_nonneg (fun k => thresholdCost_nonneg C t ht (k + J))
  have hbound := dyadicMean_thresholdTailTest_le C t ht hs J Q R M hQ hM
  have hprod := mul_le_mul_of_nonneg_right hK hcost0
  have htest : dyadicMean Q R M (thresholdTailTest C t J) < 1 / 4 := by
    nlinarith only [hbound, hprod, hJ]
  have hwsmall :
      dyadicMean Q R M (fun N => displacement 2 E N / ρ) < 1 / 4 := by
    rw [dyadicMean_div_const]
    apply (div_lt_iff₀ hρ).2
    simpa only [div_eq_mul_inv, one_mul, mul_comm] using hW
  have hmean : dyadicMean Q R M
      (fun N => displacement 2 E N / ρ + thresholdTailTest C t J N) < 1 := by
    rw [dyadicMean_add]
    linarith only [hwsmall, htest]
  obtain ⟨j, m, _, _, _, hsample⟩ :=
    exists_sample_lt_of_dyadicMean_lt Q R M hM
      (fun N => displacement 2 E N / ρ + thresholdTailTest C t J N) 1 hmean
  let N := (m + 1) * Q
  have hN : 0 < N := Nat.mul_pos (Nat.succ_pos m) hQ
  have hQN : Q ∣ N := ⟨m + 1, by dsimp [N]; ring⟩
  have hW0 : 0 ≤ displacement 2 E N / ρ :=
    div_nonneg (displacement_nonneg 2 E N (by norm_num)) hρ.le
  have hT0 : 0 ≤ thresholdTailTest C t J N :=
    tsum_nonneg (fun k => mul_nonneg (thresholdScale_pos C t ht (k + J)).le
      (coverPotential_nonneg C (k + J) N))
  have hS : thresholdTailTest C t J N < 1 :=
    (le_add_of_nonneg_left hW0).trans_lt hsample
  have hW1 : displacement 2 E N / ρ < 1 :=
    (le_add_of_nonneg_right hT0).trans_lt hsample
  have hWE : displacement 2 E N < ρ := by
    have hh := (div_lt_iff₀ hρ).mp hW1
    simpa only [one_mul] using hh
  have hdN : ∀ d ∈ coverPrefix C J, d ∣ N :=
    fun d hd => ((hdiv d hd).trans hLQ).trans hQN
  have hCV := displacement_host_le_of_thresholdTailTest C t ht hs ρ htsum J N hdN hS
  have hUnion := displacement_union_le 2 E C.host N (by norm_num)
  have hLarge : displacement 2 (E ∪ C.host) N < ε := by
    dsimp [ρ] at hWE hCV
    linarith only [hUnion, hWE, hCV]
  have hsub : E ∪ V ⊆ E ∪ C.host := by
    intro a ha
    rcases ha with hEa | hVa
    · exact Or.inl hEa
    · exact Or.inr (D.covers a hVa)
  exact ⟨N, hN,
    (displacement_mono 2 (E ∪ V) (E ∪ C.host) N (by norm_num) hsub).trans_lt hLarge⟩

/-- Exact arbitrary-weight mixed conclusion: every infinite subset of the
union has irrational support series in every integer base at least two. -/
theorem arbitraryWeightMixedSupport_allBase_hereditary
    (E V : Set ℕ) (hE0 : 0 ∉ E) (hE : FinitePrimeWeighted 2 E)
    (D : LogBudgetCover V) :
    ∀ A : Set ℕ, A ⊆ E ∪ V → A.Infinite → ∀ b : ℕ, 2 ≤ b →
      Irrational (erdosSupportSeries b A) :=
  all_base_hereditary_of_binary_returns (E ∪ V)
    (mixedLogBudget_binary_returns_of_mean_target weightedDyadicMeanTarget
      E V hE0 hE D)

end ErdosProblems.Erdos257.PaperCompleteR8
end
