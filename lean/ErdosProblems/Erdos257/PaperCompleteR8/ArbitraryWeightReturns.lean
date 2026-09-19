import ErdosProblems.Erdos257.PaperCompleteR8.CountableGaugeBudget
import ErdosProblems.Erdos257.PaperCompleteR8.PositiveCoverReturn
import ErdosProblems.Erdos257.PaperCompleteR7.TailGluing

/-!
# Actual return supplier for arbitrary strictly positive probability weights

This proves the paper's arbitrary-weight remark. It does not attempt to
re-enumerate an arbitrary probability sequence into geometric weights.
The checked single-column potential and finite-prefix limits are reused.
Build and axiom-audit status belongs to source-bound validation receipts.
-/
noncomputable section
namespace ErdosProblems.Erdos257.PaperCompleteR8
open Finset Filter
open Erdos249257
open ErdosProblems.Erdos257.PaperCompleteR7

def LogBudgetCover.toPositiveCoverData {A : Set ℕ} (D : LogBudgetCover A) : PositiveCoverData where
  frame := D.frame
  exponent := D.exponent
  coefficient := D.coefficient
  frame_positive := D.frame_positive
  exponent_bounds := D.exponent_bounds
  coefficient_nonneg := D.coefficient_nonneg
  column_summable := D.column_summable
  majorises := D.majorises

/-- A general positive threshold, whose sum will be fixed only at the final
consumer. This is actual coefficient scaling, not a return hypothesis. -/
def thresholdScale (C : PositiveCoverData) (t : ℕ → ℝ) (j : ℕ) : ℝ :=
  t j ^ (-C.exponent j)

def thresholdCost (C : PositiveCoverData) (t : ℕ → ℝ) (j : ℕ) : ℝ :=
  thresholdScale C t j * (C.cost j / (coverBase C j - 1))

def thresholdTailTest (C : PositiveCoverData) (t : ℕ → ℝ) (J N : ℕ) : ℝ :=
  ∑' k : ℕ, thresholdScale C t (k + J) * coverPotential C (k + J) N

theorem thresholdScale_pos (C : PositiveCoverData) (t : ℕ → ℝ)
    (ht : ∀ j, 0 < t j) (j : ℕ) : 0 < thresholdScale C t j :=
  Real.rpow_pos_of_pos (ht j) _

theorem thresholdCost_nonneg (C : PositiveCoverData) (t : ℕ → ℝ)
    (ht : ∀ j, 0 < t j) (j : ℕ) : 0 ≤ thresholdCost C t j :=
  mul_nonneg (thresholdScale_pos C t ht j).le
    (div_nonneg (positiveCover_cost_nonneg C j) (sub_pos.mpr (coverBase_gt_one C j)).le)

theorem summable_thresholdTailTest_terms (C : PositiveCoverData) (t : ℕ → ℝ)
    (ht : ∀ j, 0 < t j) (hs : Summable (thresholdCost C t)) (J N : ℕ) :
    Summable (fun k => thresholdScale C t (k + J) * coverPotential C (k + J) N) := by
  have htail : Summable (fun k => thresholdCost C t (k + J)) :=
    (summable_nat_add_iff J).mpr hs
  apply Summable.of_nonneg_of_le _ _ (htail.mul_left (2 * (N : ℝ) + 1))
  · intro k
    exact mul_nonneg (thresholdScale_pos C t ht (k + J)).le (coverPotential_nonneg C (k + J) N)
  · intro k
    have h := mul_le_mul_of_nonneg_left (coverPotential_le_cost C (k + J) N)
      (thresholdScale_pos C t ht (k + J)).le
    convert h using 1 <;> unfold thresholdCost <;> ring

theorem dyadicMean_thresholdTailTest_le (C : PositiveCoverData) (t : ℕ → ℝ)
    (ht : ∀ j, 0 < t j) (hs : Summable (thresholdCost C t))
    (J L R M : ℕ) (hL : 0 < L) (hM : 0 < M) :
    dyadicMean L R M (thresholdTailTest C t J) ≤
      (1 + 4 * (L : ℝ) / M) * (∑' k, thresholdCost C t (k + J)) := by
  let u : ℕ → ℕ → ℝ := fun k N => thresholdScale C t (k + J) * coverPotential C (k + J) N
  let K : ℝ := 1 + 4 * (L : ℝ) / M
  have hu : ∀ N, Summable (fun k => u k N) := summable_thresholdTailTest_terms C t ht hs J
  have hc : Summable (fun k => thresholdCost C t (k + J)) := (summable_nat_add_iff J).mpr hs
  have hdom : Summable (fun k => K * thresholdCost C t (k + J)) := hc.mul_left K
  have hp : ∀ k, dyadicMean L R M (u k) ≤ K * thresholdCost C t (k + J) := by
    intro k
    change dyadicMean L R M (fun N => thresholdScale C t (k + J) * coverPotential C (k + J) N) ≤ _
    rw [dyadicMean_const_mul]
    have h := mul_le_mul_of_nonneg_left
      (dyadicMean_coverPotential_le C (k + J) L R M hL hM)
      (thresholdScale_pos C t ht (k + J)).le
    convert h using 1 <;> dsimp [K, thresholdCost] <;> ring
  have hleft : Summable (fun k => dyadicMean L R M (u k)) := by
    refine Summable.of_nonneg_of_le ?_ hp hdom
    intro k
    exact dyadicMean_nonneg L R M (u k) (fun N =>
      mul_nonneg (thresholdScale_pos C t ht (k + J)).le (coverPotential_nonneg C (k + J) N))
  have h := Summable.tsum_le_tsum hp hleft hdom
  rw [tsum_dyadicMean u hu L R M, tsum_mul_left] at h
  exact h

theorem framePotential_lt_of_thresholdTailTest (C : PositiveCoverData) (t : ℕ → ℝ)
    (ht : ∀ j, 0 < t j) (hs : Summable (thresholdCost C t)) (J N : ℕ)
    (hsmall : thresholdTailTest C t J N < 1) (k : ℕ) :
    framePotential (C.frame (k + J)) N < t (k + J) := by
  have hsum := summable_thresholdTailTest_terms C t ht hs J N
  have hterm : thresholdScale C t (k + J) * coverPotential C (k + J) N ≤ thresholdTailTest C t J N :=
    hsum.le_tsum k (fun i _ => mul_nonneg (thresholdScale_pos C t ht (i + J)).le
      (coverPotential_nonneg C (i + J) N))
  have hbridge := positiveCover_frame_bridge C (k + J) N
  have hscale := thresholdScale_pos C t ht (k + J)
  have hp : thresholdScale C t (k + J) * framePotential (C.frame (k + J)) N ^ C.exponent (k + J) < 1 :=
    (mul_le_mul_of_nonneg_left hbridge hscale.le).trans_lt (hterm.trans_lt hsmall)
  have hone : thresholdScale C t (k + J) * t (k + J) ^ C.exponent (k + J) = 1 := by
    unfold thresholdScale
    rw [Real.rpow_neg (ht (k + J)).le]
    exact inv_mul_cancel₀ (Real.rpow_pos_of_pos (ht (k + J)) _).ne'
  by_contra hbad
  have hge : t (k + J) ≤ framePotential (C.frame (k + J)) N := le_of_not_gt hbad
  have hpow := Real.rpow_le_rpow (ht (k + J)).le hge (C.exponent_bounds (k + J)).1.le
  have hmult := mul_le_mul_of_nonneg_left hpow hscale.le
  rw [hone] at hmult
  exact (not_lt_of_ge hmult) hp

theorem displacement_host_le_of_thresholdTailTest (C : PositiveCoverData) (t : ℕ → ℝ)
    (ht : ∀ j, 0 < t j) (hs : Summable (thresholdCost C t)) (ρ : ℝ)
    (htsum : HasSum t ρ) (J N : ℕ) (hdiv : ∀ d ∈ coverPrefix C J, d ∣ N)
    (hsmall : thresholdTailTest C t J N < 1) : displacement 2 C.host N ≤ ρ := by
  have hbound := framePotential_lt_of_thresholdTailTest C t ht hs J N hsmall
  have ht' : Summable (fun k => t (k + J)) := (summable_nat_add_iff J).mpr htsum.summable
  have hu : Summable (fun k => framePotential (C.frame (k + J)) N) :=
    Summable.of_nonneg_of_le (fun k => framePotential_nonneg (C.frame (k + J)) N)
      (fun k => (hbound k).le) ht'
  have hzero := displacement_finset_eq_zero 2 (coverPrefix C J) N (by norm_num) hdiv
  have hsum := Summable.tsum_le_tsum (fun k => (hbound k).le) hu ht'
  have hsplit := htsum.summable.sum_add_tsum_nat_add J
  rw [htsum.tsum_eq] at hsplit
  have hpre : 0 ≤ ∑ k ∈ range J, t k := Finset.sum_nonneg (fun k _ => (ht k).le)
  have htail : (∑' k, t (k + J)) ≤ ρ := by linarith only [hsplit, hpre]
  exact (displacement_host_le_tsum_tail C J N hzero hu).trans (hsum.trans htail)

/-- The actual arbitrary-weight cost supplies every epsilon-scaled cost. -/
theorem summable_logBudget_thresholdCost {A : Set ℕ} (D : LogBudgetCover A)
    {ρ : ℝ} (hρ : 0 < ρ) :
    Summable (thresholdCost D.toPositiveCoverData (fun j => ρ * D.weight j)) := by
  let C := D.toPositiveCoverData
  let a : ℕ → ℝ := fun j => (∑' d : ℕ, D.coefficient j d / (d : ℝ)) /
    (D.weight j ^ D.exponent j) / ((2 : ℝ) ^ D.exponent j - 1)
  have ha : Summable a := D.budget_summable
  have hn : ∀ j, 0 ≤ a j := by
    intro j
    apply div_nonneg _ (sub_pos.mpr (Real.one_lt_rpow (by norm_num) (D.exponent_bounds j).1)).le
    apply div_nonneg _ (Real.rpow_pos_of_pos (D.weight_positive j) _).le
    exact positiveCover_cost_nonneg C j
  have heq : ∀ j, thresholdCost C (fun j => ρ * D.weight j) j =
      ρ ^ (-D.exponent j) * a j := by
    intro j
    unfold thresholdCost thresholdScale
    change (ρ * D.weight j) ^ (-D.exponent j) *
      ((∑' d : ℕ, D.coefficient j d / (d : ℝ)) / ((2 : ℝ) ^ D.exponent j - 1)) = _
    rw [Real.mul_rpow hρ.le (D.weight_positive j).le,
      Real.rpow_neg (D.weight_positive j).le]
    dsimp [a]
    ring
  apply Summable.of_nonneg_of_le
    (thresholdCost_nonneg C _ (fun j => mul_pos hρ (D.weight_positive j))) _ (ha.mul_left (max 1 ρ⁻¹))
  intro j
  rw [heq]
  exact mul_le_mul_of_nonneg_right
    (rpow_neg_le_max_one_inv hρ (D.exponent_bounds j).1 (D.exponent_bounds j).2) (hn j)

/-- Return admissibility with the paper's exact arbitrary positive weights.
The prefix and common multiple are constructed, not added as assumptions. -/
theorem logBudgetCover_returnAdmissible {A : Set ℕ} (D : LogBudgetCover A) :
    ReturnAdmissible A := by
  classical
  let C := D.toPositiveCoverData
  have hAC : A ⊆ C.host := fun a ha => D.covers a ha
  apply returnAdmissible_mono hAC
  intro ε hε L₀ hL₀ N₀
  let ρ : ℝ := ε / 2
  let t : ℕ → ℝ := fun j => ρ * D.weight j
  have hρ : 0 < ρ := div_pos hε (by norm_num)
  have ht : ∀ j, 0 < t j := fun j => mul_pos hρ (D.weight_positive j)
  have htsum : HasSum t ρ := by simpa only [mul_one] using D.weight_sum.mul_left ρ
  have hs : Summable (thresholdCost C t) := summable_logBudget_thresholdCost D hρ
  have htail := tendsto_sum_nat_add (thresholdCost C t)
  obtain ⟨J, hJ⟩ := (htail.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1/4))).exists
  obtain ⟨L₁, hL₁, hdiv⟩ := coverPrefix_common_multiple C J
  let L := L₀ * (N₀ + 1) * L₁
  have hL : 0 < L := Nat.mul_pos (Nat.mul_pos hL₀ (Nat.succ_pos _)) hL₁
  have hL₀L : L₀ ∣ L := dvd_mul_of_dvd_left (dvd_mul_right _ _) _
  have hL₁L : L₁ ∣ L := dvd_mul_left _ _
  have hNL : N₀ + 1 ∣ L := dvd_mul_of_dvd_left (dvd_mul_left _ _) _
  let M : ℕ := 4 * L
  have hM : 0 < M := Nat.mul_pos (by decide) hL
  have hK := one_add_four_ratio_le_two L M hM le_rfl
  have hcost0 : 0 ≤ ∑' k, thresholdCost C t (k + J) :=
    tsum_nonneg (fun k => thresholdCost_nonneg C t ht (k + J))
  have hbound := dyadicMean_thresholdTailTest_le C t ht hs J L 0 M hL hM
  have hprod := mul_le_mul_of_nonneg_right hK hcost0
  have hmean : dyadicMean L 0 M (thresholdTailTest C t J) < 1 := by
    nlinarith only [hbound, hprod, hJ]
  obtain ⟨j, m, _, _, _, hsample⟩ :=
    exists_sample_lt_of_dyadicMean_lt L 0 M hM (thresholdTailTest C t J) 1 hmean
  let N := (m + 1) * L
  have hN : 0 < N := Nat.mul_pos (Nat.succ_pos m) hL
  have hLN : L ∣ N := ⟨m + 1, by dsimp [N]; ring⟩
  have hlate := Nat.le_of_dvd hN (hNL.trans hLN)
  have hdN : ∀ d ∈ coverPrefix C J, d ∣ N := fun d hd => ((hdiv d hd).trans hL₁L).trans hLN
  have hret := displacement_host_le_of_thresholdTailTest C t ht hs ρ htsum J N hdN hsample
  refine ⟨N, by omega, hN, hL₀L.trans hLN, ?_⟩
  dsimp [ρ] at hret
  linarith only [hret, hε]

theorem logBudgetCover_allBase_hereditary {A : Set ℕ} (D : LogBudgetCover A) :
    ∀ B : Set ℕ, B ⊆ A → B.Infinite → ∀ b : ℕ, 2 ≤ b →
      Irrational (erdosSupportSeries b B) :=
  returnAdmissible_hereditary_irrational (logBudgetCover_returnAdmissible D)

end ErdosProblems.Erdos257.PaperCompleteR8
end
