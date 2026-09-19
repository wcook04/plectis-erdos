import ErdosProblems.Erdos257.PaperCompleteR8.CountableCoverLogBudget
import ErdosProblems.Erdos257.PaperCompleteR8.CoverScalarGauge
import ErdosProblems.Erdos257.PaperCompleteR8.OptimizedCoverBudget

/-! Full Psi-valued countable cover budget. Candidate authoring; Lean and
axiom audit UNRUN. The finite subcover retains its original weights and
uses only their subprobability bound; no disjointness is imposed. -/
noncomputable section
namespace ErdosProblems.Erdos257.PaperCompleteR8
open Finset
open ErdosProblems.Erdos257.PaperCompleteR7

/-- Pointwise full scalar-gauge cost for a finite subfamily of a countable cover. -/
theorem finite_subprobability_cover_gauge_pointwise (J : Finset ℕ) (η α : ℕ → ℝ)
    (f : ℕ) (g : ℕ → ℕ) (hJ : J.Nonempty)
    (hη : ∑ j ∈ J, η j ≤ 1) (hηpos : ∀ j ∈ J, 0 < η j)
    (hα : ∀ j ∈ J, 0 < α j ∧ α j ≤ 1)
    (hcover : f ≤ ∑ j ∈ J, g j) :
    coverGauge (f : ℝ) ≤
      ∑ j ∈ J, (g j : ℝ) ^ α j / (η j ^ α j) / ((2 : ℝ) ^ α j - 1) := by
  have hden : ∀ j ∈ J, 0 < (2 : ℝ) ^ α j - 1 := by
    intro j hj
    have hh := Real.one_lt_rpow (by norm_num : (1 : ℝ) < 2) (hα j hj).1
    linarith
  have hnonneg : ∀ j ∈ J,
      0 ≤ (g j : ℝ) ^ α j / (η j ^ α j) / ((2 : ℝ) ^ α j - 1) := by
    intro j hj
    exact div_nonneg (div_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)
      (Real.rpow_pos_of_pos (hηpos j hj) _).le) (hden j hj).le
  by_cases hf : f = 0
  · simp only [hf, Nat.cast_zero, coverGauge_zero]
    exact Finset.sum_nonneg hnonneg
  have hcov : (f : ℝ) ≤ ∑ j ∈ J, (g j : ℝ) := by exact_mod_cast hcover
  obtain ⟨j, hj, hshare⟩ := exists_frame_ge_subprobability_share J η (fun j => (g j : ℝ)) f hJ hη (Nat.cast_nonneg f) hcov
  have hratio : (f : ℝ) ≤ (g j : ℝ) / η j :=
    (le_div_iff₀ (hηpos j hj)).2 (by simpa [mul_comm] using hshare)
  have hp := Real.rpow_le_rpow (Nat.cast_nonneg f) hratio (hα j hj).1.le
  rw [Real.div_rpow (Nat.cast_nonneg _) (hηpos j hj).le (α j)] at hp
  exact (coverGauge_le_cost (Nat.cast_nonneg f) (hα j hj).1 (hα j hj).2).trans
    ((div_le_div_of_nonneg_right hp (hden j hj).le).trans
      (Finset.single_le_sum hnonneg hj))

/-- The full countable-cover scalar-gauge budget at every finite horizon.
The finite support can overlap arbitrarily many countable frames. -/
theorem countable_cover_gauge_mean_le_cost
    (F : Finset ℕ) (G : ℕ → Finset ℕ) (η α : ℕ → ℝ) (c : ℕ → ℕ → ℝ)
    (X : ℕ) (hX : 0 < X)
    (hη : HasSum η 1) (hηpos : ∀ j, 0 < η j)
    (hα : ∀ j, 0 < α j ∧ α j ≤ 1)
    (hc : ∀ j d, 0 < d → 0 ≤ c j d)
    (hcolumn : ∀ j, Summable (fun d : ℕ => c j d / (d : ℝ)))
    (hcover : ∀ a ∈ F, ∃ j, a ∈ G j)
    (hmaj : ∀ j n, 0 < n →
      (((G j).filter (fun a => a ∣ n)).card : ℝ) ^ α j ≤ ∑ d ∈ n.divisors, c j d)
    (hcost : Summable (fun j => (∑' d : ℕ, c j d / (d : ℝ)) /
      (η j ^ α j) / ((2 : ℝ) ^ α j - 1))) :
    (∑ n ∈ Finset.Icc 1 X,
      coverGauge ((F.filter (fun a => a ∣ n)).card : ℝ)) / X ≤
      ∑' j, (∑' d : ℕ, c j d / (d : ℝ)) /
        (η j ^ α j) / ((2 : ℝ) ^ α j - 1) := by
  classical
  let K : ℕ → ℝ := fun j => (∑' d : ℕ, c j d / (d : ℝ)) /
    (η j ^ α j) / ((2 : ℝ) ^ α j - 1)
  have hden : ∀ j, 0 < (2 : ℝ) ^ α j - 1 := by
    intro j
    have hh := Real.one_lt_rpow (by norm_num : (1 : ℝ) < 2) (hα j).1
    linarith
  have hK : ∀ j, 0 ≤ K j := by
    intro j
    apply div_nonneg _ (hden j).le
    apply div_nonneg _ (Real.rpow_pos_of_pos (hηpos j) _).le
    apply tsum_nonneg
    intro d
    by_cases hd : d = 0
    · simp [hd]
    · exact div_nonneg (hc j d (Nat.pos_of_ne_zero hd)) (Nat.cast_nonneg d)
  by_cases hF : F = ∅
  · simp only [hF, Finset.filter_empty, Finset.card_empty, Nat.cast_zero,
      coverGauge_zero, Finset.sum_const_zero, zero_div]
    exact tsum_nonneg hK
  obtain ⟨J, hFJ⟩ := exists_finite_frame_subcover F G hcover
  have hJ : J.Nonempty := by
    obtain ⟨a, ha⟩ := Finset.nonempty_iff_ne_empty.mpr hF
    obtain ⟨j, hj, _⟩ := Finset.mem_biUnion.mp (hFJ ha)
    exact ⟨j, hj⟩
  have hηJ : ∑ j ∈ J, η j ≤ 1 := by
    have hh := hη.summable.sum_le_tsum J (fun j _ => (hηpos j).le)
    simpa only [hη.tsum_eq] using hh
  have hpoint : ∀ n, coverGauge ((F.filter (fun a => a ∣ n)).card : ℝ) ≤
      ∑ j ∈ J, (((G j).filter (fun a => a ∣ n)).card : ℝ) ^ α j /
        (η j ^ α j) / ((2 : ℝ) ^ α j - 1) := by
    intro n
    exact finite_subprobability_cover_gauge_pointwise J η α _ _ hJ hηJ
      (fun j _ => hηpos j) (fun j _ => hα j)
      (divisor_count_le_sum_of_frame_cover F J G hFJ n)
  calc
    _ ≤ (∑ n ∈ Finset.Icc 1 X, ∑ j ∈ J,
        (((G j).filter (fun a => a ∣ n)).card : ℝ) ^ α j /
          (η j ^ α j) / ((2 : ℝ) ^ α j - 1)) / X :=
      div_le_div_of_nonneg_right (Finset.sum_le_sum (fun n _ => hpoint n)) (Nat.cast_nonneg X)
    _ = ∑ j ∈ J, ((∑ n ∈ Finset.Icc 1 X,
        (((G j).filter (fun a => a ∣ n)).card : ℝ) ^ α j) / X) /
          (η j ^ α j) / ((2 : ℝ) ^ α j - 1) := by
      rw [Finset.sum_comm, Finset.sum_div]
      apply Finset.sum_congr rfl
      intro j hj
      rw [← Finset.sum_div, ← Finset.sum_div]
      ring
    _ ≤ ∑ j ∈ J, K j := by
      apply Finset.sum_le_sum
      intro j hj
      have hav := cesaro_le_tsum_divisorMajorantCost
        (fun n => (((G j).filter (fun a => a ∣ n)).card : ℝ) ^ α j)
        (c j) X hX (fun n => Real.rpow_nonneg (Nat.cast_nonneg _) _)
        (hc j) (hcolumn j) (hmaj j)
      exact div_le_div_of_nonneg_right
        (div_le_div_of_nonneg_right hav (Real.rpow_pos_of_pos (hηpos j) _).le) (hden j).le
    _ ≤ _ := hcost.sum_le_tsum J (fun j _ => hK j)

def finiteGaugeMean (F : Finset ℕ) (X : ℕ) : ℝ :=
  (∑ n ∈ Finset.Icc 1 X, coverGauge ((F.filter (fun a => a ∣ n)).card : ℝ)) / X

theorem finiteGaugeMean_le_cost {A : Set ℕ} (C : LogBudgetCover A)
    (F : Finset ℕ) (hFA : (F : Set ℕ) ⊆ A) (X : ℕ) (hX : 0 < X) :
    finiteGaugeMean F X ≤ C.cost :=
  countable_cover_gauge_mean_le_cost F C.frame C.weight C.exponent C.coefficient
    X hX C.weight_sum C.weight_positive C.exponent_bounds C.coefficient_nonneg
    C.column_summable (fun a ha => C.covers a (hFA ha)) C.majorises C.budget_summable

theorem finiteGaugeMean_le_optimizedCost {A : Set ℕ}
    (C : LogBudgetCover A) (F : Finset ℕ) (hFA : (F : Set ℕ) ⊆ A)
    (X : ℕ) (hX : 0 < X) :
    finiteGaugeMean F X ≤ optimizedLogCoverCost A := by
  apply le_csInf (show (admissibleLogCoverCosts A).Nonempty from ⟨C.cost, ⟨C, rfl⟩⟩)
  rintro _ ⟨D, rfl⟩
  exact finiteGaugeMean_le_cost D F hFA X hX

theorem no_logBudgetCover_of_unbounded_finite_gauge_means (A : Set ℕ)
    (hlarge : ∀ R : ℝ, ∃ F : Finset ℕ, (F : Set ℕ) ⊆ A ∧
      ∃ X : ℕ, 0 < X ∧ R < finiteGaugeMean F X) :
    IsEmpty (LogBudgetCover A) := by
  refine ⟨fun C => ?_⟩
  obtain ⟨F, hFA, X, hX, hbig⟩ := hlarge C.cost
  exact (not_lt_of_ge (finiteGaugeMean_le_cost C F hFA X hX)) hbig

end ErdosProblems.Erdos257.PaperCompleteR8
end
