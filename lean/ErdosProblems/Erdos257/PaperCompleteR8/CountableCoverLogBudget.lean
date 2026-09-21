import ErdosProblems.Erdos257.PaperCompleteR8.FiniteCoverLogBudget

/-!
# Countable positive-cover first logarithmic moment

A finite test support admits a finite subcover. The omitted frame weights
are retained as a subprobability inequality, so no renormalisation cost is
lost. Countable divisor majorants are truncated only at the actual finite
observation horizon; their reciprocal costs are bounded by their convergent
series. The endpoint assumes summability of the explicit total cover cost,
not the logarithmic obstruction it proves.
-/
noncomputable section
namespace ErdosProblems.Erdos257.PaperCompleteR8
open Finset
open ErdosProblems.Erdos257.PaperCompleteR7

/-- A finite fraction of a probability cover still has a sufficiently large frame. -/
theorem exists_frame_ge_subprobability_share (J : Finset ℕ) (η u : ℕ → ℝ) (t : ℝ)
    (hJ : J.Nonempty) (hη : ∑ j ∈ J, η j ≤ 1) (ht : 0 ≤ t)
    (hcover : t ≤ ∑ j ∈ J, u j) :
    ∃ j ∈ J, η j * t ≤ u j := by
  by_contra h
  push_neg at h
  have hs := Finset.sum_lt_sum_of_nonempty hJ h
  have heq : (∑ j ∈ J, η j * t) ≤ t := by
    rw [← Finset.sum_mul]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hη ht
  exact (not_lt_of_ge hcover) (hs.trans_le heq)

/-- Pointwise logarithmic cost for a finite subfamily of a countable cover. -/
theorem finite_subprobability_cover_log_pointwise (J : Finset ℕ) (η α : ℕ → ℝ)
    (f : ℕ) (g : ℕ → ℕ) (hJ : J.Nonempty)
    (hη : ∑ j ∈ J, η j ≤ 1) (hηpos : ∀ j ∈ J, 0 < η j)
    (hα : ∀ j ∈ J, 0 < α j ∧ α j ≤ 1)
    (hcover : f ≤ ∑ j ∈ J, g j) :
    Real.exp 1 * Real.log (f : ℝ) ≤
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
  · simp only [hf, Nat.cast_zero, Real.log_zero, mul_zero]
    exact Finset.sum_nonneg hnonneg
  have hf1 : (1 : ℝ) ≤ f := by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hf)
  have hcov : (f : ℝ) ≤ ∑ j ∈ J, (g j : ℝ) := by exact_mod_cast hcover
  obtain ⟨j, hj, hshare⟩ := exists_frame_ge_subprobability_share J η (fun j => (g j : ℝ)) f hJ hη (Nat.cast_nonneg f) hcov
  have hratio : (f : ℝ) ≤ (g j : ℝ) / η j :=
    (le_div_iff₀ (hηpos j hj)).2 (by simpa [mul_comm] using hshare)
  have hp := Real.rpow_le_rpow (Nat.cast_nonneg f) hratio (hα j hj).1.le
  rw [Real.div_rpow (Nat.cast_nonneg _) (hηpos j hj).le (α j)] at hp
  exact (exp_one_mul_log_le_rpow_div hf1 (hα j hj).1 (hα j hj).2).trans
    ((div_le_div_of_nonneg_right hp (hden j hj).le).trans
      (Finset.single_le_sum hnonneg hj))

/-- Countable divisor-majorant averaging at a finite horizon. -/
theorem cesaro_le_tsum_divisorMajorantCost
    (g c : ℕ → ℝ) (X : ℕ) (hX : 0 < X)
    (hg : ∀ n, 0 ≤ g n) (hc : ∀ d, 0 < d → 0 ≤ c d)
    (hs : Summable (fun d : ℕ => c d / (d : ℝ)))
    (hmaj : ∀ n, 0 < n → g n ≤ ∑ d ∈ n.divisors, c d) :
    (∑ n ∈ Finset.Icc 1 X, g n) / X ≤ ∑' d : ℕ, c d / (d : ℝ) := by
  classical
  let D := Finset.Icc 1 X
  let gX : ℕ → ℝ := fun n => if n ≤ X then g n else 0
  have hD : ∀ d ∈ D, 0 < d := by
    intro d hd
    exact (Finset.mem_Icc.mp hd).1
  have htrunc : ∀ n, 0 < n →
      gX n ≤ ∑ d ∈ D.filter (fun d => d ∣ n), c d := by
    intro n hn
    by_cases hnx : n ≤ X
    · have hsub : n.divisors ⊆ D.filter (fun d => d ∣ n) := by
        intro d hd
        have hdn := Nat.dvd_of_mem_divisors hd
        exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr
          ⟨Nat.pos_of_mem_divisors hd, (Nat.le_of_dvd hn hdn).trans hnx⟩, hdn⟩
      have hsum := Finset.sum_le_sum_of_subset_of_nonneg hsub
        (fun d hd _ => hc d (hD d (Finset.mem_filter.mp hd).1))
      simpa only [gX, if_pos hnx] using (hmaj n hn).trans hsum
    · simp only [gX, if_neg hnx]
      exact Finset.sum_nonneg (fun d hd => hc d (hD d (Finset.mem_filter.mp hd).1))
  have hfinite := cesaro_le_divisorMajorantCost gX D c X hX hD
    (fun d hd => hc d (hD d hd)) (fun n => by
      dsimp [gX]
      split_ifs
      · exact hg n
      · exact le_rfl) htrunc
  have heq : (∑ n ∈ Finset.Icc 1 X, gX n) = ∑ n ∈ Finset.Icc 1 X, g n := by
    apply Finset.sum_congr rfl
    intro n hn
    exact if_pos (Finset.mem_Icc.mp hn).2
  rw [heq] at hfinite
  have hcost : divisorMajorantCost D c ≤ ∑' d : ℕ, c d / (d : ℝ) := by
    apply hs.sum_le_tsum D
    intro d _
    by_cases hd : d = 0
    · simp [hd]
    · exact div_nonneg (hc d (Nat.pos_of_ne_zero hd)) (Nat.cast_nonneg d)
  exact hfinite.trans hcost

/-- Literal finite supports have finite subcovers, with no disjointness requirement. -/
theorem exists_finite_frame_subcover (F : Finset ℕ) (G : ℕ → Finset ℕ)
    (hcover : ∀ a ∈ F, ∃ j, a ∈ G j) :
    ∃ J : Finset ℕ, F ⊆ J.biUnion G := by
  classical
  revert hcover
  induction F using Finset.induction_on with
  | empty =>
    intro _
    exact ⟨∅, by simp⟩
  | @insert a F ha ih =>
    intro hcover
    obtain ⟨j, hj⟩ := hcover a (Finset.mem_insert_self a F)
    obtain ⟨J, hJ⟩ := ih (fun b hb => hcover b (Finset.mem_insert_of_mem hb))
    refine ⟨insert j J, ?_⟩
    intro b hb
    rcases Finset.mem_insert.mp hb with rfl | hb
    · exact Finset.mem_biUnion.mpr ⟨j, Finset.mem_insert_self _ _, hj⟩
    · obtain ⟨k, hk, hbk⟩ := Finset.mem_biUnion.mp (hJ hb)
      exact Finset.mem_biUnion.mpr ⟨k, Finset.mem_insert_of_mem hk, hbk⟩

/-- The full countable-cover logarithmic budget at every finite horizon.
The finite support can overlap arbitrarily many countable frames. -/
theorem countable_cover_log_mean_le_cost
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
      Real.exp 1 * Real.log ((F.filter (fun a => a ∣ n)).card : ℝ)) / X ≤
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
      Real.log_zero, mul_zero, Finset.sum_const_zero, zero_div]
    exact tsum_nonneg hK
  obtain ⟨J, hFJ⟩ := exists_finite_frame_subcover F G hcover
  have hJ : J.Nonempty := by
    obtain ⟨a, ha⟩ := Finset.nonempty_iff_ne_empty.mpr hF
    obtain ⟨j, hj, _⟩ := Finset.mem_biUnion.mp (hFJ ha)
    exact ⟨j, hj⟩
  have hηJ : ∑ j ∈ J, η j ≤ 1 := by
    have hh := hη.summable.sum_le_tsum J (fun j _ => (hηpos j).le)
    simpa only [hη.tsum_eq] using hh
  have hpoint : ∀ n, Real.exp 1 * Real.log ((F.filter (fun a => a ∣ n)).card : ℝ) ≤
      ∑ j ∈ J, (((G j).filter (fun a => a ∣ n)).card : ℝ) ^ α j /
        (η j ^ α j) / ((2 : ℝ) ^ α j - 1) := by
    intro n
    exact finite_subprobability_cover_log_pointwise J η α _ _ hJ hηJ
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

end ErdosProblems.Erdos257.PaperCompleteR8
end
