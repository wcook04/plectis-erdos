import ErdosProblems.Erdos257.WeightedSupportAveraging

/-!
# Infinite-support observation errors

The dyadic error estimate only needs summability after division by the
conductor. The unweighted atom costs may have divergent sum. Every finite
set of observation lengths sees a finite union of conductors, so the
finite Fubini inequality applies before any infinite sum is bounded.
-/

namespace ErdosProblems.Erdos257

open Erdos249257 Filter

noncomputable section

/-- The actual cost seen up to a finite conductor cutoff. -/
def supportObservationMass (A : Set ℕ) (α : ℕ → ℝ) (R : ℕ) : ℝ := by
  classical
  exact ∑ a ∈ (Finset.range (R + 1)).filter (fun a => 0 < a ∧ a ∈ A), α a

/-- The reciprocal majorant; no summability of `α` itself is required. -/
def weightedObservationTerm (A : Set ℕ) (α : ℕ → ℝ) (a : ℕ) : ℝ := by
  classical
  exact if 0 < a ∧ a ∈ A then α a / a else 0

lemma weightedObservationTerm_nonneg (A : Set ℕ) (α : ℕ → ℝ)
    (hα : ∀ a ∈ A, 0 ≤ α a) (a : ℕ) :
    0 ≤ weightedObservationTerm A α a := by
  unfold weightedObservationTerm
  split_ifs with h
  · exact div_nonneg (hα a h.2) (Nat.cast_nonneg a)
  · exact le_rfl

/-- The full infinite support obeys the same finite dyadic bound. -/
theorem dyadic_supportObservationMass_sum_le (A : Set ℕ) (α : ℕ → ℝ)
    (hα : ∀ a ∈ A, 0 ≤ α a)
    (hs : Summable (weightedObservationTerm A α)) (J : Finset ℕ) (Q : ℕ) :
    (∑ j ∈ J, (1 / 2 : ℝ) ^ j * supportObservationMass A α (Q * 2 ^ j)) ≤
      2 * (Q : ℝ) * ∑' a : ℕ, weightedObservationTerm A α a := by
  classical
  let R := J.sup (fun j => Q * 2 ^ j)
  let F := (Finset.range (R + 1)).filter (fun a => 0 < a ∧ a ∈ A)
  have hF : ∀ a ∈ F, 0 < a := by
    intro a ha
    exact (Finset.mem_filter.mp ha).2.1
  have hFA : ∀ a ∈ F, a ∈ A := by
    intro a ha
    exact (Finset.mem_filter.mp ha).2.2
  have hcut : ∀ j ∈ J,
      F.filter (fun a => a ≤ Q * 2 ^ j) =
        (Finset.range (Q * 2 ^ j + 1)).filter (fun a => 0 < a ∧ a ∈ A) := by
    intro j hj
    have hjR : Q * 2 ^ j ≤ R := Finset.le_sup (f := fun j => Q * 2 ^ j) hj
    ext a
    simp only [F, Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨⟨ha, hpos, hA⟩, hle⟩
      exact ⟨by omega, hpos, hA⟩
    · rintro ⟨ha, hpos, hA⟩
      exact ⟨⟨by omega, hpos, hA⟩, by omega⟩
  have hfinite := dyadic_observation_sum_le J F Q α hF (fun a ha => hα a (hFA a ha))
  have hleft : (∑ j ∈ J, (1 / 2 : ℝ) ^ j * supportObservationMass A α (Q * 2 ^ j)) =
      ∑ j ∈ J, (1 / 2 : ℝ) ^ j * ∑ a ∈ F.filter (fun a => a ≤ Q * 2 ^ j), α a := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [hcut j hj]
    rfl
  have hsum : (∑ a ∈ F, α a / a) ≤ ∑' a : ℕ, weightedObservationTerm A α a := by
    have heq : (∑ a ∈ F, α a / a) = ∑ a ∈ F, weightedObservationTerm A α a := by
      apply Finset.sum_congr rfl
      intro a ha
      simp [weightedObservationTerm, hF a ha, hFA a ha]
    rw [heq]
    exact hs.sum_le_tsum F (fun a _ => weightedObservationTerm_nonneg A α hα a)
  rw [hleft]
  exact hfinite.trans (mul_le_mul_of_nonneg_left hsum (by positivity))

/-- The mean incomplete-period cost vanishes without an unweighted majorant. -/
theorem tendsto_dyadic_supportObservationMass_mean (A : Set ℕ) (α : ℕ → ℝ)
    (hα : ∀ a ∈ A, 0 ≤ α a)
    (hs : Summable (weightedObservationTerm A α)) (Q : ℕ) :
    Tendsto (fun M : ℕ =>
      (∑ j ∈ Finset.Ico M (2 * M), (1 / 2 : ℝ) ^ j *
        supportObservationMass A α (Q * 2 ^ j)) / M) atTop (nhds 0) := by
  classical
  have hupper : ∀ M : ℕ,
      (∑ j ∈ Finset.Ico M (2 * M), (1 / 2 : ℝ) ^ j *
        supportObservationMass A α (Q * 2 ^ j)) / M ≤
      (2 * (Q : ℝ) * ∑' a : ℕ, weightedObservationTerm A α a) / M := by
    intro M
    exact div_le_div_of_nonneg_right
      (dyadic_supportObservationMass_sum_le A α hα hs _ Q) (Nat.cast_nonneg M)
  have hlower : ∀ M : ℕ, 0 ≤
      (∑ j ∈ Finset.Ico M (2 * M), (1 / 2 : ℝ) ^ j *
        supportObservationMass A α (Q * 2 ^ j)) / M := by
    intro M
    apply div_nonneg _ (Nat.cast_nonneg M)
    apply Finset.sum_nonneg
    intro j hj
    apply mul_nonneg (by positivity)
    unfold supportObservationMass
    apply Finset.sum_nonneg
    intro a ha
    exact hα a (Finset.mem_filter.mp ha).2.2
  exact squeeze_zero hlower hupper
    (tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop)

/-- More strongly, the full dyadic error series is summable. -/
theorem summable_dyadic_supportObservationMass (A : Set ℕ) (α : ℕ → ℝ)
    (hα : ∀ a ∈ A, 0 ≤ α a)
    (hs : Summable (weightedObservationTerm A α)) (Q : ℕ) :
    Summable (fun j : ℕ => (1 / 2 : ℝ) ^ j *
      supportObservationMass A α (Q * 2 ^ j)) := by
  classical
  apply summable_of_sum_le (c := 2 * (Q : ℝ) * ∑' a, weightedObservationTerm A α a)
  · intro j
    apply mul_nonneg (by positivity)
    unfold supportObservationMass
    apply Finset.sum_nonneg
    intro a ha
    exact hα a (Finset.mem_filter.mp ha).2.2
  · intro J
    exact dyadic_supportObservationMass_sum_le A α hα hs J Q

#print axioms dyadic_supportObservationMass_sum_le
#print axioms tendsto_dyadic_supportObservationMass_mean
#print axioms summable_dyadic_supportObservationMass

end
end ErdosProblems.Erdos257
