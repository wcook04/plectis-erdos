import ErdosProblems.Erdos257.PaperCompleteR8.CountableCoverLogBudget

/-! # Optimizing the actual countable positive-cover cost

The admissible objects contain literal frames, divisor coefficients and the
paper's explicit summability hypotheses. Their costs are optimized only when
at least one admissible cover exists; the separate nonexistence theorem does
not assign a fictitious value to the real infimum of an empty set.
-/
noncomputable section
namespace ErdosProblems.Erdos257.PaperCompleteR8

/-- The paper's arbitrary-weight positive-cover data on an actual support. -/
structure LogBudgetCover (A : Set ℕ) where
  frame : ℕ → Finset ℕ
  weight : ℕ → ℝ
  exponent : ℕ → ℝ
  coefficient : ℕ → ℕ → ℝ
  frame_positive : ∀ j, 0 ∉ frame j
  weight_positive : ∀ j, 0 < weight j
  weight_sum : HasSum weight 1
  exponent_bounds : ∀ j, 0 < exponent j ∧ exponent j ≤ 1
  coefficient_nonneg : ∀ j d, 0 < d → 0 ≤ coefficient j d
  column_summable : ∀ j, Summable (fun d : ℕ => coefficient j d / (d : ℝ))
  covers : ∀ a ∈ A, ∃ j, a ∈ frame j
  majorises : ∀ j n, 0 < n →
    (((frame j).filter (fun a => a ∣ n)).card : ℝ) ^ exponent j ≤
      ∑ d ∈ n.divisors, coefficient j d
  budget_summable : Summable (fun j =>
    (∑' d : ℕ, coefficient j d / (d : ℝ)) /
      (weight j ^ exponent j) / ((2 : ℝ) ^ exponent j - 1))

def LogBudgetCover.cost {A : Set ℕ} (C : LogBudgetCover A) : ℝ :=
  ∑' j, (∑' d : ℕ, C.coefficient j d / (d : ℝ)) /
    (C.weight j ^ C.exponent j) / ((2 : ℝ) ^ C.exponent j - 1)

def finiteLogarithmicMean (F : Finset ℕ) (X : ℕ) : ℝ :=
  (∑ n ∈ Finset.Icc 1 X,
    Real.exp 1 * Real.log ((F.filter (fun a => a ∣ n)).card : ℝ)) / X

/-- A finite covered test support bounds every admissible countable cost. -/
theorem finiteLogarithmicMean_le_cost {A : Set ℕ} (C : LogBudgetCover A)
    (F : Finset ℕ) (hFA : (F : Set ℕ) ⊆ A) (X : ℕ) (hX : 0 < X) :
    finiteLogarithmicMean F X ≤ C.cost := by
  exact countable_cover_log_mean_le_cost F C.frame C.weight C.exponent C.coefficient
    X hX C.weight_sum C.weight_positive C.exponent_bounds C.coefficient_nonneg
    C.column_summable (fun a ha => C.covers a (hFA ha)) C.majorises C.budget_summable

def admissibleLogCoverCosts (A : Set ℕ) : Set ℝ :=
  Set.range (fun C : LogBudgetCover A => C.cost)

def optimizedLogCoverCost (A : Set ℕ) : ℝ := sInf (admissibleLogCoverCosts A)

/-- Optimization preserves the obstruction for any support admitting a cover.
The existence premise is about literal admissible data, not the desired bound. -/
theorem finiteLogarithmicMean_le_optimizedCost {A : Set ℕ}
    (C : LogBudgetCover A) (F : Finset ℕ) (hFA : (F : Set ℕ) ⊆ A)
    (X : ℕ) (hX : 0 < X) :
    finiteLogarithmicMean F X ≤ optimizedLogCoverCost A := by
  apply le_csInf (show (admissibleLogCoverCosts A).Nonempty from ⟨C.cost, ⟨C, rfl⟩⟩)
  intro x hx
  obtain ⟨D, rfl⟩ := hx
  exact finiteLogarithmicMean_le_cost D F hFA X hX

/-- Unbounded finite logarithmic means exclude every finite-cost positive cover. -/
theorem no_logBudgetCover_of_unbounded_finite_means (A : Set ℕ)
    (hlarge : ∀ R : ℝ, ∃ F : Finset ℕ, (F : Set ℕ) ⊆ A ∧
      ∃ X : ℕ, 0 < X ∧ R < finiteLogarithmicMean F X) :
    IsEmpty (LogBudgetCover A) := by
  refine ⟨fun C => ?_⟩
  obtain ⟨F, hFA, X, hX, hlargeX⟩ := hlarge C.cost
  exact (not_lt_of_ge (finiteLogarithmicMean_le_cost C F hFA X hX)) hlargeX

end ErdosProblems.Erdos257.PaperCompleteR8
end
