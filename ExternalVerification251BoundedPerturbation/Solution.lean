import Mathlib
import ErdosProblems.Erdos251.BoundedPerturbationCountermodel

/-!
# Bounded-perturbation obstruction

The statements quantify over arbitrary convergent natural-digit dyadic series.
They retain the positive perturbation size, arbitrary finite prefix, and the
whole admissible perturbation family. No prime-gap property is substituted
for the stated invariance hypothesis.
-/

namespace Erdos249257.ExternalVerification251BoundedPerturbation

theorem exists_rational_bounded_perturbation {g : ℕ → ℕ} {S : ℝ}
    (hS : HasSum (fun n => (g n : ℝ) / 2 ^ (n + 1)) S)
    (M : ℕ) (hM : 0 < M) (K : ℕ) :
    ∃ (δ : ℕ → ℕ) (r : ℚ), (∀ n, δ n ≤ 1) ∧ (∀ n < K, δ n = 0) ∧
      HasSum (fun n => ((g n + M * δ n : ℕ) : ℝ) / 2 ^ (n + 1)) r := by
  exact ErdosProblems.Erdos251.exists_rational_bounded_perturbation hS M hM K

theorem not_forall_irrational_of_bounded_perturbation_invariant
    {P : (ℕ → ℕ) → Prop} {g : ℕ → ℕ} {S : ℝ}
    (hS : HasSum (fun n => (g n : ℝ) / 2 ^ (n + 1)) S)
    (M : ℕ) (hM : 0 < M) (K : ℕ)
    (hP : ∀ δ : ℕ → ℕ, (∀ n, δ n ≤ 1) → (∀ n < K, δ n = 0) →
      P (fun n => g n + M * δ n)) :
    ¬ ∀ a : ℕ → ℕ, P a →
      Irrational (∑' n : ℕ, (a n : ℝ) / 2 ^ (n + 1)) := by
  exact ErdosProblems.Erdos251.not_forall_irrational_of_bounded_perturbation_invariant hS M hM K hP

end Erdos249257.ExternalVerification251BoundedPerturbation
