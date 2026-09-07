/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import ErdosProblems.Erdos251.BoundedPerturbationCountermodel

open scoped BigOperators

namespace Erdos249257.ExternalVerification251BoundedPerturbationCountermodel

noncomputable abbrev prime0 := ErdosProblems.Erdos251.prime0
noncomputable abbrev primeGap0 := ErdosProblems.Erdos251.primeGap0
noncomputable abbrev binaryDigit := ErdosProblems.Erdos251.binaryDigit

theorem not_irrational_bounded_perturbation_primeGap (M : ℕ) (hM : 0 < M) (K : ℕ) :
    ∃ δ : ℕ → ℕ, (∀ n, δ n ≤ 1) ∧ (∀ n < K, δ n = 0) ∧
      ¬ Irrational (∑' n, ((primeGap0 n + M * δ n : ℕ) : ℝ) / 2 ^ (n + 1)) :=
  ErdosProblems.Erdos251.not_irrational_bounded_perturbation_primeGap M hM K

theorem exists_rational_bounded_perturbation_primeGap (M : ℕ) (hM : 0 < M) (K : ℕ) :
    ∃ (δ : ℕ → ℕ) (r : ℚ), (∀ n, δ n ≤ 1) ∧ (∀ n < K, δ n = 0) ∧
      HasSum (fun n => ((primeGap0 n + M * δ n : ℕ) : ℝ) / 2 ^ (n + 1)) r :=
  ErdosProblems.Erdos251.exists_rational_bounded_perturbation_primeGap M hM K

theorem perturbed_gap_bounds (M : ℕ) (δ : ℕ → ℕ) (hδ : ∀ n, δ n ≤ 1) (n : ℕ) :
    primeGap0 n ≤ primeGap0 n + M * δ n ∧ primeGap0 n + M * δ n ≤ primeGap0 n + M ∧
      (primeGap0 n + M * δ n) % M = primeGap0 n % M :=
  ErdosProblems.Erdos251.perturbed_gap_bounds M δ hδ n

theorem exists_bounded_perturbation {g : ℕ → ℕ} {S : ℝ}
    (hS : HasSum (fun n => (g n : ℝ) / 2 ^ (n + 1)) S) (M : ℕ) (hM : 0 < M)
    (r : ℝ) (hr₁ : S < r) (K : ℕ) (hK : r < S + M / 2 ^ K) :
    ∃ δ : ℕ → ℕ, (∀ n, δ n ≤ 1) ∧ (∀ n < K, δ n = 0) ∧
      HasSum (fun n => ((g n + M * δ n : ℕ) : ℝ) / 2 ^ (n + 1)) r :=
  ErdosProblems.Erdos251.exists_bounded_perturbation hS M hM r hr₁ K hK

theorem hasSum_binaryDigit (D : ℝ) (h0 : 0 ≤ D) (h1 : D < 1) :
    HasSum (fun n : ℕ => (binaryDigit D n : ℝ) / 2 ^ (n + 1)) D :=
  ErdosProblems.Erdos251.hasSum_binaryDigit D h0 h1

end Erdos249257.ExternalVerification251BoundedPerturbationCountermodel
