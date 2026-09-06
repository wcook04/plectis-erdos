/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib

/-!
# Trusted challenge for the Erdős #251 bounded-perturbation countermodel

Let `g n = p_{n+1} - p_n` be the actual consecutive prime gaps, zero-based with
`p_0 = 2`.  This Mathlib-only statement exposes five declarations.

For every `M ≥ 1` and every `K` there are digits `δ n ∈ {0,1}`, vanishing for
every `n < K`, such that `∑ (g n + M * δ n) / 2^(n+1)` is a rational number and
therefore fails to be irrational.  Pointwise, each perturbed gap lies in
`[g n, g n + M]` and is congruent to `g n` modulo `M`.

The general mechanism holds for any natural-digit dyadic series: if
`∑ g n / 2^(n+1)` has sum `S`, then for every `M ≥ 1`, every `K`, and every real
`r` with `S < r < S + M / 2^K` there are digits `δ n ∈ {0,1}`, vanishing below
`K`, with `∑ (g n + M * δ n) / 2^(n+1) = r`.  The digit supply is the binary
expansion: for `0 ≤ D < 1` the digits `⌊2^(n+1) D⌋ - 2⌊2^n D⌋` sum to `D`
against the weights `2^{-(n+1)}`.

Every statement here concerns perturbed gap sequences.  None of them determines
the value of `∑ g n / 2^(n+1)`, so Erdős Problem 251 is open here.  The
consequence they support is a no-go: a hypothesis on a gap sequence that
survives the replacement `g n ↦ g n + M * δ n` with `δ n ∈ {0,1}` is consistent
with a rational dyadic sum, so it cannot imply irrationality.
-/

open scoped BigOperators

namespace Erdos249257.ExternalVerification251BoundedPerturbationCountermodel

/-- Zero-based prime enumeration. -/
noncomputable def prime0 (n : ℕ) : ℕ :=
  Nat.nth Nat.Prime n

/-- Zero-based consecutive prime gap. -/
noncomputable def primeGap0 (n : ℕ) : ℕ :=
  prime0 (n + 1) - prime0 n

/-- The `n`th binary digit (after the point) of `D`: `⌊2^{n+1} D⌋ - 2⌊2^n D⌋`. -/
noncomputable def binaryDigit (D : ℝ) (n : ℕ) : ℤ :=
  ⌊(2 : ℝ) ^ (n + 1) * D⌋ - 2 * ⌊(2 : ℝ) ^ n * D⌋

/-- **Bounded-perturbation countermodel for the actual prime gaps.**  For every
`M ≥ 1` and every `K` there are digits `δ n ∈ {0,1}`, zero for `n < K`, whose
perturbed prime-gap dyadic series has a value that is not irrational. -/
theorem not_irrational_bounded_perturbation_primeGap (M : ℕ) (hM : 0 < M) (K : ℕ) :
    ∃ δ : ℕ → ℕ, (∀ n, δ n ≤ 1) ∧ (∀ n < K, δ n = 0) ∧
      ¬ Irrational (∑' n, ((primeGap0 n + M * δ n : ℕ) : ℝ) / 2 ^ (n + 1)) := by
  sorry

/-- The same digits carry an explicit rational witness `r` with
`∑ (g n + M * δ n) / 2^(n+1) = r`. -/
theorem exists_rational_bounded_perturbation_primeGap (M : ℕ) (hM : 0 < M) (K : ℕ) :
    ∃ (δ : ℕ → ℕ) (r : ℚ), (∀ n, δ n ≤ 1) ∧ (∀ n < K, δ n = 0) ∧
      HasSum (fun n => ((primeGap0 n + M * δ n : ℕ) : ℝ) / 2 ^ (n + 1)) r := by
  sorry

/-- Pointwise perturbation bounds: every perturbed gap lies in `[g n, g n + M]`
and is congruent to `g n` modulo `M`. -/
theorem perturbed_gap_bounds (M : ℕ) (δ : ℕ → ℕ) (hδ : ∀ n, δ n ≤ 1) (n : ℕ) :
    primeGap0 n ≤ primeGap0 n + M * δ n ∧ primeGap0 n + M * δ n ≤ primeGap0 n + M ∧
      (primeGap0 n + M * δ n) % M = primeGap0 n % M := by
  sorry

/-- **Bounded-perturbation countermodel, general form.**  If the natural-digit
dyadic series `∑ g n / 2^(n+1)` has sum `S`, then for every `M ≥ 1`, every real
`r` with `S < r < S + M / 2^K`, there are digits `δ n ∈ {0,1}`, vanishing for
`n < K`, with `∑ (g n + M * δ n) / 2^(n+1) = r`. -/
theorem exists_bounded_perturbation {g : ℕ → ℕ} {S : ℝ}
    (hS : HasSum (fun n => (g n : ℝ) / 2 ^ (n + 1)) S) (M : ℕ) (hM : 0 < M)
    (r : ℝ) (hr₁ : S < r) (K : ℕ) (hK : r < S + M / 2 ^ K) :
    ∃ δ : ℕ → ℕ, (∀ n, δ n ≤ 1) ∧ (∀ n < K, δ n = 0) ∧
      HasSum (fun n => ((g n + M * δ n : ℕ) : ℝ) / 2 ^ (n + 1)) r := by
  sorry

/-- The digit supply: `∑ δ n / 2^(n+1) = D` for `0 ≤ D < 1`. -/
theorem hasSum_binaryDigit (D : ℝ) (h0 : 0 ≤ D) (h1 : D < 1) :
    HasSum (fun n : ℕ => (binaryDigit D n : ℝ) / 2 ^ (n + 1)) D := by
  sorry

end Erdos249257.ExternalVerification251BoundedPerturbationCountermodel
