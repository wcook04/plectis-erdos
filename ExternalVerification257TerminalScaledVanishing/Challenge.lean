/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib

/-!
# Trusted challenge for the terminal scaled-vanishing counterexample endpoint

A cofinal sequence of finite Boolean support words whose normalized terminal
carry tends to zero already produces an infinite support with Mersenne
subseries exactly equal to one half. Consequently that same hypothesis
refutes the universal irrationality assertion in Erdős Problem 257.

The theorem is conditional. It does not construct the sequence, prove that
one half belongs to the achievement set, or settle the parent problem.
-/

namespace Erdos249257.ExternalVerification257TerminalScaledVanishing

open Filter Set

noncomputable section

/-- Divisor-incidence coefficient of a support. -/
noncomputable def supportCoeff (A : Set ℕ) (n : ℕ) : ℕ :=
  letI := Classical.decPred fun d : ℕ => d ∈ A
  (n.divisors.filter fun d => d ∈ A).card

/-- Binary affine orbit driven by the coefficient sequence. -/
def affineBinaryOrbit (a : ℕ → ℤ) (u0 : ℤ) : ℕ → ℤ
  | 0 => u0
  | n + 1 => 2 * affineBinaryOrbit a u0 n - a (n + 1)

/-- Integer half-carry attached to a support. -/
noncomputable def integerHalfCarry (A : Set ℕ) : ℕ → ℤ :=
  affineBinaryOrbit (fun n : ℕ ↦ (supportCoeff A (n + 1) : ℤ)) 1

/-- Boolean support word through depth N. -/
abbrev HalfWord (N : ℕ) := Fin (N + 1) → Bool

/-- Set represented by a finite Boolean word. -/
def wordSupport {N : ℕ} (a : HalfWord N) : Set ℕ :=
  {n | ∃ h : n < N + 1, a ⟨n, h⟩ = true}

/-- The exact terminal scaled-vanishing hypothesis.

The finite words exclude ranks zero and one, their depths tend to infinity,
and their absolute terminal carry divided by the binary place value tends to
zero. No compatibility between successive words is assumed. -/
structure HalfTerminalOnlyScaledVanishingSequence where
  depth : ℕ → ℕ
  word : ∀ n : ℕ, HalfWord (depth n)
  depth_pos : ∀ n : ℕ, 1 ≤ depth n
  depth_tendsto : Tendsto depth atTop atTop
  zero : ∀ n : ℕ,
    word n ⟨0, Nat.zero_lt_succ (depth n)⟩ = false
  one : ∀ (n : ℕ) (h : 1 < depth n + 1), word n ⟨1, h⟩ = false
  carry_scaled_tendsto :
    Tendsto
      (fun n : ℕ ↦
        |(integerHalfCarry (wordSupport (word n)) (depth n - 1) : ℝ)| /
          (2 : ℝ) ^ depth n)
      atTop (nhds 0)

/-- The base-b reciprocal-Mersenne support series. -/
noncomputable def erdosSupportSeries (b : ℕ) (A : Set ℕ) : ℝ :=
  ∑' a : ℕ, Set.indicator A
    (fun a => (1 : ℝ) / ((b : ℝ) ^ a - 1)) a

/-- The universal irrationality assertion in Erdős Problem 257. -/
def UniversalMersenneSubseriesIrrationality : Prop :=
  ∀ A : Set ℕ, A.Infinite → Irrational (erdosSupportSeries 2 A)

/-- Complete conditional counterexample endpoint.

Terminal scaled vanishing produces an infinite support of exact value one
half and, at the problem level, refutes the universal irrationality
assertion. The open producer remains the existence of the input sequence. -/
theorem terminalScaledVanishing_completeCounterexample
    (S : HalfTerminalOnlyScaledVanishingSequence) :
    (∃ A : Set ℕ, A.Infinite ∧
      erdosSupportSeries 2 A = (1 : ℝ) / 2) ∧
    ¬ UniversalMersenneSubseriesIrrationality := by
  sorry

end

end Erdos249257.ExternalVerification257TerminalScaledVanishing
