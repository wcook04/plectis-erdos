/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib

namespace Erdos249257.ExternalVerification257TerminalScaledVanishing

open Filter Set

noncomputable section

noncomputable def supportCoeff (A : Set ℕ) (n : ℕ) : ℕ :=
  letI := Classical.decPred fun d : ℕ => d ∈ A
  (n.divisors.filter fun d => d ∈ A).card

def affineBinaryOrbit (a : ℕ → ℤ) (u0 : ℤ) : ℕ → ℤ
  | 0 => u0
  | n + 1 => 2 * affineBinaryOrbit a u0 n - a (n + 1)

noncomputable def integerHalfCarry (A : Set ℕ) : ℕ → ℤ :=
  affineBinaryOrbit (fun n : ℕ ↦ (supportCoeff A (n + 1) : ℤ)) 1

abbrev HalfWord (N : ℕ) := Fin (N + 1) → Bool

def wordSupport {N : ℕ} (a : HalfWord N) : Set ℕ :=
  {n | ∃ h : n < N + 1, a ⟨n, h⟩ = true}

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

noncomputable def erdosSupportSeries (b : ℕ) (A : Set ℕ) : ℝ :=
  ∑' a : ℕ, Set.indicator A
    (fun a => (1 : ℝ) / ((b : ℝ) ^ a - 1)) a

def UniversalMersenneSubseriesIrrationality : Prop :=
  ∀ A : Set ℕ, A.Infinite → Irrational (erdosSupportSeries 2 A)

/-- Deliberate mismatch: the extra True hypothesis must be rejected. -/
theorem terminalScaledVanishing_completeCounterexample
    (S : HalfTerminalOnlyScaledVanishingSequence) :
    True →
    (∃ A : Set ℕ, A.Infinite ∧
      erdosSupportSeries 2 A = (1 : ℝ) / 2) ∧
    ¬ UniversalMersenneSubseriesIrrationality := by
  sorry

end

end Erdos249257.ExternalVerification257TerminalScaledVanishing
