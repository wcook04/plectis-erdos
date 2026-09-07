/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import ErdosProblems.Erdos257.HalfCounterexampleFrontier

namespace Erdos249257.ExternalVerification257TerminalScaledVanishing

open Filter Set

noncomputable section

noncomputable def supportCoeff (A : Set ℕ) (n : ℕ) : ℕ :=
  Erdos257PeriodNoncollapse.supportCoeff A n

def affineBinaryOrbit (a : ℕ → ℤ) (u0 : ℤ) : ℕ → ℤ :=
  Erdos257PeriodNoncollapse.affineBinaryOrbit a u0

noncomputable def integerHalfCarry (A : Set ℕ) : ℕ → ℤ :=
  Erdos257PeriodNoncollapse.HalfCarryReachability.integerHalfCarry A

abbrev HalfWord (N : ℕ) := Fin (N + 1) → Bool

def wordSupport {N : ℕ} (a : HalfWord N) : Set ℕ :=
  Erdos257PeriodNoncollapse.HalfCarryReachability.wordSupport a

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
  Erdos257PeriodNoncollapse.erdosSupportSeries b A

def UniversalMersenneSubseriesIrrationality : Prop :=
  ∀ A : Set ℕ, A.Infinite → Irrational (erdosSupportSeries 2 A)

theorem terminalScaledVanishing_completeCounterexample
    (S : HalfTerminalOnlyScaledVanishingSequence) :
    (∃ A : Set ℕ, A.Infinite ∧
      erdosSupportSeries 2 A = (1 : ℝ) / 2) ∧
    ¬ UniversalMersenneSubseriesIrrationality := by
  let S' :
      Erdos257PeriodNoncollapse.HalfCarryReachability.HalfTerminalOnlyScaledVanishingSequence :=
    { depth := S.depth
      word := S.word
      depth_pos := S.depth_pos
      depth_tendsto := S.depth_tendsto
      zero := S.zero
      one := S.one
      carry_scaled_tendsto := by
        simpa [integerHalfCarry, wordSupport] using
          S.carry_scaled_tendsto }
  constructor
  · simpa [erdosSupportSeries] using
      ErdosProblems.Erdos257.exists_rational_half_counterexample_of_terminalScaledVanishing
        S'
  · simpa [UniversalMersenneSubseriesIrrationality, erdosSupportSeries,
      ErdosProblems.Erdos257.UniversalMersenneSubseriesIrrationality] using
      ErdosProblems.Erdos257.not_universal_of_terminalScaledVanishing S'

end

end Erdos249257.ExternalVerification257TerminalScaledVanishing
