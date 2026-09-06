/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib
import Erdos249257.SignedQMomentObstruction
import ErdosProblems.Erdos249.MobiusMersenneLadderSeparation

/-!
# Source transport for the Möbius–Mersenne ladder structure in Erdős #249

The declarations below restate the Mathlib-only challenge vocabulary and
transport the exact source theorems without strengthening their hypotheses.
-/

namespace Erdos249257.ExternalVerification249MobiusMersenneLadderStructure

open scoped BigOperators
open ArithmeticFunction

noncomputable def mobiusMersenneTerm (r n : ℕ) : ℝ :=
  ((moebius (n + 1) : ℤ) : ℝ) /
    (((2 : ℝ) ^ (n + 1) - 1) ^ r)

noncomputable def mobiusMersenneTheta (r : ℕ) : ℝ :=
  ∑' n : ℕ, mobiusMersenneTerm r n

noncomputable def mobiusMersenneLambertRung (r : ℕ) : ℝ :=
  ∑' d : ℕ+, ((moebius (d : ℕ) : ℤ) : ℝ) / ((2 : ℝ) ^ (r * (d : ℕ)) - 1)

private lemma theta_eq (r : ℕ) :
    mobiusMersenneTheta r =
      _root_.Erdos249257.SignedQMomentObstruction.mobiusMersenneTheta r :=
  rfl

private lemma rung_eq (r : ℕ) :
    mobiusMersenneLambertRung r =
      _root_.ErdosProblems.Erdos249.MobiusMersenneLadderSeparation.mobiusMersenneLambertRung r :=
  rfl

theorem mobiusMersenneTheta_no_linearRecurrence_of_eventually
    {m : ℕ} (c : Fin (m + 1) → ℝ) (n₀ : ℕ) (hc : ∃ k, c k ≠ 0)
    (hrec : ∀ n : ℕ, n₀ ≤ n →
      ∑ k : Fin (m + 1), c k * mobiusMersenneTheta (n + (k : ℕ)) = 0) : False := by
  refine _root_.ErdosProblems.Erdos249.MobiusMersenneLadderSeparation.mobiusMersenneTheta_no_linearRecurrence_of_eventually
    c n₀ hc (fun n hn => ?_)
  simpa only [theta_eq] using hrec n hn

theorem mobiusMersenneTheta_no_linearRecurrence :
    ¬ ∃ (m : ℕ) (c : Fin (m + 1) → ℝ), (∃ k, c k ≠ 0) ∧
        ∀ n : ℕ, 1 ≤ n →
          ∑ k : Fin (m + 1), c k * mobiusMersenneTheta (n + (k : ℕ)) = 0 := by
  simpa only [theta_eq] using
    _root_.ErdosProblems.Erdos249.MobiusMersenneLadderSeparation.mobiusMersenneTheta_no_linearRecurrence

theorem mobiusMersenneTheta_strict_logConcave (r : ℕ) (hr : 1 ≤ r) :
    mobiusMersenneTheta r * mobiusMersenneTheta (r + 2) <
      mobiusMersenneTheta (r + 1) ^ 2 := by
  simpa only [theta_eq] using
    _root_.Erdos249257.SignedQMomentObstruction.mobiusMersenneTheta_strict_logConcave
      r hr

theorem mobiusMersenneTheta_hankel_two_neg (r : ℕ) (hr : 1 ≤ r) :
    mobiusMersenneTheta r * mobiusMersenneTheta (r + 2) -
      mobiusMersenneTheta (r + 1) ^ 2 < 0 := by
  simpa only [theta_eq] using
    _root_.Erdos249257.SignedQMomentObstruction.mobiusMersenneTheta_hankel_two_neg
      r hr

theorem mobiusMersenneLambertRung_eq (r : ℕ) (hr : 1 ≤ r) :
    mobiusMersenneLambertRung r = ((1 : ℝ) / 2) ^ r := by
  simpa only [rung_eq] using
    _root_.ErdosProblems.Erdos249.MobiusMersenneLadderSeparation.mobiusMersenneLambertRung_eq r hr

theorem lambertRung_shifted_hankelDet_eq_zero (s N : ℕ) (hs : 1 ≤ s) (hN : 2 ≤ N) :
    Matrix.det (Matrix.of fun i j : Fin N =>
      mobiusMersenneLambertRung (s + (i : ℕ) + (j : ℕ))) = 0 := by
  simpa only [rung_eq] using
    _root_.ErdosProblems.Erdos249.MobiusMersenneLadderSeparation.lambertRung_shifted_hankelDet_eq_zero
      s N hs hN

theorem mobiusMersenneTheta_ne_mobiusMersenneLambertRung :
    ¬ ∀ r : ℕ, 1 ≤ r → mobiusMersenneTheta r = mobiusMersenneLambertRung r := by
  simpa only [theta_eq, rung_eq] using
    _root_.ErdosProblems.Erdos249.MobiusMersenneLadderSeparation.mobiusMersenneTheta_ne_mobiusMersenneLambertRung

end Erdos249257.ExternalVerification249MobiusMersenneLadderStructure
