/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib
import ErdosProblems.Erdos68.PaperCompleteGcdSegment

/-!
# Source transport for the factorial-gap quotient gcd and terminal-block segment

The proof transports the two project theorems into the literal, Mathlib-only
Challenge statements.  The local `channelLCM` unfolds to the project definition,
so the segment inequality transports without restating the bound.
-/

namespace Erdos249257.ExternalVerification68GapGcd

open scoped BigOperators

def channelLCM (D : ℕ) : ℕ :=
  (Finset.Icc 2 D).lcm (fun d => d.factorial - 1)

theorem factorial_gap_gcd {i j : ℕ} (hi : 2 ≤ i) (hij : i < j) :
    Nat.gcd (i.factorial - 1) (j.factorial - 1) ∣
        j.factorial / i.factorial - 1 ∧
    Nat.gcd (i.factorial - 1) (j.factorial - 1) ≤
        j.factorial / i.factorial - 1 ∧
    j.factorial / i.factorial - 1 < j ^ (j - i) :=
  ErdosProblems.Erdos68.PaperComplete.factorial_gap_gcd hi hij

theorem segment_inequality {N k : ℕ} (hk : 2 ≤ k) (hkN : k ≤ N - 1) :
    (∑ n ∈ Finset.Icc (N - k + 1) N,
        Real.log ((n.factorial - 1 : ℕ) : ℝ)) ≤
      Real.log (channelLCM N : ℝ) +
        ((k + 1).choose 3 : ℝ) * Real.log (N : ℝ) := by
  simpa only [channelLCM, _root_.Erdos68.channelLCM] using
    ErdosProblems.Erdos68.PaperComplete.segment_inequality hk hkN

end Erdos249257.ExternalVerification68GapGcd
