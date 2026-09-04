/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib
import Erdos257PeriodNoncollapse.AllBaseReciprocalSupportIrrationality

/-!
# Deliberate mismatch for the #257 reciprocal-summable support theorem

This declaration adds an irrelevant `True` hypothesis.  It can still reuse
the source proof, but its type is not the Challenge type; Comparator must
reject it as a declaration mismatch.
-/

namespace Erdos249257.ExternalVerification257ReciprocalSupport

noncomputable section

noncomputable def supportReciprocalTerm (A : Set ℕ) (a : ℕ) : ℝ :=
  Set.indicator A (fun a : ℕ => (1 : ℝ) / (a : ℝ)) a

noncomputable def supportPowerSeries (b : ℕ) (A : Set ℕ) : ℝ :=
  ∑' a : ℕ, Set.indicator A
    (fun a : ℕ => (1 : ℝ) / ((b : ℝ) ^ a - 1)) a

theorem irrational_supportPowerSeries_of_summable_reciprocal
    (b : ℕ) (A : Set ℕ) (hb : 2 ≤ b) (hA : A.Infinite)
    (hsum : Summable (supportReciprocalTerm A)) (hweak : True) :
    Irrational (supportPowerSeries b A) := by
  simpa [supportReciprocalTerm, supportPowerSeries,
    Erdos257PeriodNoncollapse.reciprocalSupportTerm,
    Erdos257PeriodNoncollapse.erdosSupportSeries] using
    Erdos257PeriodNoncollapse.irrational_erdosSupportSeries_of_summable_reciprocal
      b A hb hA hsum

end

end Erdos249257.ExternalVerification257ReciprocalSupport
