/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Erdos257PeriodNoncollapse.RationalSupportCarrySkeleton

/-! Deliberate mismatch: the strict dyadic mass conclusion has an extra
`True` hypothesis.  Comparator must reject this declaration type. -/

namespace Erdos249257.ExternalVerification257RationalTailRigidity

open Set

noncomputable section

noncomputable def erdosSupportSeries (b : ℕ) (A : Set ℕ) : ℝ :=
  ∑' a : ℕ, Set.indicator A (fun a => (1 : ℝ) / ((b : ℝ) ^ a - 1)) a

noncomputable def reciprocalSupportTerm (A : Set ℕ) (a : ℕ) : ℝ :=
  Set.indicator A (fun a : ℕ => (1 : ℝ) / (a : ℝ)) a

noncomputable def reciprocalMass (A : Set ℕ) : ℝ :=
  ∑' a : ℕ, reciprocalSupportTerm A a

theorem dyadic_support_fraction_reciprocalMass_diverges_or_gt_one
    (_extra : True) (A : Set ℕ) (hAinf : A.Infinite) (p : ℤ) (c : ℕ)
    (hvalue : erdosSupportSeries 2 A =
      (p : ℝ) / ((2 ^ c : ℕ) : ℝ)) :
    ¬ Summable (reciprocalSupportTerm A) ∨ 1 < reciprocalMass A := by
  simpa [reciprocalSupportTerm, reciprocalMass, erdosSupportSeries,
    Erdos257PeriodNoncollapse.reciprocalSupportTerm,
    Erdos257PeriodNoncollapse.reciprocalMass,
    Erdos257PeriodNoncollapse.erdosSupportSeries] using
      Erdos257PeriodNoncollapse.dyadic_support_fraction_reciprocalMass_diverges_or_gt_one
        A hAinf p c (by
          simpa [erdosSupportSeries,
            Erdos257PeriodNoncollapse.erdosSupportSeries] using hvalue)

end

end Erdos249257.ExternalVerification257RationalTailRigidity
