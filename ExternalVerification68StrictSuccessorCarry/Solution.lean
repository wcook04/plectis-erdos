/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib
import ErdosProblems.Erdos68.CompanionOrbitRationality

/-!
# Source transport for the Erdős #68 companion-orbit and strict-successor characterizations

The proof exposes two source-independent, Mathlib-only Comparator statements.
The fixed companion orbit comes first because it is the strongest exact
coordinate: its cofinal-miss assertion is equivalent to irrationality, not
assumed or proved separately.  The strict-successor theorem then supplies the
parallel exact integer-divisibility coordinate.  Neither theorem produces the
cofinal misses, so neither solves Erdős #68.
-/

namespace Erdos249257.ExternalVerification68StrictSuccessorCarry

noncomputable section

noncomputable def factorialGapSeries : ℝ :=
  ∑' d : ℕ, if 1 < d then
    (1 : ℝ) / ((((d.factorial : ℤ) - 1 : ℤ) : ℝ))
  else 0

noncomputable def companionConstant : ℝ :=
  ∑' n : ℕ, if 2 ≤ n then
    (1 : ℝ) /
      ((n.factorial : ℝ) * ((((n.factorial : ℤ) - 1 : ℤ) : ℝ)))
  else 0

noncomputable def facFloor (x : ℝ) (m : ℕ) : ℤ :=
  ⌊(m.factorial : ℝ) * x⌋

def factorialGapPrefix (n : ℕ) : ℚ :=
  ∑ k ∈ Finset.Icc 2 n, 1 / ((k.factorial : ℚ) - 1)

noncomputable def strictFacTop (x : ℝ) (n : ℕ) : ℤ :=
  ⌊(n.factorial : ℝ) * x⌋ + 1

def strictFacTopRat (x : ℚ) (n : ℕ) : ℤ :=
  ⌊(n.factorial : ℚ) * x⌋ + 1

noncomputable def factorialGapPredecessorGap (m : ℕ) : ℝ :=
  (strictFacTop
      ((factorialGapPrefix (m - 1) : ℚ) : ℝ) (m - 1) : ℝ) -
    ((m - 1).factorial : ℝ) *
      ((factorialGapPrefix (m - 1) : ℚ) : ℝ)

noncomputable def factorialGapStepCarry (m : ℕ) : ℤ :=
  -⌊1 + 1 / ((m.factorial : ℝ) - 1) -
      (m : ℝ) * factorialGapPredecessorGap m⌋

theorem companionOrbit_completeCharacterization :
    (¬Irrational factorialGapSeries ↔
      ∃ M : ℕ, ∀ m : ℕ, M ≤ m →
        ((facFloor companionConstant m + 2 : ℤ) % (m : ℤ)) = 0) ∧
    (Irrational factorialGapSeries ↔
      ∀ B : ℕ, ∃ m : ℕ, B < m ∧
        ((facFloor companionConstant m + 2 : ℤ) % (m : ℤ)) ≠ 0) := by
  constructor
  · simpa [factorialGapSeries, Erdos68.factorialGapSeries,
      Erdos68.factorialGapTail, Erdos68.factorialGapTailTerm,
      companionConstant, ErdosProblems.Erdos68.companionConstant,
      ErdosProblems.Erdos68.compConstTerm, facFloor,
      ErdosProblems.Erdos68.facFloor] using
      ErdosProblems.Erdos68.not_irrational_factorialGapSeries_iff_eventually_companion_floor_neg_two
  · simpa [factorialGapSeries, Erdos68.factorialGapSeries,
      Erdos68.factorialGapTail, Erdos68.factorialGapTailTerm,
      companionConstant, ErdosProblems.Erdos68.companionConstant,
      ErdosProblems.Erdos68.compConstTerm, facFloor,
      ErdosProblems.Erdos68.facFloor] using
      ErdosProblems.Erdos68.irrational_factorialGapSeries_iff_cofinal_companion_floor_misses

theorem strictSuccessorCarry_completeCharacterization :
    (¬Irrational factorialGapSeries ↔
      ∃ M : ℕ, ∀ m : ℕ, M ≤ m → factorialGapStepCarry m = 1) ∧
    (Irrational factorialGapSeries ↔
      ∀ B : ℕ, ∃ m : ℕ, B < m ∧ factorialGapStepCarry m ≠ 1) ∧
    (∀ m : ℕ, 3 ≤ m →
      (factorialGapStepCarry m = 1 ↔
        (m : ℤ) ∣ strictFacTopRat (factorialGapPrefix m) m)) ∧
    (Irrational factorialGapSeries ↔
      ∀ B : ℕ, ∃ m : ℕ, B < m ∧
        ¬((m : ℤ) ∣ strictFacTopRat (factorialGapPrefix m) m)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [factorialGapSeries, Erdos68.factorialGapSeries,
      Erdos68.factorialGapTail, Erdos68.factorialGapTailTerm,
      factorialGapStepCarry, factorialGapPredecessorGap, strictFacTop,
      factorialGapPrefix,
      ErdosProblems.Erdos68.factorialGapStepCarry,
      ErdosProblems.Erdos68.factorialGapPredecessorGap,
      ErdosProblems.Erdos68.strictFacTop,
      ErdosProblems.Erdos68.factorialGapPrefix] using
      ErdosProblems.Erdos68.not_irrational_factorialGapSeries_iff_eventually_unit_carries
  · simpa [factorialGapSeries, Erdos68.factorialGapSeries,
      Erdos68.factorialGapTail, Erdos68.factorialGapTailTerm,
      factorialGapStepCarry, factorialGapPredecessorGap, strictFacTop,
      factorialGapPrefix,
      ErdosProblems.Erdos68.factorialGapStepCarry,
      ErdosProblems.Erdos68.factorialGapPredecessorGap,
      ErdosProblems.Erdos68.strictFacTop,
      ErdosProblems.Erdos68.factorialGapPrefix] using
      ErdosProblems.Erdos68.irrational_factorialGapSeries_iff_cofinal_nonunit_carries
  · intro m hm
    simpa [factorialGapStepCarry, factorialGapPredecessorGap, strictFacTop,
      strictFacTopRat, factorialGapPrefix,
      ErdosProblems.Erdos68.factorialGapStepCarry,
      ErdosProblems.Erdos68.factorialGapPredecessorGap,
      ErdosProblems.Erdos68.strictFacTop,
      ErdosProblems.Erdos68.strictFacTopRat,
      ErdosProblems.Erdos68.factorialGapPrefix] using
      ErdosProblems.Erdos68.factorialGapStepCarry_eq_one_iff_dvd_strictFacTopRat hm
  · simpa [factorialGapSeries, Erdos68.factorialGapSeries,
      Erdos68.factorialGapTail, Erdos68.factorialGapTailTerm,
      strictFacTopRat, factorialGapPrefix,
      ErdosProblems.Erdos68.strictFacTopRat,
      ErdosProblems.Erdos68.factorialGapPrefix] using
      ErdosProblems.Erdos68.irrational_factorialGapSeries_iff_cofinal_strictFacTopRat_misses

end

end Erdos249257.ExternalVerification68StrictSuccessorCarry
