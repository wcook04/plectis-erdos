/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib
import ErdosProblems.Erdos68.CompanionOrbitRationality

/-!
# Source transport for the Erdős #68 companion-orbit rationality boundary

The proof exposes three source-independent, Mathlib-only Comparator
statements. The generic shift boundary comes first because it is the widest
coordinate: it holds at every real base point. The named-series boundary is
the specialisation at the companion constant of `∑_{d≥2} 1/(d! - 1)`, and the
exponential identity is the evaluation that makes that specialisation exact.

Each theorem is an equivalence in both directions. None of them produces the
cofinal misses of the exceptional residue, so none of them proves
irrationality of the Erdős #68 series.
-/

namespace Erdos249257.ExternalVerification68CompanionOrbitBoundary

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

noncomputable def unitFactTerm (n : ℕ) : ℝ :=
  if 2 ≤ n then (1 : ℝ) / ((n.factorial : ℝ)) else 0

noncomputable def facFloor (x : ℝ) (m : ℕ) : ℤ :=
  ⌊(m.factorial : ℝ) * x⌋

noncomputable def canonicalDigit (x : ℝ) (m : ℕ) : ℤ :=
  facFloor x m - (m : ℤ) * facFloor x (m - 1)

private theorem unitFactTerm_eq :
    unitFactTerm = ErdosProblems.Erdos68.unitFactTerm := rfl

private theorem facFloor_eq :
    facFloor = ErdosProblems.Erdos68.facFloor := rfl

private theorem canonicalDigit_eq :
    canonicalDigit = ErdosProblems.Erdos68.canonicalDigit := rfl

private theorem companionConstant_eq :
    companionConstant = ErdosProblems.Erdos68.companionConstant := rfl

private theorem factorialGapSeries_eq :
    factorialGapSeries = Erdos68.factorialGapSeries := rfl

theorem companionOrbitBoundary_genericShift (x : ℝ) :
    (¬Irrational (x + ∑' n : ℕ, unitFactTerm n) ↔
      ∃ M : ℕ, ∀ m : ℕ, M ≤ m → canonicalDigit x m = (m : ℤ) - 2) ∧
    (¬Irrational (x + ∑' n : ℕ, unitFactTerm n) ↔
      ∃ M : ℕ, ∀ m : ℕ, M ≤ m →
        ((facFloor x m + 2 : ℤ) % (m : ℤ)) = 0) := by
  rw [unitFactTerm_eq, canonicalDigit_eq, facFloor_eq]
  exact
    ⟨ErdosProblems.Erdos68.not_irrational_add_unitFact_iff_eventually_canonicalDigit_eq_sub_two x,
      ErdosProblems.Erdos68.not_irrational_add_unitFact_iff_eventually_facFloor_mod_neg_two x⟩

theorem companionOrbitBoundary_factorialGapSeries :
    (¬Irrational factorialGapSeries ↔
      ∃ M : ℕ, ∀ m : ℕ, M ≤ m →
        ((facFloor companionConstant m + 2 : ℤ) % (m : ℤ)) = 0) ∧
    (Irrational factorialGapSeries ↔
      ∀ B : ℕ, ∃ m : ℕ, B < m ∧
        ((facFloor companionConstant m + 2 : ℤ) % (m : ℤ)) ≠ 0) := by
  rw [factorialGapSeries_eq, companionConstant_eq, facFloor_eq]
  exact
    ⟨ErdosProblems.Erdos68.not_irrational_factorialGapSeries_iff_eventually_companion_floor_neg_two,
      ErdosProblems.Erdos68.irrational_factorialGapSeries_iff_cofinal_companion_floor_misses⟩

theorem tsum_unitFactTerm_eq_exp_one_sub_two :
    (∑' n : ℕ, unitFactTerm n) = Real.exp 1 - 2 := by
  rw [unitFactTerm_eq]
  exact ErdosProblems.Erdos68.tsum_unitFactTerm_eq_exp_one_sub_two

end

end Erdos249257.ExternalVerification68CompanionOrbitBoundary
