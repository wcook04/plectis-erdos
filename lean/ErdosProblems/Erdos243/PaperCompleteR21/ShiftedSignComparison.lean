import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Erdős 243: the shifted-sign identity for the growth defect

This file supplies two of the clauses of `long243:res:classicalhalfspace`
in the long note `paper/reasoning-parts/erdos243/core.tex`:

* the displayed identity `long243:eq:shiftedsign`,

  `aₙ² / aₙ₊₁ - 1 = -Eₙ/Cₙ + Λₙ`,
  `Λₙ = (1 - Eₙ/Cₙ)(aₙ - 1 + Eₙ₊₁/Cₙ₊₁) / aₙ₊₁`,

  valid whenever `aₙ₊₁ Cₙ Cₙ₊₁ ≠ 0`;

* the final clause "on a Sylvester tail `Eₙ = 0` and
  `Λₙ = (aₙ - 1)/aₙ₊₁ > 0`".

The data are the paper's one-based exact recurrences of its
Section "Signs of the error and of the growth ratio", stated as hypotheses
on real numbers: `Dₙ₊₁ = aₙ Dₙ`, `Cₙ₊₁ = aₙ Cₙ - Dₙ`,
`Eₙ = Dₙ - (aₙ - 1) Cₙ`.  The remaining clauses of that proposition (the
divisibility `Mₙ ∣ Gₙ`, the integrality and sign of `Eₙ/Mₙ`, the eventual
bound `0 < Λₙ < 3/aₙ`, and the statements about the Erdős–Straus quantity
`Zₙ^ES`) are not proved here.
-/

namespace ErdosProblems.Erdos243.PaperCompleteR21

/-- The correction term `Λₙ` of `long243:eq:shiftedsign`. -/
noncomputable def shiftedSignCorrection
    (a aNext C CNext E ENext : ℝ) : ℝ :=
  (1 - E / C) * (a - 1 + ENext / CNext) / aNext

/-- **The shifted-sign identity `long243:eq:shiftedsign`.**
For the exact recurrences `Dₙ₊₁ = aₙ Dₙ`, `Cₙ₊₁ = aₙ Cₙ - Dₙ` and the
centred error `Eₙ = Dₙ - (aₙ - 1) Cₙ`, whenever `aₙ₊₁ Cₙ Cₙ₊₁ ≠ 0`,

`aₙ²/aₙ₊₁ - 1 = -Eₙ/Cₙ + Λₙ`. -/
theorem growthDefect_eq_neg_relativeError_add_correction
    {a aNext D DNext C CNext E ENext : ℝ}
    (hD : DNext = a * D)
    (hC : CNext = a * C - D)
    (hE : E = D - (a - 1) * C)
    (hENext : ENext = DNext - (aNext - 1) * CNext)
    (hne : aNext * C * CNext ≠ 0) :
    a ^ 2 / aNext - 1 =
      -(E / C) + shiftedSignCorrection a aNext C CNext E ENext := by
  have haNext : aNext ≠ 0 := by
    intro h; apply hne; rw [h]; ring
  have hC0 : C ≠ 0 := by
    intro h; apply hne; rw [h]; ring
  have hCNext : CNext ≠ 0 := by
    intro h; apply hne; rw [h]; ring
  subst hD
  subst hE
  subst hENext
  simp only [shiftedSignCorrection]
  rw [hC] at hCNext ⊢
  field_simp
  ring

/-- **The Sylvester-tail clause of `long243:res:classicalhalfspace`.**
If the centred error vanishes at index `n` and `aₙ₊₁ = aₙ² - aₙ + 1`, then
the centred error vanishes at index `n + 1` as well, and the correction term
is `Λₙ = (aₙ - 1)/aₙ₊₁ > 0`. -/
theorem sylvesterTail_correction
    {a aNext D DNext C CNext E ENext : ℝ}
    (hD : DNext = a * D)
    (hC : CNext = a * C - D)
    (hE : E = D - (a - 1) * C)
    (hENext : ENext = DNext - (aNext - 1) * CNext)
    (ha : 1 < a)
    (hsyl : aNext = a ^ 2 - a + 1)
    (hzero : E = 0) :
    ENext = 0 ∧
      shiftedSignCorrection a aNext C CNext E ENext = (a - 1) / aNext ∧
      0 < shiftedSignCorrection a aNext C CNext E ENext := by
  have hDval : D = (a - 1) * C := by
    rw [hE] at hzero; linarith
  have hCNext : CNext = C := by rw [hC, hDval]; ring
  have hENextZero : ENext = 0 := by
    rw [hENext, hD, hDval, hCNext, hsyl]; ring
  have haNextPos : 0 < aNext := by
    rw [hsyl]; nlinarith
  have hLam : shiftedSignCorrection a aNext C CNext E ENext
      = (a - 1) / aNext := by
    simp only [shiftedSignCorrection, hzero, hENextZero, zero_div, sub_zero,
      add_zero, one_mul]
  refine ⟨hENextZero, hLam, ?_⟩
  rw [hLam]
  exact div_pos (by linarith) haNextPos

#print axioms ErdosProblems.Erdos243.PaperCompleteR21.growthDefect_eq_neg_relativeError_add_correction
#print axioms ErdosProblems.Erdos243.PaperCompleteR21.sylvesterTail_correction

end ErdosProblems.Erdos243.PaperCompleteR21
