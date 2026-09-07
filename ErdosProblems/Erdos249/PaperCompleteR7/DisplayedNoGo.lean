import Erdos257PeriodNoncollapse.TotientTailPeriodKiller
import Mathlib

/-!
# Counterexamples to literal displayed formulations

Uncompiled proof-source candidates. These do not refute the correctly
hypothesised library theorems and make no assertion settling Erdős #249.

* Long-record environment 220, "Locked reconstruction preserves a nonzero
  minor", omits the locked-gauge equation. Its cited source actually uses
  W(j) = z(j)^{-1}, not arbitrary residual weights r(i,j).
* Environment 202 writes all h <= f(N) without h > 0. Taken literally,
  this includes h=0, for which no certificate can hold. This is an omitted
  guard, not an obstruction to the intended positive-period producer.
-/

namespace ErdosProblems.Erdos249.PaperCompleteR7.DisplayedNoGo

open Erdos257PeriodNoncollapse.TotientTailPeriodKiller

/-- The matrices in the literal, row-dependent printed formulation. -/
def printedPhase {d : ℕ} (e : Fin d → ℕ) (z : Fin d → ℂ) :
    Matrix (Fin d) (Fin d) ℂ := fun i j => z j ^ e i

def printedResidual {d : ℕ} (e : Fin d → ℕ)
    (r : Matrix (Fin d) (Fin d) ℂ) (z : Fin d → ℂ) :
    Matrix (Fin d) (Fin d) ℂ := fun i j => r i j * z j ^ e i

/-- With z=1, e=1 and r=0 the phase determinant is 1 but the residual
matrix is zero. Nonzero z alone does not preserve the determinant. -/
theorem unrestricted_residual_determinant_counterexample :
    ∃ (e : Fin 1 → ℕ) (r : Matrix (Fin 1) (Fin 1) ℂ) (z : Fin 1 → ℂ),
      (∀ j, z j ≠ 0) ∧ e 0 = 1 ∧
      Matrix.det (printedPhase e z) ≠ 0 ∧
      Matrix.det (printedResidual e r z) = 0 := by
  refine ⟨fun _ => 1, fun _ _ => 0, fun _ => 1, ?_, rfl, ?_, ?_⟩
  · intro j; norm_num
  · norm_num [printedPhase, Matrix.det_fin_one]
  · norm_num [printedResidual, Matrix.det_fin_one]

/-- Even requiring the residual weights and both determinants to be
nonzero does not make the exponent-one row equal to 1: take r=2. -/
theorem unrestricted_residual_row_counterexample :
    ∃ (e : Fin 1 → ℕ) (r : Matrix (Fin 1) (Fin 1) ℂ) (z : Fin 1 → ℂ),
      (∀ j, z j ≠ 0) ∧ (∀ i j, r i j ≠ 0) ∧ e 0 = 1 ∧
      Matrix.det (printedPhase e z) ≠ 0 ∧
      Matrix.det (printedResidual e r z) ≠ 0 ∧
      printedResidual e r z 0 0 ≠ 1 := by
  refine ⟨fun _ => 1, fun _ _ => 2, fun _ => 1, ?_, ?_, rfl, ?_, ?_, ?_⟩
  · intro j; norm_num
  · intro i j; norm_num
  · norm_num [printedPhase, Matrix.det_fin_one]
  · norm_num [printedResidual, Matrix.det_fin_one]
  · norm_num [printedResidual]

/-- A zero period has zero discrepancy and cannot satisfy a central gap. -/
theorem no_zero_period_certificate (N L : ℕ) : ¬ certifiedKill 0 N L := by
  have hD : windowDiscrepancy 0 N L = 0 := by
    simp [windowDiscrepancy]
  intro h
  have hleft := h.1
  rw [hD, Int.zero_emod] at hleft
  have hN : (0 : ℤ) ≤ N := by positivity
  have hL : (0 : ℤ) ≤ L := by positivity
  omega

/-- The literal unguarded simultaneous-period demand is false already
at h=0, independently of any growth condition on f. -/
theorem unguarded_simultaneous_periods_impossible (f : ℕ → ℕ) :
    ¬ ∃ N L : ℕ, ∀ h : ℕ, h ≤ f N → certifiedKill h N L := by
  rintro ⟨N, L, h⟩
  exact no_zero_period_certificate N L (h 0 (Nat.zero_le _))

/-- The displayed separated-pair estimate also needs delta >= 0. With a
singleton zero family and delta=-1, the separation hypothesis holds, while
its proposed squared lower bound is 1 <= 0. -/
theorem negative_separation_counterexample :
    let δ : ℝ := -1
    let z : Fin 1 → ℂ := fun _ => 0
    (∀ i j : Fin 1, δ ≤ ‖z i - z j‖) ∧
      ¬ ((Fintype.card (Fin 1 × Fin 1) : ℝ) * δ ^ 2 ≤
        ∑ i : Fin 1, ∑ j : Fin 1, ‖z i - z j‖ ^ 2) := by
  norm_num

end ErdosProblems.Erdos249.PaperCompleteR7.DisplayedNoGo
