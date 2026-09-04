import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

/-!
# Erdős #1041: the translated even-symmetric trinomial spoke kernel

For `f(z)=(z-h)^(2q)+a*(z-h)^q+c`, put `y=z-h` and `w=y^q`.  A quadratic root
`w^2+a*w+c=0` satisfying `‖w‖^2 <= ‖c‖` produces a whole safe radial
spoke from `h`.  Translation disappears in the `y` coordinate, so this file
kernel-checks the exact factorization and norm estimate there.

The accompanying analytic note selects such a quadratic root by Vieta, takes
two distinct points in its `q`-th-root fibre, and verifies the strict length
budget.  Those finite root-existence steps are not asserted as axioms here.
-/

namespace ErdosProblems.Erdos1041

/-- The elementary disk inequality behind the even-symmetric spoke estimate. -/
theorem unitDisk_linearFactor_norm_le_one {u : ℝ} {delta : ℂ}
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (hdelta : ‖delta‖ ≤ 1) :
    ‖(1 - (u : ℂ)) * (1 - (u : ℂ) * delta)‖ ≤ 1 := by
  have h1u : 0 ≤ 1 - u := by linarith
  have hfirst : (1 : ℂ) - (u : ℂ) = ((1 - u : ℝ) : ℂ) := by
    push_cast
    ring
  have hnorm_one_sub : ‖(1 - (u : ℂ))‖ = 1 - u := by
    rw [hfirst, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg h1u]
  have hnorm_u : ‖(u : ℂ)‖ = u := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hu0]
  have hsecond : ‖(1 - (u : ℂ) * delta)‖ ≤ 1 + u * ‖delta‖ := by
    calc
      ‖(1 : ℂ) - (u : ℂ) * delta‖
          ≤ ‖(1 : ℂ)‖ + ‖(u : ℂ) * delta‖ := norm_sub_le _ _
      _ = 1 + u * ‖delta‖ := by rw [norm_mul, hnorm_u]; norm_num
  calc
    ‖(1 - (u : ℂ)) * (1 - (u : ℂ) * delta)‖
        = (1 - u) * ‖(1 - (u : ℂ) * delta)‖ := by
          rw [norm_mul, hnorm_one_sub]
    _ ≤ (1 - u) * (1 + u * ‖delta‖) :=
      mul_le_mul_of_nonneg_left hsecond h1u
    _ ≤ (1 - u) * (1 + u) := by
      have hudelta : u * ‖delta‖ ≤ u :=
        by simpa only [mul_one] using mul_le_mul_of_nonneg_left hdelta hu0
      exact mul_le_mul_of_nonneg_left (by linarith) h1u
    _ ≤ 1 := by nlinarith [sq_nonneg u]

/-- Eliminating the middle coefficient at a quadratic root gives the exact
factorization used on every radial spoke. -/
theorem quadraticRoot_spoke_factorization {a c w delta u : ℂ}
    (hroot : w ^ 2 + a * w + c = 0)
    (hdelta : w ^ 2 = c * delta) :
    u ^ 2 * w ^ 2 + a * u * w + c =
      c * (1 - u) * (1 - u * delta) := by
  rw [hdelta] at hroot ⊢
  linear_combination u * hroot

/-- The quotient parameter `delta=w^2/c` lies in the closed unit disk when
the selected quadratic root satisfies the Vieta bound `‖w‖^2 <= ‖c‖`. -/
theorem quadraticRoot_ratio_norm_le_one {c w : ℂ}
    (hc : c ≠ 0) (hw : ‖w‖ ^ 2 ≤ ‖c‖) :
    ‖w ^ 2 / c‖ ≤ 1 := by
  have hcpos : 0 < ‖c‖ := norm_pos_iff.mpr hc
  rw [norm_div, norm_pow]
  exact (div_le_one hcpos).2 hw

/-- A Vieta-small root of the quadratic quotient produces a safe spoke for
the translated even-symmetric trinomial.  The real parameter `u` is `t^q` in
the application `z=h+t*y`; translation has already been removed. -/
theorem quadraticRoot_spoke_norm_le_constant {a c w : ℂ}
    (hc : c ≠ 0) (hroot : w ^ 2 + a * w + c = 0)
    (hw : ‖w‖ ^ 2 ≤ ‖c‖) {u : ℝ}
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    ‖(u : ℂ) ^ 2 * w ^ 2 + a * (u : ℂ) * w + c‖ ≤ ‖c‖ := by
  let delta : ℂ := w ^ 2 / c
  have hdelta : w ^ 2 = c * delta := by
    dsimp [delta]
    field_simp [hc]
  have hfactor := quadraticRoot_spoke_factorization
    (a := a) (c := c) (w := w) (delta := delta) (u := (u : ℂ)) hroot hdelta
  rw [hfactor]
  have hfactor_norm :
      ‖(1 - (u : ℂ)) * (1 - (u : ℂ) * delta)‖ ≤ 1 := by
    exact unitDisk_linearFactor_norm_le_one hu0 hu1
      (quadraticRoot_ratio_norm_le_one hc hw)
  calc
    ‖c * (1 - (u : ℂ)) * (1 - (u : ℂ) * delta)‖
        = ‖c‖ * ‖(1 - (u : ℂ)) * (1 - (u : ℂ) * delta)‖ := by
          rw [mul_assoc, norm_mul]
    _
        ≤ ‖c‖ * 1 := mul_le_mul_of_nonneg_left hfactor_norm (norm_nonneg c)
    _ = ‖c‖ := mul_one _

/-- Two displacements of norm below one give a broken-line hub whose total
Euclidean length is strictly below two.  In the application these are two
members of the selected regular fibre, measured from its centre `h`. -/
theorem two_short_displacements_give_short_hub {y₁ y₂ : ℂ}
    (hy₁ : ‖y₁‖ < 1) (hy₂ : ‖y₂‖ < 1) :
    ‖y₁‖ + ‖y₂‖ < 2 := by
  linarith

end ErdosProblems.Erdos1041
