import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

/-!
# Erdős #1041: the arbitrary cyclic-trinomial spoke kernel

For

`f(z) = (z-h)^(q*m) + a*(z-h)^(q*r) + c`,

put `w=(z-h)^q`.  If `w` is a root of `w^m+a*w^r+c` and
`‖w‖^m ≤ ‖c‖`, then the entire radial spoke from `h` to every member of the
`q`-point fibre over `w` stays below `‖c‖`.  Vieta supplies such a quotient
root, while the open-unit-disk hypothesis makes `‖c‖<1` and the fibre radius
strictly smaller than one.

More strongly, if merely `‖w‖<1` and `‖c‖<1`, then the same spoke is strictly
inside the unit lemniscate.  Thus every root spoke is safe for a centred
trinomial, and every fibre spoke is safe after a nontrivial cyclic lift.

The accompanying analytic note performs those finite root-selection and fibre
steps.  This file kernel-checks the load-bearing arbitrary-exponent identity
and norm estimate.
-/

namespace ErdosProblems.Erdos1041

/-- Powers reverse their exponent order on the real unit interval. -/
theorem unitInterval_pow_anti {u : ℝ} {r m : ℕ}
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (hrm : r ≤ m) :
    u ^ m ≤ u ^ r := by
  let k := m - r
  have hmk : m = r + k := by
    dsimp [k]
    omega
  have hk : u ^ k ≤ 1 := pow_le_one₀ hu0 hu1
  rw [hmk, pow_add]
  simpa only [mul_one] using
    mul_le_mul_of_nonneg_left hk (pow_nonneg hu0 r)

/-- Eliminating the linear coefficient at a root of the quotient trinomial
gives a two-term spoke identity valid in every quotient degree. -/
theorem trinomialRoot_spoke_factorization
    {m r : ℕ} {a c w : ℂ} {u : ℝ}
    (hroot : w ^ m + a * w ^ r + c = 0) :
    (u : ℂ) ^ m * w ^ m + a * (u : ℂ) ^ r * w ^ r + c =
      ((1 - u ^ r : ℝ) : ℂ) * c -
        ((u ^ r - u ^ m : ℝ) : ℂ) * w ^ m := by
  push_cast
  linear_combination (u : ℂ) ^ r * hroot

/-- A Vieta-small quotient root produces a safe radial spoke for
`w^m+a*w^r+c`.  The application substitutes `u=t^q`. -/
theorem trinomialRoot_spoke_norm_le_constant
    {m r : ℕ} (hrm : r ≤ m) {a c w : ℂ}
    (hroot : w ^ m + a * w ^ r + c = 0)
    (hw : ‖w‖ ^ m ≤ ‖c‖) {u : ℝ}
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    ‖(u : ℂ) ^ m * w ^ m + a * (u : ℂ) ^ r * w ^ r + c‖ ≤ ‖c‖ := by
  have hpownonneg : 0 ≤ u ^ m := pow_nonneg hu0 m
  have hpowone : u ^ m ≤ 1 := pow_le_one₀ hu0 hu1
  have hpowanti : u ^ m ≤ u ^ r := unitInterval_pow_anti hu0 hu1 hrm
  have hrpowone : u ^ r ≤ 1 := pow_le_one₀ hu0 hu1
  have hfirst : ‖(((1 - u ^ r : ℝ) : ℂ))‖ = 1 - u ^ r := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg]
    linarith
  have hsecond : ‖(((u ^ r - u ^ m : ℝ) : ℂ))‖ = u ^ r - u ^ m := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg]
    linarith
  rw [trinomialRoot_spoke_factorization hroot]
  calc
    ‖((1 - u ^ r : ℝ) : ℂ) * c -
        ((u ^ r - u ^ m : ℝ) : ℂ) * w ^ m‖
        ≤ ‖((1 - u ^ r : ℝ) : ℂ) * c‖ +
            ‖((u ^ r - u ^ m : ℝ) : ℂ) * w ^ m‖ := norm_sub_le _ _
    _ = (1 - u ^ r) * ‖c‖ + (u ^ r - u ^ m) * (‖w‖ ^ m) := by
          rw [norm_mul, norm_mul, hfirst, hsecond, norm_pow]
    _ ≤ (1 - u ^ r) * ‖c‖ + (u ^ r - u ^ m) * ‖c‖ := by
          exact add_le_add (le_refl _)
            (mul_le_mul_of_nonneg_left hw (sub_nonneg.mpr hpowanti))
    _ = (1 - u ^ m) * ‖c‖ := by ring
    _ ≤ ‖c‖ := by
          have hcoef : 1 - u ^ m ≤ 1 := by linarith
          simpa using mul_le_mul_of_nonneg_right hcoef (norm_nonneg c)

/-- The strict containment conclusion once the quotient constant term is
strictly inside the unit disk. -/
theorem trinomialRoot_spoke_norm_lt_one
    {m r : ℕ} (hrm : r ≤ m) {a c w : ℂ}
    (hroot : w ^ m + a * w ^ r + c = 0)
    (hw : ‖w‖ ^ m ≤ ‖c‖) (hc : ‖c‖ < 1) {u : ℝ}
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    ‖(u : ℂ) ^ m * w ^ m + a * (u : ℂ) ^ r * w ^ r + c‖ < 1 :=
  lt_of_le_of_lt
    (trinomialRoot_spoke_norm_le_constant hrm hroot hw hu0 hu1) hc

/-- The all-root version used by the case theorem.  No Vieta-small selection is
needed: when both the quotient root and constant term lie in the open unit
disk, the two nonnegative spoke coefficients spend at most the unit budget. -/
theorem trinomialRoot_spoke_norm_lt_one_of_norm_lt_one
    {m r : ℕ} (hr : 1 ≤ r) (hrm : r ≤ m) {a c w : ℂ}
    (hroot : w ^ m + a * w ^ r + c = 0)
    (hw : ‖w‖ < 1) (hc : ‖c‖ < 1) {u : ℝ}
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    ‖(u : ℂ) ^ m * w ^ m + a * (u : ℂ) ^ r * w ^ r + c‖ < 1 := by
  by_cases hu : u = 1
  · subst u
    norm_num [hroot]
  · have hult : u < 1 := lt_of_le_of_ne hu1 hu
    have hpowanti : u ^ m ≤ u ^ r := unitInterval_pow_anti hu0 hu1 hrm
    have hrpowlt : u ^ r < 1 := pow_lt_one₀ hu0 hult (by omega)
    have hm0 : m ≠ 0 := by omega
    have hwm : ‖w‖ ^ m < 1 := pow_lt_one₀ (norm_nonneg w) hw hm0
    have hfirst : ‖(((1 - u ^ r : ℝ) : ℂ))‖ = 1 - u ^ r := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg]
      linarith
    have hsecond : ‖(((u ^ r - u ^ m : ℝ) : ℂ))‖ = u ^ r - u ^ m := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg]
      linarith
    have hApos : 0 < 1 - u ^ r := by linarith
    have hBnonneg : 0 ≤ u ^ r - u ^ m := by linarith
    rw [trinomialRoot_spoke_factorization hroot]
    calc
      ‖((1 - u ^ r : ℝ) : ℂ) * c -
          ((u ^ r - u ^ m : ℝ) : ℂ) * w ^ m‖
          ≤ ‖((1 - u ^ r : ℝ) : ℂ) * c‖ +
              ‖((u ^ r - u ^ m : ℝ) : ℂ) * w ^ m‖ := norm_sub_le _ _
      _ = (1 - u ^ r) * ‖c‖ + (u ^ r - u ^ m) * (‖w‖ ^ m) := by
            rw [norm_mul, norm_mul, hfirst, hsecond, norm_pow]
      _ < (1 - u ^ r) * 1 + (u ^ r - u ^ m) * 1 := by
            exact add_lt_add_of_lt_of_le
              (mul_lt_mul_of_pos_left hc hApos)
              (mul_le_mul_of_nonneg_left hwm.le hBnonneg)
      _ = 1 - u ^ m := by ring
      _ ≤ 1 := by
            have : 0 ≤ u ^ m := pow_nonneg hu0 m
            linarith

/-- Two members of a selected fibre of radius below one give the strict metric
budget for the broken line through the symmetry centre. -/
theorem cyclicTrinomial_two_short_fiber_displacements {y₁ y₂ : ℂ}
    (hy₁ : ‖y₁‖ < 1) (hy₂ : ‖y₂‖ < 1) :
    ‖y₁‖ + ‖y₂‖ < 2 := by
  linarith

end ErdosProblems.Erdos1041
