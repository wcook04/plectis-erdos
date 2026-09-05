import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

/-!
# Erdős #1041: the reciprocal Newton expansion kernel

`ReciprocalNewtonExpansion.md` replaces the anchored root-error expansion by the
Taylor series of `log(f(z)/f(0))`, whose coefficients are the exact reciprocal
power sums `p m = sum_j (a j)⁻¹ ^ m`.  This module checks the finite steps that
the analytic proof leans on:

* `norm_recipPowerSum_le` — the coefficient bound `|p m| <= n r⁻ᵐ` driving the
  `C⁰`, `C¹` and `C²` tail estimates.
* `tsum_geometric_tail` — the geometric tail those estimates are summed against.
* `newton_solve` — the solved form of Newton's identity for the reversed
  polynomial, which makes every coefficient rational in the coefficients of `f`.
* `staple_length_eq`, `staple_length_lt_two` — the equal-radius staple length
  identity, and the fact that it spends no margin.
* `quadratic_contact_absorbs`, `contact_survives` — the completed-square
  discriminant that decides a zero-margin contact.  Uniform convergence to a
  non-positive model is not enough: `-x² + ε` is the countermodel.

The logarithmic series, Newton's identity in general, and Taylor with integral
remainder are carried by the ordinary proof.
-/

namespace ErdosProblems.Erdos1041.ReciprocalNewtonExpansion

open Finset

/-! ## 1. The reciprocal coefficient bound -/

/-- If every root has modulus at least `r > 0` then the `m`-th reciprocal power
sum is bounded by `n r⁻ᵐ`.  This is the only input to the tail estimates. -/
theorem norm_recipPowerSum_le {n : ℕ} (a : Fin n → ℂ) (m : ℕ) {r : ℝ}
    (hr : 0 < r) (ha : ∀ j, r ≤ ‖a j‖) :
    ‖∑ j, (a j)⁻¹ ^ m‖ ≤ n * (r⁻¹) ^ m := by
  have hterm : ∀ j ∈ (univ : Finset (Fin n)), ‖(a j)⁻¹ ^ m‖ ≤ (r⁻¹) ^ m := by
    intro j _
    rw [norm_pow, norm_inv]
    have hj : ‖a j‖⁻¹ ≤ r⁻¹ := by
      have := ha j
      gcongr
    gcongr
  calc ‖∑ j, (a j)⁻¹ ^ m‖ ≤ ∑ j, ‖(a j)⁻¹ ^ m‖ := norm_sum_le _ _
    _ ≤ ∑ _j : Fin n, (r⁻¹) ^ m := Finset.sum_le_sum hterm
    _ = n * (r⁻¹) ^ m := by simp [mul_comm]

/-- The geometric tail the `C⁰`, `C¹` and `C²` estimates are summed against. -/
theorem tsum_geometric_tail {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) (N : ℕ) :
    ∑' m : ℕ, q ^ (N + 1 + m) = q ^ (N + 1) / (1 - q) := by
  have hcongr : ∀ m : ℕ, q ^ (N + 1 + m) = q ^ (N + 1) * q ^ m := fun m =>
    pow_add q (N + 1) m
  have hlt : |q| < 1 := by rwa [abs_of_nonneg hq0]
  rw [tsum_congr hcongr, tsum_mul_left, tsum_geometric_of_lt_one hq0 hq1]
  field_simp

/-! ## 2. Newton's identity in solved form -/

/-- The reversed-polynomial Newton identity, solved for `p m`.  Since
`chat k = c k / c 0`, this exhibits every reciprocal Newton coordinate as a
rational function of the coefficients of `f`, with denominator a power of
`f 0`. -/
theorem newton_solve {m : ℕ} (hm : 0 < m) (chat p : ℕ → ℂ) (h0 : chat 0 = 1)
    (h : (∑ j ∈ Finset.range m, chat j * p (m - j)) + m * chat m = 0) :
    p m = -(m * chat m) - ∑ j ∈ Finset.Ico 1 m, chat j * p (m - j) := by
  have hsplit : Finset.range m = insert 0 (Finset.Ico 1 m) := by
    ext j
    simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Ico]
    omega
  have hnot : (0 : ℕ) ∉ Finset.Ico 1 m := by simp
  rw [hsplit, Finset.sum_insert hnot, h0, one_mul, Nat.sub_zero] at h
  linear_combination h

/-! ## 3. The staple length spends no margin -/

/-- The equal-radius staple `a_i -> s u_i -> s u_j -> a_j` has length exactly
`|a_i| + |a_j| - s (2 - |u_i - u_j|)`. -/
theorem staple_length_eq (A B s c : ℝ) :
    (A - s) + s * c + (B - s) = A + B - s * (2 - c) := by ring

/-- Whatever the root directions do, the staple is never longer than the sum of
the two root moduli, hence strictly shorter than `2` for roots in the open unit
disk.  No polynomial-independent slack is consumed. -/
theorem staple_length_lt_two {A B s c : ℝ} (hA : A < 1) (hB : B < 1)
    (hs : 0 ≤ s) (hc : c ≤ 2) :
    A + B - s * (2 - c) < 2 := by
  nlinarith

/-! ## 4. Contact absorption -/

/-- Completed square: a quadratic contact absorbs a transverse slope at the
exact cost `B² / (4 kappa)`. -/
theorem quadratic_contact_absorbs {kappa B V eps x F : ℝ} (hk : 0 < kappa)
    (hF : F ≤ -kappa * x ^ 2 + B * |x| + V + eps) :
    F ≤ V + eps + B ^ 2 / (4 * kappa) := by
  have hsq : 0 ≤ (2 * kappa * |x| - B) ^ 2 := sq_nonneg _
  have habs : |x| ^ 2 = x ^ 2 := sq_abs x
  have hkey : -kappa * x ^ 2 + B * |x| ≤ B ^ 2 / (4 * kappa) := by
    rw [← habs, le_div_iff₀ (by positivity)]
    nlinarith [hsq]
  linarith

/-- The contact survives exactly when the completed-square discriminant is
negative.  Uniform convergence to a non-positive model is not enough; the
countermodel is `-x² + eps`. -/
theorem contact_survives {kappa B V eps x F : ℝ} (hk : 0 < kappa)
    (hF : F ≤ -kappa * x ^ 2 + B * |x| + V + eps)
    (hdisc : V + eps + B ^ 2 / (4 * kappa) < 0) :
    F < 0 :=
  lt_of_le_of_lt (quadratic_contact_absorbs hk hF) hdisc

end ErdosProblems.Erdos1041.ReciprocalNewtonExpansion
