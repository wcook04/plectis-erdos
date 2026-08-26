import ErdosProblems.Erdos1041.CyclicTrinomialFiberCase
import Mathlib.Tactic

/-!
# Erdős #1041: endpoint-vanishing trinomial interpolation

For a polynomial restricted to the radial segment `z = u*a`, choose one
middle exponent `j` and interpolate the two endpoint values by a trinomial.
The discarded modes then carry factors `u^k-u^j`, so the error vanishes at
both endpoints.  The companion analytic note uses this exact identity as a
finite multiscale certificate; it does not claim that one exponent works on
every spoke.
-/

open scoped BigOperators

namespace ErdosProblems.Erdos1041.TrinomialInterpolationSpoke

/-- If `A*a^j` equals the complete middle part at the selected root `a`, then
replacing that middle part by `A*z^j` leaves an endpoint-vanishing error on
`z=u*a`. -/
theorem interpolation_remainder_identity
    {n j : ℕ} (s : Finset ℕ) (b : ℕ → ℂ) {a A c : ℂ} {u : ℝ}
    (hA : A * a ^ j = ∑ k ∈ s, b k * a ^ k) :
    ((u : ℂ) * a) ^ n + (∑ k ∈ s, b k * ((u : ℂ) * a) ^ k) + c -
        (((u : ℂ) * a) ^ n + A * ((u : ℂ) * a) ^ j + c) =
      ∑ k ∈ s, b k * a ^ k * ((u : ℂ) ^ k - (u : ℂ) ^ j) := by
  have hsum_pow : (∑ k ∈ s, b k * ((u : ℂ) * a) ^ k) =
      ∑ k ∈ s, b k * a ^ k * (u : ℂ) ^ k := by
    apply Finset.sum_congr rfl
    intro k _hk
    rw [mul_pow]
    ring
  calc
    ((u : ℂ) * a) ^ n + (∑ k ∈ s, b k * ((u : ℂ) * a) ^ k) + c -
          (((u : ℂ) * a) ^ n + A * ((u : ℂ) * a) ^ j + c) =
        (∑ k ∈ s, b k * a ^ k * (u : ℂ) ^ k) -
          (A * a ^ j) * (u : ℂ) ^ j := by
            rw [hsum_pow, mul_pow]
            ring
    _ = (∑ k ∈ s, b k * a ^ k * (u : ℂ) ^ k) -
          (∑ k ∈ s, b k * a ^ k) * (u : ℂ) ^ j := by rw [hA]
    _ = ∑ k ∈ s, b k * a ^ k * ((u : ℂ) ^ k - (u : ℂ) ^ j) := by
      rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro k _hk
      ring

/-- The interpolating trinomial has the exact two-term spoke form already
available for cyclic trinomials. -/
theorem interpolatingTrinomial_spoke_identity
    {n j : ℕ} {A c a : ℂ} {u : ℝ}
    (hroot : a ^ n + A * a ^ j + c = 0) :
    (u : ℂ) ^ n * a ^ n + A * (u : ℂ) ^ j * a ^ j + c =
      ((1 - u ^ j : ℝ) : ℂ) * c -
        ((u ^ j - u ^ n : ℝ) : ℂ) * a ^ n :=
  trinomialRoot_spoke_factorization hroot

/-- The exact unused norm budget of the interpolating trinomial.  This
decomposition exposes three nonnegative sources of slack on the unit interval.
-/
theorem spokeSlack_identity {n j : ℕ} {u C R : ℝ} :
    1 - ((1 - u ^ j) * C + (u ^ j - u ^ n) * R) =
      u ^ n + (1 - u ^ j) * (1 - C) +
        (u ^ j - u ^ n) * (1 - R) := by
  ring

/-- The norm of the interpolating trinomial is bounded by the two-term budget
whose complement is `spokeSlack_identity`. -/
theorem interpolatingTrinomial_norm_le_budget
    {n j : ℕ} (hjn : j ≤ n) {A c a : ℂ}
    (hroot : a ^ n + A * a ^ j + c = 0) {u : ℝ}
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    ‖(u : ℂ) ^ n * a ^ n + A * (u : ℂ) ^ j * a ^ j + c‖ ≤
      (1 - u ^ j) * ‖c‖ + (u ^ j - u ^ n) * ‖a‖ ^ n := by
  have hpowanti : u ^ n ≤ u ^ j :=
    unitInterval_pow_anti hu0 hu1 hjn
  have hjpowone : u ^ j ≤ 1 := pow_le_one₀ hu0 hu1
  have hfirst : ‖(((1 - u ^ j : ℝ) : ℂ))‖ = 1 - u ^ j := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg]
    linarith
  have hsecond : ‖(((u ^ j - u ^ n : ℝ) : ℂ))‖ = u ^ j - u ^ n := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg]
    linarith
  rw [interpolatingTrinomial_spoke_identity hroot]
  calc
    ‖((1 - u ^ j : ℝ) : ℂ) * c -
        ((u ^ j - u ^ n : ℝ) : ℂ) * a ^ n‖
        ≤ ‖((1 - u ^ j : ℝ) : ℂ) * c‖ +
            ‖((u ^ j - u ^ n : ℝ) : ℂ) * a ^ n‖ := norm_sub_le _ _
    _ = (1 - u ^ j) * ‖c‖ + (u ^ j - u ^ n) * ‖a‖ ^ n := by
      rw [norm_mul, norm_mul, hfirst, hsecond, norm_pow]

/-- An approximating model that spends at most `1-slack`, together with an
endpoint-vanishing remainder smaller than `slack`, certifies the actual point
inside the open unit lemniscate. -/
theorem norm_lt_one_of_model_remainder_slack {actual model : ℂ} {slack : ℝ}
    (hmodel : ‖model‖ ≤ 1 - slack)
    (hremainder : ‖actual - model‖ < slack) :
    ‖actual‖ < 1 := by
  calc
    ‖actual‖ = ‖model + (actual - model)‖ := by ring_nf
    _ ≤ ‖model‖ + ‖actual - model‖ := norm_add_le _ _
    _ < (1 - slack) + slack := add_lt_add_of_le_of_lt hmodel hremainder
    _ = 1 := by ring

end ErdosProblems.Erdos1041.TrinomialInterpolationSpoke
