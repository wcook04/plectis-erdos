import ErdosProblems.Erdos1041.TetranomialTailProductSelector

/-!
# Erdős #1041: reciprocal-moment radius selector

Missing low coefficients of a tetranomial force vanishing Newton moments of
the reciprocal roots.  The analytic companion uses that cancellation to bound
the second-smallest root radius.  This module checks the scalar radius-product
kernel, the monotone Abel-tail estimate, and the end-to-end conversion of two
small roots into two complete safe spokes.
-/

namespace ErdosProblems.Erdos1041

/-- Scalar kernel behind the reciprocal-moment selector.  Reciprocal
cancellation supplies the first hypothesis and Vieta supplies the second. -/
theorem secondRadius_pow_bound_of_reciprocal_and_product
    {m k : ℕ} (hm : 2 ≤ m)
    {rho1 rho2 C : ℝ}
    (hrho1 : 0 ≤ rho1) (hrho2 : 0 ≤ rho2)
    (hreciprocal : rho2 ^ k ≤ ((m - 1 : ℕ) : ℝ) * rho1 ^ k)
    (hproduct : rho1 * rho2 ^ (m - 1) ≤ C) :
    rho2 ^ (m * k) ≤ ((m - 1 : ℕ) : ℝ) * C ^ k := by
  have hproduct0 : 0 ≤ rho1 * rho2 ^ (m - 1) :=
    mul_nonneg hrho1 (pow_nonneg hrho2 _)
  have hproductPow : (rho1 * rho2 ^ (m - 1)) ^ k ≤ C ^ k :=
    pow_le_pow_left₀ hproduct0 hproduct k
  have hproductPow' : rho1 ^ k * rho2 ^ ((m - 1) * k) ≤ C ^ k := by
    simpa [mul_pow, pow_mul] using hproductPow
  have hrhoTail0 : 0 ≤ rho2 ^ ((m - 1) * k) := pow_nonneg hrho2 _
  have hmul := mul_le_mul_of_nonneg_right hreciprocal hrhoTail0
  have hm1nonneg : 0 ≤ ((m - 1 : ℕ) : ℝ) := by positivity
  have hscaled := mul_le_mul_of_nonneg_left hproductPow' hm1nonneg
  have hexponent : k + (m - 1) * k = m * k := by
    calc
      k + (m - 1) * k = (m - 1) * k + 1 * k := by simp [Nat.add_comm]
      _ = ((m - 1) + 1) * k := by rw [Nat.add_mul]
      _ = m * k := by rw [Nat.sub_add_cancel (by omega : 1 ≤ m)]
  calc
    rho2 ^ (m * k) = rho2 ^ k * rho2 ^ ((m - 1) * k) := by
      rw [← pow_add, hexponent]
    _ ≤ ((m - 1 : ℕ) : ℝ) *
        (rho1 ^ k * rho2 ^ ((m - 1) * k)) := by
      nlinarith
    _ ≤ ((m - 1 : ℕ) : ℝ) * C ^ k := hscaled

/-- A strict radius cap and a weak coefficient envelope make the upper Abel
tail strictly smaller than one. -/
theorem radial_upperTail_lt_one
    {m r : ℕ} (hr : 1 ≤ r)
    {x q A : ℝ} (hx0 : 0 ≤ x) (hxq : x < q) (hA0 : 0 ≤ A)
    (hbudget : q ^ r * (q ^ (m - r) + A) ≤ 1) :
    x ^ r * (x ^ (m - r) + A) < 1 := by
  have hq0 : 0 ≤ q := le_trans hx0 hxq.le
  have hxr : x ^ r < q ^ r :=
    pow_lt_pow_left₀ hxq hx0 (by omega)
  have hxd : x ^ (m - r) ≤ q ^ (m - r) :=
    pow_le_pow_left₀ hx0 hxq.le _
  have hxpow0 : 0 ≤ x ^ r := pow_nonneg hx0 _
  have hrightPos : 0 < q ^ (m - r) + A := by
    by_cases hd : m - r = 0
    · simp only [hd, pow_zero]
      linarith
    · have : 0 < q := lt_of_le_of_lt hx0 hxq
      exact add_pos_of_pos_of_nonneg (pow_pos this _) hA0
  calc
    x ^ r * (x ^ (m - r) + A) ≤
        x ^ r * (q ^ (m - r) + A) := by
      gcongr
    _ < q ^ r * (q ^ (m - r) + A) :=
      mul_lt_mul_of_pos_right hxr hrightPos
    _ ≤ 1 := hbudget

/-- Two roots below the reciprocal-moment radius cap have complete safe
tetranomial spokes.  The analytic theorem produces these indices from the
vanishing reciprocal Newton moment and the scalar kernel above. -/
theorem two_small_tetranomialRoots_safeSpokes
    {ι : Type*} (S : Finset ι) (w : ι → ℂ) (i j : ι)
    {m r s : ℕ} (hs : 1 ≤ s) (hsr : s ≤ r) (hrm : r ≤ m)
    {a b c : ℂ} {q : ℝ}
    (hiS : i ∈ S) (hjS : j ∈ S) (hij : i ≠ j)
    (hroot : ∀ z ∈ S, w z ^ m + a * w z ^ r + b * w z ^ s + c = 0)
    (hw : ∀ z ∈ S, ‖w z‖ < 1) (hc : ‖c‖ < 1)
    (hiq : ‖w i‖ < q) (hjq : ‖w j‖ < q)
    (hqbudget : q ^ r * (q ^ (m - r) + ‖a‖) ≤ 1) :
    i ≠ j ∧
    (∀ u : ℝ, 0 ≤ u → u ≤ 1 →
      ‖(u : ℂ) ^ m * w i ^ m + a * (u : ℂ) ^ r * w i ^ r +
        b * (u : ℂ) ^ s * w i ^ s + c‖ < 1) ∧
    (∀ u : ℝ, 0 ≤ u → u ≤ 1 →
      ‖(u : ℂ) ^ m * w j ^ m + a * (u : ℂ) ^ r * w j ^ r +
        b * (u : ℂ) ^ s * w j ^ s + c‖ < 1) := by
  have hr : 1 ≤ r := le_trans hs hsr
  have htail (z : ι) (hzS : z ∈ S) (hzq : ‖w z‖ < q) :
      ‖a * w z ^ r + w z ^ m‖ < 1 := by
    have hpowSplit : ‖w z‖ ^ m = ‖w z‖ ^ r * ‖w z‖ ^ (m - r) := by
      rw [← pow_add, Nat.add_sub_of_le hrm]
    have hnormUpper : ‖a * w z ^ r + w z ^ m‖ ≤
        ‖w z‖ ^ r * (‖w z‖ ^ (m - r) + ‖a‖) := by
      calc
        ‖a * w z ^ r + w z ^ m‖ ≤ ‖a * w z ^ r‖ + ‖w z ^ m‖ :=
          norm_add_le _ _
        _ = ‖w z‖ ^ r * (‖w z‖ ^ (m - r) + ‖a‖) := by
          rw [norm_mul, norm_pow, norm_pow, hpowSplit]
          ring
    have hrealTail : ‖w z‖ ^ r * (‖w z‖ ^ (m - r) + ‖a‖) < 1 :=
      radial_upperTail_lt_one hr (norm_nonneg _) hzq (norm_nonneg _) hqbudget
    exact lt_of_le_of_lt hnormUpper hrealTail
  refine ⟨hij, ?_, ?_⟩
  · intro u hu0 hu1
    exact tetranomialRoot_spoke_norm_lt_one_of_tail
      hs hsr hrm (hroot i hiS) (hw i hiS) hc (htail i hiS hiq) hu0 hu1
  · intro u hu0 hu1
    exact tetranomialRoot_spoke_norm_lt_one_of_tail
      hs hsr hrm (hroot j hjS) (hw j hjS) hc (htail j hjS hjq) hu0 hu1

end ErdosProblems.Erdos1041
