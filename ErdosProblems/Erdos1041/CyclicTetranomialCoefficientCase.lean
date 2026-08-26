import ErdosProblems.Erdos1041.CyclicTrinomialFiberCase

/-!
# Erdős #1041: a coefficient-controlled cyclic tetranomial class

For a quotient root of

`g(w) = w^m + a*w^r + b*w^s + c`,  `m >= r >= s >= 1`,

Abel summation turns the root spoke into three vectors with nonnegative scalar
coefficients whose sum is `1-u^m`:

`g(u*w) = (1-u^s)c - (u^s-u^r)(a*w^r+w^m) - (u^r-u^m)w^m`.

The root equation identifies the middle tail as `-(c+b*w^s)`.  Consequently
`‖b‖+‖c‖ <= 1`, `‖w‖<1`, and `‖c‖<1` put all three vectors strictly inside the
unit ball, regardless of the size of the middle coefficient `a`.  The whole
root spoke is therefore in the strict unit lemniscate.

The analytic companion supplies the root-product and cyclic-fibre steps.  This
module checks the arbitrary-exponent factorization and its strict norm budget.
-/

namespace ErdosProblems.Erdos1041

/-- Abel summation for a root of a centred tetranomial. -/
theorem tetranomialRoot_spoke_factorization
    {m r s : ℕ} {a b c w : ℂ} {u : ℝ}
    (hroot : w ^ m + a * w ^ r + b * w ^ s + c = 0) :
    (u : ℂ) ^ m * w ^ m + a * (u : ℂ) ^ r * w ^ r +
        b * (u : ℂ) ^ s * w ^ s + c =
      ((1 - u ^ s : ℝ) : ℂ) * c -
        ((u ^ s - u ^ r : ℝ) : ℂ) * (a * w ^ r + w ^ m) -
          ((u ^ r - u ^ m : ℝ) : ℂ) * w ^ m := by
  push_cast
  linear_combination (u : ℂ) ^ s * hroot

/-- The sharp root-dependent scalar condition for the new Abel tail. -/
theorem tetranomial_middleTail_norm_lt_one_of_rootBudget
    {s : ℕ} {b c w : ℂ}
    (hbudget : ‖c‖ + ‖b‖ * ‖w‖ ^ s < 1) :
    ‖c + b * w ^ s‖ < 1 := by
  calc
    ‖c + b * w ^ s‖ ≤ ‖c‖ + ‖b * w ^ s‖ := norm_add_le _ _
    _ = ‖c‖ + ‖b‖ * ‖w‖ ^ s := by rw [norm_mul, norm_pow]
    _ < 1 := hbudget

/-- The low-coefficient budget controls the only new tail sum introduced by a
fourth monomial. -/
theorem tetranomial_middleTail_norm_lt_one
    {s : ℕ} (hs : 1 ≤ s) {b c w : ℂ}
    (hw : ‖w‖ < 1) (hc : ‖c‖ < 1)
    (hbudget : ‖b‖ + ‖c‖ ≤ 1) :
    ‖c + b * w ^ s‖ < 1 := by
  by_cases hb : b = 0
  · simpa [hb] using hc
  · have hws : ‖w‖ ^ s < 1 :=
      pow_lt_one₀ (norm_nonneg w) hw (by omega)
    have hbpos : 0 < ‖b‖ := norm_pos_iff.mpr hb
    have hmul : ‖b‖ * ‖w‖ ^ s < ‖b‖ * 1 :=
      mul_lt_mul_of_pos_left hws hbpos
    calc
      ‖c + b * w ^ s‖ ≤ ‖c‖ + ‖b * w ^ s‖ := norm_add_le _ _
      _ = ‖c‖ + ‖b‖ * ‖w‖ ^ s := by rw [norm_mul, norm_pow]
      _ < ‖c‖ + ‖b‖ * 1 := by nlinarith
      _ ≤ 1 := by simpa [add_comm] using hbudget

/-- If the constant, middle tail, and leading root power are strictly inside
the unit ball, their Abel coefficients force the complete root spoke below
one. -/
theorem tetranomialRoot_spoke_norm_lt_one_of_tail
    {m r s : ℕ} (hs : 1 ≤ s) (hsr : s ≤ r) (hrm : r ≤ m)
    {a b c w : ℂ}
    (hroot : w ^ m + a * w ^ r + b * w ^ s + c = 0)
    (hw : ‖w‖ < 1) (hc : ‖c‖ < 1)
    (htail : ‖a * w ^ r + w ^ m‖ < 1) {u : ℝ}
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    ‖(u : ℂ) ^ m * w ^ m + a * (u : ℂ) ^ r * w ^ r +
        b * (u : ℂ) ^ s * w ^ s + c‖ < 1 := by
  by_cases hu : u = 1
  · subst u
    norm_num [hroot]
  · have hult : u < 1 := lt_of_le_of_ne hu1 hu
    have hsrpow : u ^ r ≤ u ^ s :=
      unitInterval_pow_anti hu0 hu1 hsr
    have hrmpow : u ^ m ≤ u ^ r :=
      unitInterval_pow_anti hu0 hu1 hrm
    have hspowlt : u ^ s < 1 :=
      pow_lt_one₀ hu0 hult (by omega)
    have hm0 : m ≠ 0 := by omega
    have hwm : ‖w‖ ^ m < 1 :=
      pow_lt_one₀ (norm_nonneg w) hw hm0
    have hApos : 0 < 1 - u ^ s := by linarith
    have hBnonneg : 0 ≤ u ^ s - u ^ r := by linarith
    have hCnonneg : 0 ≤ u ^ r - u ^ m := by linarith
    have hAnorm : ‖(((1 - u ^ s : ℝ) : ℂ))‖ = 1 - u ^ s := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg]
      linarith
    have hBnorm : ‖(((u ^ s - u ^ r : ℝ) : ℂ))‖ = u ^ s - u ^ r := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg]
      exact hBnonneg
    have hCnorm : ‖(((u ^ r - u ^ m : ℝ) : ℂ))‖ = u ^ r - u ^ m := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg]
      exact hCnonneg
    have hAterm : (1 - u ^ s) * ‖c‖ < (1 - u ^ s) * 1 :=
      mul_lt_mul_of_pos_left hc hApos
    have hBterm :
        (u ^ s - u ^ r) * ‖a * w ^ r + w ^ m‖ ≤
          (u ^ s - u ^ r) * 1 :=
      mul_le_mul_of_nonneg_left htail.le hBnonneg
    have hCterm :
        (u ^ r - u ^ m) * (‖w‖ ^ m) ≤
          (u ^ r - u ^ m) * 1 :=
      mul_le_mul_of_nonneg_left hwm.le hCnonneg
    rw [tetranomialRoot_spoke_factorization hroot]
    calc
      ‖((1 - u ^ s : ℝ) : ℂ) * c -
          ((u ^ s - u ^ r : ℝ) : ℂ) * (a * w ^ r + w ^ m) -
            ((u ^ r - u ^ m : ℝ) : ℂ) * w ^ m‖
          ≤ ‖((1 - u ^ s : ℝ) : ℂ) * c -
                ((u ^ s - u ^ r : ℝ) : ℂ) * (a * w ^ r + w ^ m)‖ +
              ‖((u ^ r - u ^ m : ℝ) : ℂ) * w ^ m‖ := norm_sub_le _ _
      _ ≤ (‖((1 - u ^ s : ℝ) : ℂ) * c‖ +
              ‖((u ^ s - u ^ r : ℝ) : ℂ) * (a * w ^ r + w ^ m)‖) +
            ‖((u ^ r - u ^ m : ℝ) : ℂ) * w ^ m‖ :=
          by
            have htriangle := norm_sub_le
              (((1 - u ^ s : ℝ) : ℂ) * c)
              (((u ^ s - u ^ r : ℝ) : ℂ) * (a * w ^ r + w ^ m))
            nlinarith
      _ = (1 - u ^ s) * ‖c‖ +
            (u ^ s - u ^ r) * ‖a * w ^ r + w ^ m‖ +
              (u ^ r - u ^ m) * (‖w‖ ^ m) := by
          rw [norm_mul, norm_mul, norm_mul, hAnorm, hBnorm, hCnorm, norm_pow]
      _ < (1 - u ^ s) * 1 + (u ^ s - u ^ r) * 1 +
            (u ^ r - u ^ m) * 1 := by
          nlinarith
      _ = 1 - u ^ m := by ring
      _ ≤ 1 := by
          have : 0 ≤ u ^ m := pow_nonneg hu0 m
          linarith

/-- The sharp pointwise coefficient form: it is enough that the lower tail
budget hold at the selected root. -/
theorem tetranomialRoot_spoke_norm_lt_one_of_rootBudget
    {m r s : ℕ} (hs : 1 ≤ s) (hsr : s ≤ r) (hrm : r ≤ m)
    {a b c w : ℂ}
    (hroot : w ^ m + a * w ^ r + b * w ^ s + c = 0)
    (hw : ‖w‖ < 1) (hc : ‖c‖ < 1)
    (hbudget : ‖c‖ + ‖b‖ * ‖w‖ ^ s < 1) {u : ℝ}
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    ‖(u : ℂ) ^ m * w ^ m + a * (u : ℂ) ^ r * w ^ r +
        b * (u : ℂ) ^ s * w ^ s + c‖ < 1 := by
  have htailEq : a * w ^ r + w ^ m = -(c + b * w ^ s) := by
    linear_combination hroot
  have htail : ‖a * w ^ r + w ^ m‖ < 1 := by
    rw [htailEq, norm_neg]
    exact tetranomial_middleTail_norm_lt_one_of_rootBudget hbudget
  exact tetranomialRoot_spoke_norm_lt_one_of_tail
    hs hsr hrm hroot hw hc htail hu0 hu1

/-- The coefficient form used by the case theorem: the middle coefficient is
unrestricted, while the newly introduced low coefficient and the constant
term spend at most the unit budget. -/
theorem tetranomialRoot_spoke_norm_lt_one_of_lowCoeffBudget
    {m r s : ℕ} (hs : 1 ≤ s) (hsr : s ≤ r) (hrm : r ≤ m)
    {a b c w : ℂ}
    (hroot : w ^ m + a * w ^ r + b * w ^ s + c = 0)
    (hw : ‖w‖ < 1) (hc : ‖c‖ < 1)
    (hbudget : ‖b‖ + ‖c‖ ≤ 1) {u : ℝ}
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    ‖(u : ℂ) ^ m * w ^ m + a * (u : ℂ) ^ r * w ^ r +
        b * (u : ℂ) ^ s * w ^ s + c‖ < 1 := by
  have htailEq : a * w ^ r + w ^ m = -(c + b * w ^ s) := by
    linear_combination hroot
  have htail : ‖a * w ^ r + w ^ m‖ < 1 := by
    rw [htailEq, norm_neg]
    exact tetranomial_middleTail_norm_lt_one hs hw hc hbudget
  exact tetranomialRoot_spoke_norm_lt_one_of_tail
    hs hsr hrm hroot hw hc htail hu0 hu1

end ErdosProblems.Erdos1041
