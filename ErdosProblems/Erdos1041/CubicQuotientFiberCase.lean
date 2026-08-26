import Mathlib

/-!
# Erdős #1041: a safe cubic spoke and its cyclic-fibre consumer

Every monic cubic whose three listed roots lie in the open unit disk has at
least one root whose complete spoke from the origin stays in the closed unit
sublevel set.  The proof selects a root by a three-charge sum and then applies
AM--GM to the other two root distances.  The resulting envelope is exactly
`(1-t)(1+t+t^2)=1-t^3`.

The analytic companion pulls the selected spoke back through
`w=(z-h)^q`.  For `q>=2`, one safe quotient root has a regular `q`-point fibre,
which supplies two distinct roots and the strict length budget.  This file
kernel-checks the new cubic selector and spoke estimate; finite fibre existence
and the regular-orbit mean-square identity are proved in ordinary mathematics
in the companion note and are not asserted as axioms here.
-/

open scoped ComplexConjugate

namespace ErdosProblems.Erdos1041

/-- The real interaction of one cubic root with the other two. -/
noncomputable def cubicRootCharge (r s v : ℂ) : ℝ :=
  (r * conj (s + v)).re

/-- The three cubic root charges sum to total squared barycentre minus total
squared radius. -/
theorem cubicRootCharge_sum_identity (r s v : ℂ) :
    cubicRootCharge r s v + cubicRootCharge s r v + cubicRootCharge v r s =
      Complex.normSq (r + s + v) -
        Complex.normSq r - Complex.normSq s - Complex.normSq v := by
  simp only [cubicRootCharge, Complex.mul_re, Complex.add_re, Complex.add_im,
    Complex.conj_re, Complex.conj_im, Complex.normSq_apply]
  ring

/-- Three roots in the open unit disk cannot all have charge at most `-1`. -/
theorem one_cubicRootCharge_gt_neg_one {r s v : ℂ}
    (hr : ‖r‖ < 1) (hs : ‖s‖ < 1) (hv : ‖v‖ < 1) :
    -1 < cubicRootCharge r s v ∨
      -1 < cubicRootCharge s r v ∨
      -1 < cubicRootCharge v r s := by
  have hrSq : Complex.normSq r < 1 := by
    rw [Complex.normSq_eq_norm_sq]
    nlinarith [norm_nonneg r]
  have hsSq : Complex.normSq s < 1 := by
    rw [Complex.normSq_eq_norm_sq]
    nlinarith [norm_nonneg s]
  have hvSq : Complex.normSq v < 1 := by
    rw [Complex.normSq_eq_norm_sq]
    nlinarith [norm_nonneg v]
  have hsumNonneg : 0 ≤ Complex.normSq (r + s + v) :=
    Complex.normSq_nonneg _
  have htotal :
      -3 < cubicRootCharge r s v + cubicRootCharge s r v +
        cubicRootCharge v r s := by
    rw [cubicRootCharge_sum_identity]
    linarith
  by_contra h
  push_neg at h
  linarith

/-- Exact expansion of the two residual squared distances on a spoke. -/
theorem cubic_distance_sq_sum_identity (r s v : ℂ) (t : ℝ) :
    ‖(t : ℂ) * r - s‖ ^ 2 + ‖(t : ℂ) * r - v‖ ^ 2 =
      2 * t ^ 2 * ‖r‖ ^ 2 + ‖s‖ ^ 2 + ‖v‖ ^ 2 -
        2 * t * cubicRootCharge r s v := by
  simp only [← Complex.normSq_eq_norm_sq, Complex.normSq_apply,
    cubicRootCharge, Complex.sub_re, Complex.sub_im, Complex.mul_re,
    Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.add_re,
    Complex.add_im, Complex.conj_re, Complex.conj_im, zero_mul, add_zero,
    mul_zero, zero_add]
  ring

/-- AM--GM plus a charge lower bound turns the two residual root distances
into the cubic cyclotomic envelope. -/
theorem cubic_distanceProduct_le_cyclotomic
    {t R S V A x y : ℝ}
    (ht0 : 0 ≤ t)
    (hR0 : 0 ≤ R) (hR1 : R ≤ 1)
    (hS0 : 0 ≤ S) (hS1 : S ≤ 1)
    (hV0 : 0 ≤ V) (hV1 : V ≤ 1)
    (hA : -1 ≤ A)
    (hsq : x ^ 2 + y ^ 2 =
      2 * t ^ 2 * R ^ 2 + S ^ 2 + V ^ 2 - 2 * t * A) :
    x * y ≤ 1 + t + t ^ 2 := by
  have hR2 : R ^ 2 ≤ 1 := by
    have hprod : 0 ≤ (1 - R) * (1 + R) :=
      mul_nonneg (sub_nonneg.mpr hR1) (by linarith)
    nlinarith
  have hS2 : S ^ 2 ≤ 1 := by
    have hprod : 0 ≤ (1 - S) * (1 + S) :=
      mul_nonneg (sub_nonneg.mpr hS1) (by linarith)
    nlinarith
  have hV2 : V ^ 2 ≤ 1 := by
    have hprod : 0 ≤ (1 - V) * (1 + V) :=
      mul_nonneg (sub_nonneg.mpr hV1) (by linarith)
    nlinarith
  have hcharge : -2 * t * A ≤ 2 * t := by
    have hprod : 0 ≤ t * (A + 1) := mul_nonneg ht0 (by linarith)
    nlinarith
  have hamgm : 2 * x * y ≤ x ^ 2 + y ^ 2 := by
    nlinarith [sq_nonneg (x - y)]
  have htR2 : t ^ 2 * R ^ 2 ≤ t ^ 2 := by
    simpa using mul_le_mul_of_nonneg_left hR2 (sq_nonneg t)
  linarith

/-- The cubic cyclotomic envelope, including a root-radius factor, is at most
one on the unit interval. -/
theorem cubic_cyclotomic_envelope_le_one {t R : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (hR0 : 0 ≤ R) (hR1 : R ≤ 1) :
    R * (1 - t) * (1 + t + t ^ 2) ≤ 1 := by
  have hfac0 : 0 ≤ (1 - t) * (1 + t + t ^ 2) :=
    mul_nonneg (sub_nonneg.mpr ht1) (by nlinarith [sq_nonneg t])
  have hfac : (1 - t) * (1 + t + t ^ 2) = 1 - t ^ 3 := by ring
  have hfac1 : (1 - t) * (1 + t + t ^ 2) ≤ 1 := by
    rw [hfac]
    exact sub_le_self _ (pow_nonneg ht0 3)
  calc
    R * (1 - t) * (1 + t + t ^ 2)
        = R * ((1 - t) * (1 + t + t ^ 2)) := by ring
    _ ≤ 1 * ((1 - t) * (1 + t + t ^ 2)) :=
      mul_le_mul_of_nonneg_right hR1 hfac0
    _ ≤ 1 := by simpa using hfac1

/-- A cubic root whose charge is at least `-1` has a complete safe radial
spoke.  The displayed product is the monic cubic written by its three roots. -/
theorem cubicRoot_spoke_norm_le_one_of_charge {r s v : ℂ}
    (hr : ‖r‖ ≤ 1) (hs : ‖s‖ ≤ 1) (hv : ‖v‖ ≤ 1)
    (hcharge : -1 ≤ cubicRootCharge r s v)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ‖((t : ℂ) * r - r) * ((t : ℂ) * r - s) * ((t : ℂ) * r - v)‖ ≤ 1 := by
  have hsq := cubic_distance_sq_sum_identity r s v t
  have hdist :
      ‖(t : ℂ) * r - s‖ * ‖(t : ℂ) * r - v‖ ≤ 1 + t + t ^ 2 :=
    cubic_distanceProduct_le_cyclotomic ht0
      (norm_nonneg r) hr (norm_nonneg s) hs (norm_nonneg v) hv hcharge hsq
  have hfirst : (t : ℂ) * r - r = (((t - 1 : ℝ) : ℂ) * r) := by
    push_cast
    ring
  have htminus : t - 1 ≤ 0 := by linarith
  have hnormFirst : ‖(t : ℂ) * r - r‖ = (1 - t) * ‖r‖ := by
    rw [hfirst, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonpos htminus]
    ring
  have hcoef : 0 ≤ ‖r‖ * (1 - t) :=
    mul_nonneg (norm_nonneg r) (sub_nonneg.mpr ht1)
  calc
    ‖((t : ℂ) * r - r) * ((t : ℂ) * r - s) * ((t : ℂ) * r - v)‖
        = ‖r‖ * (1 - t) *
            (‖(t : ℂ) * r - s‖ * ‖(t : ℂ) * r - v‖) := by
          rw [norm_mul, norm_mul, hnormFirst]
          ring
    _ ≤ ‖r‖ * (1 - t) * (1 + t + t ^ 2) :=
      mul_le_mul_of_nonneg_left hdist hcoef
    _ ≤ 1 := cubic_cyclotomic_envelope_le_one ht0 ht1 (norm_nonneg r) hr

/-- Fan-in: among three listed roots in the open unit disk, one of the three
complete origin spokes is safe for their monic cubic. -/
theorem cubic_has_safe_root_spoke {r s v : ℂ}
    (hr : ‖r‖ < 1) (hs : ‖s‖ < 1) (hv : ‖v‖ < 1) :
    (∀ t : ℝ, 0 ≤ t → t ≤ 1 →
      ‖((t : ℂ) * r - r) * ((t : ℂ) * r - s) * ((t : ℂ) * r - v)‖ ≤ 1) ∨
    (∀ t : ℝ, 0 ≤ t → t ≤ 1 →
      ‖((t : ℂ) * s - s) * ((t : ℂ) * s - r) * ((t : ℂ) * s - v)‖ ≤ 1) ∨
    (∀ t : ℝ, 0 ≤ t → t ≤ 1 →
      ‖((t : ℂ) * v - v) * ((t : ℂ) * v - r) * ((t : ℂ) * v - s)‖ ≤ 1) := by
  rcases one_cubicRootCharge_gt_neg_one hr hs hv with h | h | h
  · exact Or.inl (fun t ht0 ht1 =>
      cubicRoot_spoke_norm_le_one_of_charge (le_of_lt hr) (le_of_lt hs)
        (le_of_lt hv) (le_of_lt h) ht0 ht1)
  · exact Or.inr (Or.inl (fun t ht0 ht1 =>
      cubicRoot_spoke_norm_le_one_of_charge (le_of_lt hs) (le_of_lt hr)
        (le_of_lt hv) (le_of_lt h) ht0 ht1))
  · exact Or.inr (Or.inr (fun t ht0 ht1 =>
      cubicRoot_spoke_norm_le_one_of_charge (le_of_lt hv) (le_of_lt hr)
        (le_of_lt hs) (le_of_lt h) ht0 ht1))

/-- Exact arithmetic certificate showing that the cubic charge implication is
degree-sharp.  For the quartic with three roots at `L=999/1000` and the fourth
at `L*u`, where `‖u‖=1` and `u.re=-1/3`, the isolated root has charge
`-L^2 >= -1`.  At `t=2/5` its squared spoke value is the second expression
below, which is strictly greater than one. -/
theorem quartic_charge_envelope_counterexample :
    -1 ≤ -(((999 : ℝ) / 1000) ^ 2) ∧
      1 < ((999 : ℝ) / 1000) ^ 8 * (1 - (2 : ℝ) / 5) ^ 2 *
        (1 + ((2 : ℝ) / 5) ^ 2 + 2 * ((2 : ℝ) / 5) / 3) ^ 3 := by
  norm_num

end ErdosProblems.Erdos1041
