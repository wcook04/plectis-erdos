/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib

/-!
# Trusted challenge for the Erdős #1041 centred cyclic tetranomial spoke package

One question, two routes.  For a root `w` of a centred tetranomial
`w^m + a w^r + b w^s + c` with `1 ≤ s ≤ r ≤ m`, the *spoke* is the radial
segment `u ↦ u·w`, `u ∈ [0,1]`, from the origin to the root, and the spoke is
*safe* when the tetranomial stays strictly inside the unit disc along it.

The coefficient route: an exact Abel factorisation of the tetranomial along a
spoke turns a root-dependent budget `‖c‖ + ‖b‖‖w‖^s < 1`, or the coefficient-only
budget `‖b‖ + ‖c‖ ≤ 1`, into strict control of the whole spoke.  The energy
route: an exact signed mixed-moment identity for the finite root family gives an
`L²` energy, and energy below `card S − 1` forces two distinct safe spokes.

This package merges the two former configurations
`ExternalVerification1041SignedMomentTetranomial` and
`ExternalVerification1041CyclicTetranomialCoefficient`, which shared the same
object, the same spoke, and the same hypothesis shape.  Injective root indexing,
cyclic lifting, and final path assembly remain outside these declarations.
-/

open scoped ComplexConjugate

namespace Erdos249257.ExternalVerification1041TetranomialSpokes

/-- Abel summation for a root of a centred tetranomial: the value along the
spoke `u·w` is an exact three-term combination of `c`, `a w^r + w^m`, and `w^m`
with real coefficients `1 - u^s`, `u^s - u^r`, `u^r - u^m`. -/
theorem tetranomialRoot_spoke_factorization
    {m r s : ℕ} {a b c w : ℂ} {u : ℝ}
    (hroot : w ^ m + a * w ^ r + b * w ^ s + c = 0) :
    (u : ℂ) ^ m * w ^ m + a * (u : ℂ) ^ r * w ^ r +
        b * (u : ℂ) ^ s * w ^ s + c =
      ((1 - u ^ s : ℝ) : ℂ) * c -
        ((u ^ s - u ^ r : ℝ) : ℂ) * (a * w ^ r + w ^ m) -
          ((u ^ r - u ^ m : ℝ) : ℂ) * w ^ m := by
  sorry

/-- The root-dependent coefficient condition `‖c‖ + ‖b‖‖w‖^s < 1` forces the
complete root spoke strictly inside the unit lemniscate. -/
theorem tetranomialRoot_spoke_norm_lt_one_of_rootBudget
    {m r s : ℕ} (hs : 1 ≤ s) (hsr : s ≤ r) (hrm : r ≤ m)
    {a b c w : ℂ}
    (hroot : w ^ m + a * w ^ r + b * w ^ s + c = 0)
    (hw : ‖w‖ < 1) (hc : ‖c‖ < 1)
    (hbudget : ‖c‖ + ‖b‖ * ‖w‖ ^ s < 1) {u : ℝ}
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    ‖(u : ℂ) ^ m * w ^ m + a * (u : ℂ) ^ r * w ^ r +
        b * (u : ℂ) ^ s * w ^ s + c‖ < 1 := by
  sorry

/-- The coefficient-only corollary: the middle coefficient `a` is unrestricted,
while `b` and `c` spend at most the unit budget `‖b‖ + ‖c‖ ≤ 1`. -/
theorem tetranomialRoot_spoke_norm_lt_one_of_lowCoeffBudget
    {m r s : ℕ} (hs : 1 ≤ s) (hsr : s ≤ r) (hrm : r ≤ m)
    {a b c w : ℂ}
    (hroot : w ^ m + a * w ^ r + b * w ^ s + c = 0)
    (hw : ‖w‖ < 1) (hc : ‖c‖ < 1)
    (hbudget : ‖b‖ + ‖c‖ ≤ 1) {u : ℝ}
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    ‖(u : ℂ) ^ m * w ^ m + a * (u : ℂ) ^ r * w ^ r +
        b * (u : ℂ) ^ s * w ^ s + c‖ < 1 := by
  sorry

/-- Exact finite-family energy identity, including the signed mixed moment. -/
theorem sum_normSq_const_add_mul
    {ι : Type*} (S : Finset ι) (v : ι → ℂ) (b c : ℂ) :
    ∑ i ∈ S, Complex.normSq (c + b * v i) =
      (S.card : ℝ) * Complex.normSq c +
        Complex.normSq b * ∑ i ∈ S, Complex.normSq (v i) +
          2 * (conj c * b * (∑ i ∈ S, v i)).re := by
  sorry

/-- Energy below `card S - 1` forces two distinct strict unit tails. -/
theorem exists_two_tails_norm_lt_one_of_exact_L2_budget
    {ι : Type*} (S : Finset ι) (v : ι → ℂ) (b c : ℂ)
    (hcard : 2 ≤ S.card)
    (hbudget :
      (S.card : ℝ) * Complex.normSq c +
          Complex.normSq b * ∑ i ∈ S, Complex.normSq (v i) +
            2 * (conj c * b * (∑ i ∈ S, v i)).re <
        (S.card : ℝ) - 1) :
    ∃ i ∈ S, ∃ j ∈ S, i ≠ j ∧
      ‖c + b * v i‖ < 1 ∧ ‖c + b * v j‖ < 1 := by
  sorry

/-- Finite indexed-root form: the signed moment budget selects two distinct
indices whose complete tetranomial spokes lie strictly below one.  Distinct
root values additionally require injectivity of `w`. -/
theorem exists_two_tetranomialRoot_safeSpokes_of_moment_coeff_budget
    {ι : Type*} (S : Finset ι) (w : ι → ℂ)
    {m r s : ℕ} (hs : 1 ≤ s) (hsr : s ≤ r) (hrm : r ≤ m)
    {a b c moment : ℂ}
    (hcard : 2 ≤ S.card)
    (hroot : ∀ i ∈ S, w i ^ m + a * w i ^ r + b * w i ^ s + c = 0)
    (hw : ∀ i ∈ S, ‖w i‖ < 1) (hc : ‖c‖ < 1)
    (hmoment : ∑ i ∈ S, w i ^ s = moment)
    (hcoeff :
      (S.card : ℝ) * (Complex.normSq b + Complex.normSq c) +
          2 * (conj c * b * moment).re <
        (S.card : ℝ) - 1) :
    ∃ i ∈ S, ∃ j ∈ S, i ≠ j ∧
      (∀ u : ℝ, 0 ≤ u → u ≤ 1 →
        ‖(u : ℂ) ^ m * w i ^ m + a * (u : ℂ) ^ r * w i ^ r +
          b * (u : ℂ) ^ s * w i ^ s + c‖ < 1) ∧
      (∀ u : ℝ, 0 ≤ u → u ≤ 1 →
        ‖(u : ℂ) ^ m * w j ^ m + a * (u : ℂ) ^ r * w j ^ r +
          b * (u : ℂ) ^ s * w j ^ s + c‖ < 1) := by
  sorry

end Erdos249257.ExternalVerification1041TetranomialSpokes
