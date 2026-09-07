import ErdosProblems.Erdos1041.SexticSecondModePhaseCircle
import Mathlib.Tactic

/-!
# Erdős #1041: the pure second-mode circle lifts through every tangent cubic

On an adjacent sixth-root chord the imaginary part of the cube has a fixed
sign.  Antipodal reflection preserves the even second-mode/sextic model and
reverses the tangent cubic perturbation.  Consequently every safe pure
second-mode chord has a safe antipodal choice after adding an arbitrary real
multiple of `I * z^3`.
-/

namespace ErdosProblems.Erdos1041.SexticSecondModeCubicLift

noncomputable section

open ErdosProblems.Erdos1041.SexticCanonicalMixedSlice

def adjacentPoint (r t : ℝ) : ℂ :=
  ⟨r * (1 - t / 2), r * sqrtThree * t / 2⟩

def evenModel (B z : ℂ) : ℝ := (B * z ^ 2 - z ^ 6).re

def tangentCubic (c : ℝ) (z : ℂ) : ℝ :=
  (((c : ℂ) * Complex.I) * z ^ 3).re

def liftedModel (B : ℂ) (c : ℝ) (z : ℂ) : ℝ :=
  evenModel B z + tangentCubic c z

/-- The cubic imaginary part on the canonical adjacent chord is a positive
constant times `t(1-t)`. -/
theorem adjacentPoint_cube_im (r t : ℝ) :
    (adjacentPoint r t ^ 3).im =
      (3 * sqrtThree / 2) * r ^ 3 * t * (1 - t) := by
  simp [adjacentPoint, pow_succ, Complex.mul_re, Complex.mul_im]
  linear_combination
    (-r ^ 3 * sqrtThree * t ^ 3 / 8) * sqrtThree_sq

theorem adjacentPoint_cube_im_nonneg
    {r t : ℝ} (hr : 0 ≤ r) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    0 ≤ (adjacentPoint r t ^ 3).im := by
  rw [adjacentPoint_cube_im]
  have hs : 0 < sqrtThree := sqrtThree_pos
  have htail : 0 ≤ 1 - t := sub_nonneg.mpr ht1
  positivity

/-- Multiplication by `cI` turns the fixed imaginary cubic shape into its
negative scalar multiple. -/
theorem tangentCubic_eq_neg_mul_im (c : ℝ) (z : ℂ) :
    tangentCubic c z = -c * (z ^ 3).im := by
  simp [tangentCubic, Complex.mul_re, Complex.mul_im]

/-- Antipodal reflection preserves the even part. -/
theorem evenModel_neg (B z : ℂ) : evenModel B (-z) = evenModel B z := by
  simp [evenModel]
  ring_nf

/-- Antipodal reflection reverses the tangent cubic. -/
theorem tangentCubic_neg (c : ℝ) (z : ℂ) :
    tangentCubic c (-z) = -tangentCubic c z := by
  rw [tangentCubic_eq_neg_mul_im, tangentCubic_eq_neg_mul_im]
  have hpow : (-z) ^ 3 = -(z ^ 3) := by ring
  rw [hpow]
  simp

/-- The symmetry lift: a chord safe for the even model has either itself or
its antipodal copy safe after an arbitrary tangent cubic perturbation. -/
theorem exists_safe_antipodal_lift
    {B : ℂ} {c r : ℝ} (hr : 0 ≤ r)
    (hbase : ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
      evenModel B (adjacentPoint r t) ≤ 0) :
    (∀ t : ℝ, 0 ≤ t → t ≤ 1 →
      liftedModel B c (adjacentPoint r t) ≤ 0) ∨
    (∀ t : ℝ, 0 ≤ t → t ≤ 1 →
      liftedModel B c (-adjacentPoint r t) ≤ 0) := by
  by_cases hc : 0 ≤ c
  · left
    intro t ht0 ht1
    have him := adjacentPoint_cube_im_nonneg hr ht0 ht1
    have htangent : tangentCubic c (adjacentPoint r t) ≤ 0 := by
      rw [tangentCubic_eq_neg_mul_im]
      exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hc) him
    exact add_nonpos (hbase t ht0 ht1) htangent
  · right
    intro t ht0 ht1
    have hc' : c ≤ 0 := le_of_not_ge hc
    have him := adjacentPoint_cube_im_nonneg hr ht0 ht1
    have htangent : tangentCubic c (adjacentPoint r t) ≥ 0 := by
      rw [tangentCubic_eq_neg_mul_im]
      exact mul_nonneg (neg_nonneg.mpr hc') him
    rw [liftedModel, evenModel_neg, tangentCubic_neg]
    exact add_nonpos (hbase t ht0 ht1) (neg_nonpos.mpr htangent)

/-- The tangent cubic vanishes on any ray whose direction has real cube.
This is the radial-tail compatibility used by sixth-root spokes. -/
theorem tangentCubic_eq_zero_of_cube_im_zero
    {c : ℝ} {z : ℂ} (hzero : (z ^ 3).im = 0) :
    tangentCubic c z = 0 := by
  rw [tangentCubic_eq_neg_mul_im, hzero]
  ring

end

end ErdosProblems.Erdos1041.SexticSecondModeCubicLift
