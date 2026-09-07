import Mathlib.Tactic

/-!
# Erdős #1041: an exact canonical sextic mixed slice

This module checks the load-bearing real algebra in
`SexticCanonicalMixedSlice.md`.  For

`H_u(z) = Re (-I * u * z - z^2 - z^6)`, `u ≥ 0`,

one fixed truncated connector between the sixth-root directions `1` and
`exp (-π I / 3)` is nonpositive.  The chord certificate has one exact double
contact and factors into a square times a cubic with positive Bernstein
coefficients.
-/

namespace ErdosProblems.Erdos1041.SexticCanonicalMixedSlice

noncomputable section

def sqrtThree : ℝ := Real.sqrt 3

/-- The fourth power of the exact truncation radius. -/
def q : ℝ := (7 + 4 * sqrtThree) / 27

def radius : ℝ := Real.sqrt (Real.sqrt q)

/-- The positive cubic left after removing the exact double contact. -/
def cubic (t : ℝ) : ℝ :=
  t ^ 3 + (-6 + sqrtThree) * t ^ 2 + (27 / 2 - 7 * sqrtThree) * t
    + (-67 / 2 + 41 * sqrtThree / 2)

def cubicBernstein (t : ℝ) : ℝ :=
    (-67 / 2 + 41 * sqrtThree / 2) * (1 - t) ^ 3
  + 3 * (-29 + 109 * sqrtThree / 6) * t * (1 - t) ^ 2
  + 3 * (-53 / 2 + 97 * sqrtThree / 6) * t ^ 2 * (1 - t)
  + (-25 + 29 * sqrtThree / 2) * t ^ 3

/-- `Re(w(t)^2) + q Re(w(t)^6)` for
`w(t) = (1-t) + t exp(-π I/3)`, written over the reals. -/
def chordCarrier (t : ℝ) : ℝ :=
    -(t ^ 2 + 2 * t - 2) / 2
  + q * ((t ^ 2 - 4 * t + 1) * (t ^ 2 + 2 * t - 2) *
      (2 * t ^ 2 - 2 * t - 1) / 2)

def chordModel (u r t : ℝ) : ℝ :=
  -(r ^ 2) * chordCarrier t - u * r * sqrtThree * t / 2

def upperRayModel (_u x : ℝ) : ℝ := -(x ^ 2) - x ^ 6

def lowerRayModel (u x : ℝ) : ℝ :=
  -(u * sqrtThree * x / 2) + x ^ 2 / 2 - x ^ 6

theorem sqrtThree_sq : sqrtThree ^ 2 = 3 := by
  norm_num [sqrtThree]

theorem sqrtThree_pos : 0 < sqrtThree := by
  rw [sqrtThree]
  exact Real.sqrt_pos.2 (by norm_num)

theorem sqrtThree_gt_fifty_div_twentyNine :
    (50 / 29 : ℝ) < sqrtThree := by
  have hs0 : 0 ≤ sqrtThree := le_of_lt sqrtThree_pos
  by_contra h
  have hle : sqrtThree ≤ (50 / 29 : ℝ) := le_of_not_gt h
  have hsum : 0 ≤ sqrtThree + (50 / 29 : ℝ) := by positivity
  have hprod :
      0 ≤ ((50 / 29 : ℝ) - sqrtThree) *
        (sqrtThree + (50 / 29 : ℝ)) :=
    mul_nonneg (sub_nonneg.mpr hle) hsum
  nlinarith [sqrtThree_sq]

theorem q_pos : 0 < q := by
  unfold q
  nlinarith [sqrtThree_pos]

theorem half_lt_q : (1 / 2 : ℝ) < q := by
  have hs := sqrtThree_gt_fifty_div_twentyNine
  unfold q
  nlinarith

theorem q_lt_one : q < 1 := by
  have hs2 := sqrtThree_sq
  have hs0 : 0 ≤ sqrtThree := le_of_lt sqrtThree_pos
  have hslt : sqrtThree < 2 := by
    by_contra h
    have htwo : (2 : ℝ) ≤ sqrtThree := le_of_not_gt h
    have hdiff : 0 ≤ sqrtThree - 2 := sub_nonneg.mpr htwo
    have hsum : 0 ≤ sqrtThree + 2 := by nlinarith [sqrtThree_pos]
    have hprod : 0 ≤ (sqrtThree - 2) * (sqrtThree + 2) :=
      mul_nonneg hdiff hsum
    nlinarith
  unfold q
  nlinarith

theorem radius_nonneg : 0 ≤ radius := by
  unfold radius
  positivity

theorem radius_fourth : radius ^ 4 = q := by
  have hq : 0 ≤ q := le_of_lt q_pos
  have hinner : (Real.sqrt q) ^ 2 = q := Real.sq_sqrt hq
  have houter : radius ^ 2 = Real.sqrt q := by
    unfold radius
    exact Real.sq_sqrt (Real.sqrt_nonneg q)
  calc
    radius ^ 4 = (radius ^ 2) ^ 2 := by ring
    _ = (Real.sqrt q) ^ 2 := by rw [houter]
    _ = q := hinner

theorem cubic_eq_bernstein (t : ℝ) : cubic t = cubicBernstein t := by
  unfold cubic cubicBernstein
  ring

theorem cubic_bernstein_coefficients_pos :
    0 < (-67 / 2 + 41 * sqrtThree / 2 : ℝ) ∧
    0 < (-29 + 109 * sqrtThree / 6 : ℝ) ∧
    0 < (-53 / 2 + 97 * sqrtThree / 6 : ℝ) ∧
    0 < (-25 + 29 * sqrtThree / 2 : ℝ) := by
  have hs := sqrtThree_gt_fifty_div_twentyNine
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor <;> nlinarith

theorem cubic_nonneg {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    0 ≤ cubic t := by
  rw [cubic_eq_bernstein]
  rcases cubic_bernstein_coefficients_pos with ⟨h0, h1, h2, h3⟩
  have hsub : 0 ≤ 1 - t := sub_nonneg.mpr ht1
  unfold cubicBernstein
  positivity

/-- Exact square-times-positive-residual factorization of the chord carrier. -/
theorem chordCarrier_factor (t : ℝ) :
    chordCarrier t =
      q * (t + 1 + sqrtThree) * (t - sqrtThree + 1) ^ 2 * cubic t := by
  have hs2 : sqrtThree ^ 2 = 3 := sqrtThree_sq
  have hs3 : sqrtThree ^ 3 = 3 * sqrtThree := by
    calc
      sqrtThree ^ 3 = sqrtThree ^ 2 * sqrtThree := by ring
      _ = 3 * sqrtThree := by rw [hs2]
  have hs4 : sqrtThree ^ 4 = 9 := by
    calc
      sqrtThree ^ 4 = (sqrtThree ^ 2) ^ 2 := by ring
      _ = 3 ^ 2 := by rw [hs2]
      _ = 9 := by norm_num
  have hs5 : sqrtThree ^ 5 = 9 * sqrtThree := by
    calc
      sqrtThree ^ 5 = sqrtThree ^ 4 * sqrtThree := by ring
      _ = 9 * sqrtThree := by rw [hs4]
  unfold chordCarrier q cubic
  ring_nf
  rw [hs5, hs4, hs3, hs2]
  ring

theorem chordCarrier_nonneg {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    0 ≤ chordCarrier t := by
  rw [chordCarrier_factor]
  have hq : 0 ≤ q := le_of_lt q_pos
  have hlinear : 0 ≤ t + 1 + sqrtThree := by
    nlinarith [sqrtThree_pos]
  have hc : 0 ≤ cubic t := cubic_nonneg ht0 ht1
  exact mul_nonneg (mul_nonneg (mul_nonneg hq hlinear) (sq_nonneg _)) hc

theorem chordModel_nonpos {u r t : ℝ} (hu : 0 ≤ u) (hr : 0 ≤ r)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    chordModel u r t ≤ 0 := by
  have hc : 0 ≤ chordCarrier t := chordCarrier_nonneg ht0 ht1
  have hfirstMul : 0 ≤ r ^ 2 * chordCarrier t :=
    mul_nonneg (sq_nonneg r) hc
  have hs0 : 0 ≤ sqrtThree := le_of_lt sqrtThree_pos
  have hsecondMul : 0 ≤ u * r * sqrtThree * t / 2 := by
    exact div_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hu hr) hs0) ht0) (by norm_num)
  have hfirst : -(r ^ 2) * chordCarrier t ≤ 0 := by nlinarith
  have hsecond : -(u * r * sqrtThree * t / 2) ≤ 0 := by nlinarith
  unfold chordModel
  linarith

theorem upperRayModel_nonpos (u x : ℝ) : upperRayModel u x ≤ 0 := by
  have h2 : 0 ≤ x ^ 2 := sq_nonneg x
  have h6 : 0 ≤ x ^ 6 := by positivity
  unfold upperRayModel
  linarith

theorem lowerRayModel_nonpos {u x : ℝ} (hu : 0 ≤ u) (hx : 0 ≤ x)
    (hxq : q ≤ x ^ 4) :
    lowerRayModel u x ≤ 0 := by
  have hhalf : (1 / 2 : ℝ) ≤ x ^ 4 := (le_of_lt half_lt_q).trans hxq
  have hbase : x ^ 2 / 2 - x ^ 6 ≤ 0 := by
    have hid : x ^ 2 / 2 - x ^ 6 = x ^ 2 * (1 / 2 - x ^ 4) := by ring
    rw [hid]
    exact mul_nonpos_of_nonneg_of_nonpos (sq_nonneg x) (sub_nonpos.mpr hhalf)
  have hs0 : 0 ≤ sqrtThree := le_of_lt sqrtThree_pos
  have htiltMul : 0 ≤ u * sqrtThree * x / 2 := by
    exact div_nonneg (mul_nonneg (mul_nonneg hu hs0) hx) (by norm_num)
  have htilt : -(u * sqrtThree * x / 2) ≤ 0 := by linarith
  unfold lowerRayModel
  linarith

/-- One exact connector works for the complete canonical slice `u ≥ 0`. -/
theorem canonicalSlice_connector_nonpos {u : ℝ} (hu : 0 ≤ u) :
    (∀ t : ℝ, 0 ≤ t → t ≤ 1 → chordModel u radius t ≤ 0) ∧
    (∀ x : ℝ, radius ≤ x → upperRayModel u x ≤ 0) ∧
    (∀ x : ℝ, radius ≤ x → lowerRayModel u x ≤ 0) := by
  refine ⟨?_, ?_, ?_⟩
  · intro t ht0 ht1
    exact chordModel_nonpos hu radius_nonneg ht0 ht1
  · intro x _
    exact upperRayModel_nonpos u x
  · intro x hrx
    have hx : 0 ≤ x := radius_nonneg.trans hrx
    have hxpow : radius ^ 4 ≤ x ^ 4 :=
      pow_le_pow_left₀ radius_nonneg hrx 4
    rw [radius_fourth] at hxpow
    exact lowerRayModel_nonpos hu hx hxpow

end

end ErdosProblems.Erdos1041.SexticCanonicalMixedSlice
