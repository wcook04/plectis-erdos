import ErdosProblems.Erdos1041.SexticCanonicalMixedSlice

/-!
# Erdős #1041: the sextic square-contact null branch

This module checks the real-algebraic certificate for the one-dimensional
direction which is invisible to all four first-order contacts at the canonical
sextic point.  The normalized chord polynomial is affine in the branch
parameter `β`; both endpoint polynomials are nonpositive, so the whole segment
is nonpositive.  The second endpoint is a square times `(1-t)` times a cubic
with positive Bernstein coefficients.
-/

namespace ErdosProblems.Erdos1041.SexticNullBranch

noncomputable section

open SexticCanonicalMixedSlice

def s : ℝ := sqrtThree
def q0 : ℝ := (7 + 4 * s) / 27

/-- Last branch parameter before the non-real ray becomes tangent at its
truncation endpoint. -/
def betaStar : ℝ := (106 + 25 * s) / 1221

/-- Fourth power of the branch truncation radius. -/
def qBranch (β : ℝ) : ℝ := q0 * (1 + (3 / 2) * β * (s - 1))

def branchRadius (β : ℝ) : ℝ := Real.sqrt (Real.sqrt (qBranch β))

def p (t : ℝ) : ℝ := t ^ 2 + 2 * t - 2
def leftFactor (t : ℝ) : ℝ := t ^ 2 - 4 * t + 1
def rightFactor (t : ℝ) : ℝ := 2 * t ^ 2 - 2 * t - 1

/-- Twice the canonical chord value after division by `r²`. -/
def baseChord (t : ℝ) : ℝ :=
  p t * (1 - q0 * leftFactor t * rightFactor t)

/-- First variation in the unique null direction. -/
def nullSlope (t : ℝ) : ℝ :=
    -(3 / 2) * q0 * (s - 1) * p t * leftFactor t * rightFactor t
  + 3 * s * (2 - s) * t - 3 * s * t * (1 - t)

def branchChord (β t : ℝ) : ℝ := baseChord t + β * nullSlope t

/-- Positive cubic remaining at the terminal branch parameter. -/
def endpointCubic (t : ℝ) : ℝ :=
  -t ^ 3 + (4 - 2 * s) * t ^ 2 + (-13 / 2 + 10 * s) * t
    + (69 / 2 - 17 * s)

def endpointCubicBernstein (t : ℝ) : ℝ :=
    (69 / 2 - 17 * s) * (1 - t) ^ 3
  + 3 * (97 / 3 - 41 * s / 3) * t * (1 - t) ^ 2
  + 3 * (63 / 2 - 11 * s) * t ^ 2 * (1 - t)
  + (31 - 9 * s) * t ^ 3

/-- The non-real selected ray, after putting `x=r*y` and dividing by `r²/2`. -/
def branchRay (β y : ℝ) : ℝ :=
  3 * s * β * (2 - s) * y + y ^ 2 - 2 * qBranch β * y ^ 6

theorem s_sq : s ^ 2 = 3 := by simpa [s] using sqrtThree_sq

theorem s_pos : 0 < s := by simpa [s] using sqrtThree_pos

theorem s_gt_fifty_div_twentyNine : (50 / 29 : ℝ) < s := by
  simpa [s] using sqrtThree_gt_fifty_div_twentyNine

theorem q0_pos : 0 < q0 := by
  unfold q0
  nlinarith [s_pos]

theorem s_lt_two : s < 2 := by
  have hs0 : 0 ≤ s := le_of_lt s_pos
  by_contra h
  have htwo : (2 : ℝ) ≤ s := le_of_not_gt h
  have hprod : 0 ≤ (s - 2) * (s + 2) :=
    mul_nonneg (sub_nonneg.mpr htwo) (by nlinarith)
  nlinarith [s_sq]

theorem betaStar_pos : 0 < betaStar := by
  unfold betaStar
  nlinarith [s_pos]

theorem qBranch_pos {β : ℝ} (hβ : 0 ≤ β) : 0 < qBranch β := by
  have hsm1 : 0 < s - 1 := by
    have hs := s_gt_fifty_div_twentyNine
    nlinarith
  have hfactor : 0 < 1 + (3 / 2 : ℝ) * β * (s - 1) := by
    nlinarith [mul_nonneg hβ (le_of_lt hsm1)]
  exact mul_pos q0_pos hfactor

theorem branchRadius_nonneg (β : ℝ) : 0 ≤ branchRadius β := by
  unfold branchRadius
  positivity

theorem branchRadius_fourth {β : ℝ} (hβ : 0 ≤ β) :
    branchRadius β ^ 4 = qBranch β := by
  have hq : 0 ≤ qBranch β := le_of_lt (qBranch_pos hβ)
  have hinner : (Real.sqrt (qBranch β)) ^ 2 = qBranch β := Real.sq_sqrt hq
  have houter : branchRadius β ^ 2 = Real.sqrt (qBranch β) := by
    unfold branchRadius
    exact Real.sq_sqrt (Real.sqrt_nonneg _)
  calc
    branchRadius β ^ 4 = (branchRadius β ^ 2) ^ 2 := by ring
    _ = (Real.sqrt (qBranch β)) ^ 2 := by rw [houter]
    _ = qBranch β := hinner

theorem baseChord_eq_carrier (t : ℝ) :
    baseChord t = -2 * chordCarrier t := by
  unfold baseChord p leftFactor rightFactor chordCarrier q0 q s
  ring

theorem baseChord_nonpos {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    baseChord t ≤ 0 := by
  rw [baseChord_eq_carrier]
  have hc := chordCarrier_nonneg ht0 ht1
  linarith

theorem endpointCubic_eq_bernstein (t : ℝ) :
    endpointCubic t = endpointCubicBernstein t := by
  unfold endpointCubic endpointCubicBernstein
  ring

theorem endpointCubic_bernstein_coefficients_pos :
    0 < (69 / 2 - 17 * s : ℝ) ∧
    0 < (97 / 3 - 41 * s / 3 : ℝ) ∧
    0 < (63 / 2 - 11 * s : ℝ) ∧
    0 < (31 - 9 * s : ℝ) := by
  constructor
  · nlinarith [s_lt_two]
  constructor
  · nlinarith [s_lt_two]
  constructor <;> nlinarith [s_lt_two]

theorem endpointCubic_nonneg {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    0 ≤ endpointCubic t := by
  rw [endpointCubic_eq_bernstein]
  rcases endpointCubic_bernstein_coefficients_pos with ⟨h0, h1, h2, h3⟩
  have hsub : 0 ≤ 1 - t := sub_nonneg.mpr ht1
  unfold endpointCubicBernstein
  positivity

/-- At `β=βStar`, the old double contact persists and the selected non-real
ray endpoint becomes a new zero. -/
theorem endpointChord_factor (t : ℝ) :
    branchChord betaStar t =
      ((239 + 137 * s) / 407) * (t - 1) * (t - s + 1) ^ 2 *
        endpointCubic t := by
  have hs2 : s ^ 2 = 3 := s_sq
  have hs3 : s ^ 3 = 3 * s := by
    calc
      s ^ 3 = s ^ 2 * s := by ring
      _ = 3 * s := by rw [hs2]
  have hs4 : s ^ 4 = 9 := by
    calc
      s ^ 4 = (s ^ 2) ^ 2 := by ring
      _ = 3 ^ 2 := by rw [hs2]
      _ = 9 := by norm_num
  unfold branchChord baseChord nullSlope betaStar q0 p leftFactor rightFactor
    endpointCubic
  ring_nf
  simp only [hs4, hs3, hs2]
  ring

theorem endpointChord_nonpos {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    branchChord betaStar t ≤ 0 := by
  rw [endpointChord_factor]
  have hcoef : 0 ≤ (239 + 137 * s) / 407 := by
    nlinarith [s_pos]
  have htminus : t - 1 ≤ 0 := sub_nonpos.mpr ht1
  have hc : 0 ≤ endpointCubic t := endpointCubic_nonneg ht0 ht1
  have hleft : ((239 + 137 * s) / 407) * (t - 1) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hcoef htminus
  exact mul_nonpos_of_nonpos_of_nonneg
    (mul_nonpos_of_nonpos_of_nonneg hleft (sq_nonneg _)) hc

theorem branchChord_affine (β t : ℝ) :
    branchChord β t =
      (1 - β / betaStar) * baseChord t +
        (β / betaStar) * branchChord betaStar t := by
  have hbs : betaStar ≠ 0 := ne_of_gt betaStar_pos
  unfold branchChord
  field_simp
  ring

theorem branchChord_nonpos {β t : ℝ} (hβ0 : 0 ≤ β)
    (hβ1 : β ≤ betaStar) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    branchChord β t ≤ 0 := by
  rw [branchChord_affine]
  have hbs : 0 < betaStar := betaStar_pos
  have hw0 : 0 ≤ 1 - β / betaStar := by
    exact sub_nonneg.mpr ((div_le_one hbs).2 hβ1)
  have hw1 : 0 ≤ β / betaStar := div_nonneg hβ0 (le_of_lt hbs)
  have hb := baseChord_nonpos ht0 ht1
  have he := endpointChord_nonpos ht0 ht1
  exact add_nonpos (mul_nonpos_of_nonneg_of_nonpos hw0 hb)
    (mul_nonpos_of_nonneg_of_nonpos hw1 he)

theorem branchRay_start_factor (β : ℝ) :
    3 * s * β * (2 - s) + 1 - 2 * qBranch β =
      (-86 / 9 + 17 * s / 3) * (β - betaStar) := by
  have hs2 : s ^ 2 = 3 := s_sq
  have hs2β : s ^ 2 * β = 3 * β := by rw [hs2]
  unfold qBranch q0 betaStar
  ring_nf
  nlinarith [hs2, hs2β]

theorem branchRay_start_nonpos {β : ℝ} (hβ : β ≤ betaStar) :
    3 * s * β * (2 - s) + 1 - 2 * qBranch β ≤ 0 := by
  rw [branchRay_start_factor]
  have hcoef : 0 ≤ (-86 / 9 + 17 * s / 3 : ℝ) := by
    have hs := s_gt_fifty_div_twentyNine
    nlinarith
  exact mul_nonpos_of_nonneg_of_nonpos hcoef (sub_nonpos.mpr hβ)

theorem branchRay_nonpos {β y : ℝ} (hβ0 : 0 ≤ β)
    (hβ1 : β ≤ betaStar) (hy : 1 ≤ y) : branchRay β y ≤ 0 := by
  have hy0 : 0 ≤ y := le_trans (by norm_num) hy
  have hy_y2 : y ≤ y ^ 2 := by nlinarith [sq_nonneg (y - 1)]
  have hy2_y6 : y ^ 2 ≤ y ^ 6 := by
    have hy4 : 1 ≤ y ^ 4 := one_le_pow₀ hy
    calc
      y ^ 2 = y ^ 2 * 1 := by ring
      _ ≤ y ^ 2 * y ^ 4 := mul_le_mul_of_nonneg_left hy4 (sq_nonneg y)
      _ = y ^ 6 := by ring
  have hk : 0 ≤ 3 * s * β * (2 - s) := by
    have htwo : 0 ≤ 2 - s := sub_nonneg.mpr (le_of_lt s_lt_two)
    exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (le_of_lt s_pos)) hβ0) htwo
  have hq : 0 ≤ qBranch β := le_of_lt (qBranch_pos hβ0)
  have hfirst :
      3 * s * β * (2 - s) * y ≤ 3 * s * β * (2 - s) * y ^ 2 :=
    mul_le_mul_of_nonneg_left hy_y2 hk
  have hlast : -2 * qBranch β * y ^ 6 ≤ -2 * qBranch β * y ^ 2 := by
    have hmul := mul_le_mul_of_nonneg_left hy2_y6 (show 0 ≤ 2 * qBranch β by positivity)
    nlinarith
  have hstart := branchRay_start_nonpos hβ1
  have hscaled :
      (3 * s * β * (2 - s) + 1 - 2 * qBranch β) * y ^ 2 ≤ 0 :=
    by exact mul_nonpos_of_nonpos_of_nonneg hstart (sq_nonneg y)
  unfold branchRay
  nlinarith

/-- The complete normalized algebraic connector certificate along the null
branch.  The real ray contributes `-x²-x⁶≤0` independently. -/
theorem nullBranch_connector_nonpos {β : ℝ} (hβ0 : 0 ≤ β)
    (hβ1 : β ≤ betaStar) :
    (∀ t : ℝ, 0 ≤ t → t ≤ 1 → branchChord β t ≤ 0) ∧
    (∀ y : ℝ, 1 ≤ y → branchRay β y ≤ 0) := by
  constructor
  · intro t ht0 ht1
    exact branchChord_nonpos hβ0 hβ1 ht0 ht1
  · intro y hy
    exact branchRay_nonpos hβ0 hβ1 hy

end

end ErdosProblems.Erdos1041.SexticNullBranch
