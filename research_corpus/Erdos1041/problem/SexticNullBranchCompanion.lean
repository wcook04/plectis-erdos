import ErdosProblems.Erdos1041.SexticNullBranch

/-!
# Erdős #1041: strict companion to the sextic null branch

The zero-contact branch has a companion connector at the mirror truncation
radius.  Its chord is dominated by `branchChord (-β)`.  This file verifies the
mirror endpoint factorization, its positive Bernstein quartic, the convex
interpolation for the whole parameter interval, and the outward ray bound.
-/

namespace ErdosProblems.Erdos1041.SexticNullBranchCompanion

noncomputable section

open SexticNullBranch

def mirrorChord (β t : ℝ) : ℝ := branchChord (-β) t

/-- The actual companion chord after normalizing by its mirror radius.  `L` is
the old-radius/new-radius ratio and `M` its reciprocal. -/
def companionChord (β L M t : ℝ) : ℝ :=
    p t * (1 - qBranch (-β) * leftFactor t * rightFactor t)
  - 3 * s * β * L * (2 - s) * t
  + 3 * s * β * M * t * (1 - t)

def mirrorEndpointQuartic (t : ℝ) : ℝ :=
    t ^ 4 + (-5 + 2 * s) * t ^ 3 + (21 / 2 - 12 * s) * t ^ 2
  + (-41 + 27 * s) * t + (-8794 * s / 853 + 40775 / 1706)

def mirrorEndpointBernstein (t : ℝ) : ℝ :=
    ((40775 - 17588 * s) / 1706) * (1 - t) ^ 4
  + 4 * ((46577 - 12145 * s) / 3412) * t * (1 - t) ^ 3
  + 6 * ((17575 + 4062 * s) / 3412) * t ^ 2 * (1 - t) ^ 2
  + 4 * ((-9721 + 15151 * s) / 3412) * t ^ 3 * (1 - t)
  + ((-9041 + 5707 * s) / 853) * t ^ 4

def mirrorRay (β y : ℝ) : ℝ := branchRay (-β) y

def companionRay (β L y : ℝ) : ℝ :=
  -3 * s * β * L * (2 - s) * y + y ^ 2 - 2 * qBranch (-β) * y ^ 6

theorem mirrorEndpointQuartic_eq_bernstein (t : ℝ) :
    mirrorEndpointQuartic t = mirrorEndpointBernstein t := by
  unfold mirrorEndpointQuartic mirrorEndpointBernstein
  ring

theorem mirrorEndpoint_bernstein_coefficients_pos :
    0 < ((40775 - 17588 * s) / 1706 : ℝ) ∧
    0 < ((46577 - 12145 * s) / 3412 : ℝ) ∧
    0 < ((17575 + 4062 * s) / 3412 : ℝ) ∧
    0 < ((-9721 + 15151 * s) / 3412 : ℝ) ∧
    0 < ((-9041 + 5707 * s) / 853 : ℝ) := by
  constructor
  · nlinarith [s_lt_two]
  constructor
  · nlinarith [s_lt_two]
  constructor
  · nlinarith [s_pos]
  constructor
  · have hs := s_gt_fifty_div_twentyNine
    nlinarith
  · have hs := s_gt_fifty_div_twentyNine
    nlinarith

theorem mirrorEndpointQuartic_nonneg {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    0 ≤ mirrorEndpointQuartic t := by
  rw [mirrorEndpointQuartic_eq_bernstein]
  rcases mirrorEndpoint_bernstein_coefficients_pos with ⟨h0, h1, h2, h3, h4⟩
  have hsub : 0 ≤ 1 - t := sub_nonneg.mpr ht1
  unfold mirrorEndpointBernstein
  positivity

theorem mirrorEndpoint_factor (t : ℝ) :
    mirrorChord betaStar t =
      -((4943 + 2813 * s) / 10989) * (t - s + 1) ^ 2 *
        mirrorEndpointQuartic t := by
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
  unfold mirrorChord branchChord baseChord nullSlope betaStar q0 p leftFactor
    rightFactor mirrorEndpointQuartic
  ring_nf
  simp only [hs4, hs3, hs2]
  ring

theorem mirrorEndpoint_nonpos {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    mirrorChord betaStar t ≤ 0 := by
  rw [mirrorEndpoint_factor]
  have hcoef : 0 ≤ (4943 + 2813 * s) / 10989 := by nlinarith [s_pos]
  have hq := mirrorEndpointQuartic_nonneg ht0 ht1
  have hprod : 0 ≤ ((4943 + 2813 * s) / 10989) *
      (t - s + 1) ^ 2 * mirrorEndpointQuartic t := by positivity
  nlinarith

theorem mirrorChord_affine (β t : ℝ) :
    mirrorChord β t =
      (1 - β / betaStar) * baseChord t +
        (β / betaStar) * mirrorChord betaStar t := by
  have hbs : betaStar ≠ 0 := ne_of_gt betaStar_pos
  unfold mirrorChord branchChord
  field_simp
  ring

theorem mirrorChord_nonpos {β t : ℝ} (hβ0 : 0 ≤ β)
    (hβ1 : β ≤ betaStar) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    mirrorChord β t ≤ 0 := by
  rw [mirrorChord_affine]
  have hbs : 0 < betaStar := betaStar_pos
  have hw0 : 0 ≤ 1 - β / betaStar :=
    sub_nonneg.mpr ((div_le_one hbs).2 hβ1)
  have hw1 : 0 ≤ β / betaStar := div_nonneg hβ0 (le_of_lt hbs)
  have hb := baseChord_nonpos ht0 ht1
  have he := mirrorEndpoint_nonpos ht0 ht1
  exact add_nonpos (mul_nonpos_of_nonneg_of_nonpos hw0 hb)
    (mul_nonpos_of_nonneg_of_nonpos hw1 he)

theorem companionChord_le_mirror {β L M t : ℝ} (hβ : 0 ≤ β)
    (hL : 1 ≤ L) (hM1 : M ≤ 1)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    companionChord β L M t ≤ mirrorChord β t := by
  have htwo : 0 ≤ 2 - s := sub_nonneg.mpr (le_of_lt s_lt_two)
  have hsub : 0 ≤ 1 - t := sub_nonneg.mpr ht1
  have hA : 0 ≤ 3 * s * β * (2 - s) * t :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num)
      (le_of_lt s_pos)) hβ) htwo) ht0
  have hB : 0 ≤ 3 * s * β * t * (1 - t) :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num)
      (le_of_lt s_pos)) hβ) ht0) hsub
  have hlinear :
      3 * s * β * (2 - s) * t ≤ 3 * s * β * L * (2 - s) * t := by
    nlinarith [mul_le_mul_of_nonneg_left hL hA]
  have hcubic :
      3 * s * β * M * t * (1 - t) ≤ 3 * s * β * t * (1 - t) := by
    nlinarith [mul_le_mul_of_nonneg_left hM1 hB]
  unfold companionChord mirrorChord branchChord baseChord nullSlope qBranch
  ring_nf at hlinear hcubic ⊢
  linarith

theorem companionChord_nonpos {β L M t : ℝ} (hβ0 : 0 ≤ β)
    (hβ1 : β ≤ betaStar) (hL : 1 ≤ L) (hM1 : M ≤ 1)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : companionChord β L M t ≤ 0 := by
  exact (companionChord_le_mirror hβ0 hL hM1 ht0 ht1).trans
    (mirrorChord_nonpos hβ0 hβ1 ht0 ht1)

theorem sixth_lt_mirrorEndpointQ : (1 / 6 : ℝ) < qBranch (-betaStar) := by
  have hs2 : s ^ 2 = 3 := s_sq
  unfold qBranch q0 betaStar
  ring_nf
  nlinarith [hs2, s_pos, s_lt_two]

theorem mirrorEndpointQ_le {β : ℝ} (hβ1 : β ≤ betaStar) :
    qBranch (-betaStar) ≤ qBranch (-β) := by
  have hsm1 : 0 ≤ s - 1 := by
    have hs := s_gt_fifty_div_twentyNine
    nlinarith
  have hk : 0 ≤ q0 * (3 / 2) * (s - 1) :=
    mul_nonneg (mul_nonneg (le_of_lt q0_pos) (by norm_num)) hsm1
  unfold qBranch
  nlinarith [mul_le_mul_of_nonneg_left hβ1 hk]

theorem mirrorRay_nonpos {β y : ℝ} (hβ0 : 0 ≤ β)
    (hβ1 : β ≤ betaStar) (hy : 1 ≤ y) : mirrorRay β y ≤ 0 := by
  have hy0 : 0 ≤ y := le_trans (by norm_num) hy
  have hy2 : 1 ≤ y ^ 2 := one_le_pow₀ hy
  have hy4 : 1 ≤ y ^ 4 := one_le_pow₀ hy
  have hdiff : 0 ≤ y ^ 2 - 1 := sub_nonneg.mpr hy2
  have hfactor : y ^ 6 - 1 = (y ^ 2 - 1) * (y ^ 4 + y ^ 2 + 1) := by ring
  have hsum : 3 ≤ y ^ 4 + y ^ 2 + 1 := by linarith
  have hgrowth : 3 * (y ^ 2 - 1) ≤ y ^ 6 - 1 := by
    rw [hfactor]
    nlinarith [mul_le_mul_of_nonneg_left hsum hdiff]
  have hq : (1 / 6 : ℝ) ≤ qBranch (-β) :=
    (le_of_lt sixth_lt_mirrorEndpointQ).trans (mirrorEndpointQ_le hβ1)
  have hweighted : y ^ 2 - 1 ≤ 2 * qBranch (-β) * (y ^ 6 - 1) := by
    have hnonneg : 0 ≤ y ^ 6 - 1 := by nlinarith [hgrowth, hdiff]
    have hthird : y ^ 2 - 1 ≤ (1 / 3 : ℝ) * (y ^ 6 - 1) := by
      nlinarith [hgrowth]
    have hcoef : (1 / 3 : ℝ) ≤ 2 * qBranch (-β) := by nlinarith [hq]
    have hscale := mul_le_mul_of_nonneg_right hcoef hnonneg
    linarith
  have hK : 0 ≤ 3 * s * β * (2 - s) := by
    have htwo : 0 ≤ 2 - s := sub_nonneg.mpr (le_of_lt s_lt_two)
    exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (le_of_lt s_pos)) hβ0) htwo
  have hym1 : 0 ≤ y - 1 := sub_nonneg.mpr hy
  have hKdrop : -3 * s * β * (2 - s) * (y - 1) ≤ 0 := by
    nlinarith [mul_nonneg hK hym1]
  have hstart := branchRay_start_nonpos (β := -β) (by nlinarith [betaStar_pos])
  unfold mirrorRay branchRay
  nlinarith

theorem companionRay_le_mirror {β L y : ℝ} (hβ : 0 ≤ β)
    (hL : 1 ≤ L) (hy : 0 ≤ y) : companionRay β L y ≤ mirrorRay β y := by
  have htwo : 0 ≤ 2 - s := sub_nonneg.mpr (le_of_lt s_lt_two)
  have hA : 0 ≤ 3 * s * β * (2 - s) * y :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num)
      (le_of_lt s_pos)) hβ) htwo) hy
  unfold companionRay mirrorRay branchRay
  nlinarith [mul_le_mul_of_nonneg_left hL hA]

theorem companionRay_nonpos {β L y : ℝ} (hβ0 : 0 ≤ β)
    (hβ1 : β ≤ betaStar) (hL : 1 ≤ L) (hy : 1 ≤ y) :
    companionRay β L y ≤ 0 := by
  have hy0 : 0 ≤ y := le_trans (by norm_num) hy
  exact (companionRay_le_mirror hβ0 hL hy0).trans
    (mirrorRay_nonpos hβ0 hβ1 hy)

/-- A companion connector is nonpositive for the entire zero-contact branch.
For the geometric radii one has `L>1` and `0<M<1` whenever `β>0`, so the
comparison is strict on the chord interior. -/
theorem nullBranchCompanion_connector_nonpos {β L M : ℝ} (hβ0 : 0 ≤ β)
    (hβ1 : β ≤ betaStar) (hL : 1 ≤ L) (hM1 : M ≤ 1) :
    (∀ t : ℝ, 0 ≤ t → t ≤ 1 → companionChord β L M t ≤ 0) ∧
    (∀ y : ℝ, 1 ≤ y → companionRay β L y ≤ 0) := by
  constructor
  · intro t ht0 ht1
    exact companionChord_nonpos hβ0 hβ1 hL hM1 ht0 ht1
  · intro y hy
    exact companionRay_nonpos hβ0 hβ1 hL hy

end

end ErdosProblems.Erdos1041.SexticNullBranchCompanion
