import ErdosProblems.Erdos1041.SexticNullBranchCompanion

/-!
# Erdős #1041: a uniform tube around the positive sextic null branch

The companion connector is not merely nonpositive.  On every truncated
parameter interval `ε ≤ β ≤ betaStar` it has the explicit normalized margin
`-ε² / 10`.  The proof splits the chord at `t = 1/2`: the canonical square
factor gives a fixed margin on the first half, while the change of truncation
radius gives a quadratic margin on the second half.
-/

namespace ErdosProblems.Erdos1041.SexticNullBranchUniformMargin

noncomputable section

open SexticCanonicalMixedSlice SexticNullBranch SexticNullBranchCompanion

theorem s_lt_twentySix_div_fifteen : s < (26 / 15 : ℝ) := by
  by_contra h
  have hle : (26 / 15 : ℝ) ≤ s := le_of_not_gt h
  have hprod : 0 ≤ (s - 26 / 15) * (s + 26 / 15) := by
    exact mul_nonneg (sub_nonneg.mpr hle) (by nlinarith [s_pos])
  nlinarith [s_sq]

theorem twoHundredFiftyOne_div_oneFortyFive_lt_s :
    (251 / 145 : ℝ) < s := by
  by_contra h
  have hle : s ≤ (251 / 145 : ℝ) := le_of_not_gt h
  have hprod : 0 ≤ (251 / 145 - s) * (s + 251 / 145) := by
    exact mul_nonneg (sub_nonneg.mpr hle) (by nlinarith [s_pos])
  nlinarith [s_sq]

theorem betaStar_lt_quarter : betaStar < (1 / 4 : ℝ) := by
  unfold betaStar
  nlinarith [s_lt_two]

theorem rayMargin_constant :
    (1 / 100 : ℝ) < (-86 / 9 + 17 * s / 3) * betaStar := by
  have hs := twoHundredFiftyOne_div_oneFortyFive_lt_s
  have hs2 := s_sq
  unfold betaStar
  ring_nf
  nlinarith

theorem largeChord_constant :
    (1 / 10 : ℝ) < (3 / 10) * s * (s - 1) * (2 - s) := by
  have hs := s_lt_twentySix_div_fifteen
  have hs2 := s_sq
  nlinarith

theorem contact_square_ge_twentieth {t : ℝ} (ht : t ≤ 1 / 2) :
    (1 / 20 : ℝ) ≤ (t - s + 1) ^ 2 := by
  have hs15 : (3 / 2 : ℝ) < s := by
    nlinarith [twoHundredFiftyOne_div_oneFortyFive_lt_s]
  have hbase : (1 / 20 : ℝ) < (s - 3 / 2) ^ 2 := by
    nlinarith [s_sq, s_lt_twentySix_div_fifteen]
  have hord : s - 3 / 2 ≤ s - t - 1 := by linarith
  have hsum : 0 ≤ (s - t - 1) + (s - 3 / 2) := by nlinarith
  have hprod : 0 ≤ ((s - t - 1) - (s - 3 / 2)) *
      ((s - t - 1) + (s - 3 / 2)) :=
    mul_nonneg (sub_nonneg.mpr hord) hsum
  nlinarith

theorem cubic_ge_tenth {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (1 / 10 : ℝ) ≤ cubic t := by
  have hslo := twoHundredFiftyOne_div_oneFortyFive_lt_s
  have hshi := s_lt_twentySix_div_fifteen
  have h0 : 0 ≤ (-67 / 2 + 41 * s / 2 : ℝ) - 1 / 10 := by nlinarith
  have h1 : 0 ≤ (-29 + 109 * s / 6 : ℝ) - 1 / 10 := by nlinarith
  have h2 : 0 ≤ (-53 / 2 + 97 * s / 6 : ℝ) - 1 / 10 := by nlinarith
  have h3 : 0 ≤ (-25 + 29 * s / 2 : ℝ) - 1 / 10 := by nlinarith
  have hsub : 0 ≤ 1 - t := sub_nonneg.mpr ht1
  rw [cubic_eq_bernstein]
  unfold cubicBernstein
  have hrem : 0 ≤
      ((-67 / 2 + 41 * s / 2) - 1 / 10) * (1 - t) ^ 3
      + 3 * ((-29 + 109 * s / 6) - 1 / 10) * t * (1 - t) ^ 2
      + 3 * ((-53 / 2 + 97 * s / 6) - 1 / 10) * t ^ 2 * (1 - t)
      + ((-25 + 29 * s / 2) - 1 / 10) * t ^ 3 := by
    positivity
  have hrem' : 0 ≤
      ((-67 / 2 + 41 * sqrtThree / 2) - 1 / 10) * (1 - t) ^ 3
      + 3 * ((-29 + 109 * sqrtThree / 6) - 1 / 10) * t * (1 - t) ^ 2
      + 3 * ((-53 / 2 + 97 * sqrtThree / 6) - 1 / 10) * t ^ 2 * (1 - t)
      + ((-25 + 29 * sqrtThree / 2) - 1 / 10) * t ^ 3 := by
    simpa [s] using hrem
  nlinarith [hrem']

theorem baseChord_small_t_margin {t : ℝ} (ht0 : 0 ≤ t)
    (ht : t ≤ 1 / 2) : baseChord t ≤ -(1 / 100 : ℝ) := by
  have ht1 : t ≤ 1 := by linarith
  have hq : (1 / 2 : ℝ) ≤ q0 := by
    simpa [q0, q, s] using le_of_lt half_lt_q
  have hlin : (2 : ℝ) ≤ t + 1 + s := by
    nlinarith [s_gt_fifty_div_twentyNine]
  have hsq := contact_square_ge_twentieth ht
  have hc := cubic_ge_tenth ht0 ht1
  have hq0 : 0 ≤ q0 := le_of_lt q0_pos
  have hlin0 : 0 ≤ t + 1 + s := by linarith
  have hsq0 : 0 ≤ (t - s + 1) ^ 2 := sq_nonneg _
  have h1 : (1 : ℝ) ≤ q0 * (t + 1 + s) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hq) (sub_nonneg.mpr hlin)]
  have h2 : (1 / 20 : ℝ) ≤ q0 * (t + 1 + s) * (t - s + 1) ^ 2 := by
    have hm := mul_le_mul h1 hsq (by norm_num) (mul_nonneg hq0 hlin0)
    nlinarith
  have h3 : (1 / 200 : ℝ) ≤
      q0 * (t + 1 + s) * (t - s + 1) ^ 2 * cubic t := by
    have hm := mul_le_mul h2 hc (by norm_num)
      (mul_nonneg (mul_nonneg hq0 hlin0) hsq0)
    nlinarith
  have h3' : (1 / 200 : ℝ) ≤
      q * (t + 1 + sqrtThree) * (t - sqrtThree + 1) ^ 2 * cubic t := by
    simpa [q0, s] using h3
  rw [baseChord_eq_carrier, chordCarrier_factor]
  nlinarith [h3']

theorem mirrorEndpointQuartic_ge_nineTenths {t : ℝ} (ht0 : 0 ≤ t)
    (ht1 : t ≤ 1) : (9 / 10 : ℝ) ≤ mirrorEndpointQuartic t := by
  have hslo := twoHundredFiftyOne_div_oneFortyFive_lt_s
  have hshi := s_lt_twentySix_div_fifteen
  have h0 : 0 ≤ ((40775 - 17588 * s) / 1706 : ℝ) - 9 / 10 := by nlinarith
  have h1 : 0 ≤ ((46577 - 12145 * s) / 3412 : ℝ) - 9 / 10 := by nlinarith
  have h2 : 0 ≤ ((17575 + 4062 * s) / 3412 : ℝ) - 9 / 10 := by nlinarith
  have h3 : 0 ≤ ((-9721 + 15151 * s) / 3412 : ℝ) - 9 / 10 := by nlinarith
  have h4 : 0 ≤ ((-9041 + 5707 * s) / 853 : ℝ) - 9 / 10 := by nlinarith
  have hsub : 0 ≤ 1 - t := sub_nonneg.mpr ht1
  rw [mirrorEndpointQuartic_eq_bernstein]
  unfold mirrorEndpointBernstein
  have hrem : 0 ≤
      (((40775 - 17588 * s) / 1706) - 9 / 10) * (1 - t) ^ 4
      + 4 * (((46577 - 12145 * s) / 3412) - 9 / 10) * t * (1 - t) ^ 3
      + 6 * (((17575 + 4062 * s) / 3412) - 9 / 10) * t ^ 2 * (1 - t) ^ 2
      + 4 * (((-9721 + 15151 * s) / 3412) - 9 / 10) * t ^ 3 * (1 - t)
      + (((-9041 + 5707 * s) / 853) - 9 / 10) * t ^ 4 := by
    positivity
  nlinarith [hrem]

theorem mirrorEndpoint_small_t_margin {t : ℝ} (ht0 : 0 ≤ t)
    (ht : t ≤ 1 / 2) : mirrorChord betaStar t ≤ -(1 / 100 : ℝ) := by
  have ht1 : t ≤ 1 := by linarith
  have hcoef : (4 / 5 : ℝ) ≤ (4943 + 2813 * s) / 10989 := by
    nlinarith [twoHundredFiftyOne_div_oneFortyFive_lt_s]
  have hsq := contact_square_ge_twentieth ht
  have hquartic := mirrorEndpointQuartic_ge_nineTenths ht0 ht1
  have hcoef0 : 0 ≤ (4943 + 2813 * s) / 10989 := by nlinarith
  have hsq0 : 0 ≤ (t - s + 1) ^ 2 := sq_nonneg _
  have h1 : (1 / 25 : ℝ) ≤
      ((4943 + 2813 * s) / 10989) * (t - s + 1) ^ 2 := by
    have hm := mul_le_mul hcoef hsq (by norm_num) hcoef0
    nlinarith
  have h2 : (9 / 250 : ℝ) ≤
      ((4943 + 2813 * s) / 10989) * (t - s + 1) ^ 2 *
        mirrorEndpointQuartic t := by
    have hm := mul_le_mul h1 hquartic (by norm_num)
      (mul_nonneg hcoef0 hsq0)
    nlinarith
  rw [mirrorEndpoint_factor]
  nlinarith

theorem mirrorChord_small_t_margin {β t : ℝ} (hβ0 : 0 ≤ β)
    (hβ1 : β ≤ betaStar) (ht0 : 0 ≤ t) (ht : t ≤ 1 / 2) :
    mirrorChord β t ≤ -(1 / 100 : ℝ) := by
  rw [mirrorChord_affine]
  have hbs : 0 < betaStar := betaStar_pos
  have hw0 : 0 ≤ 1 - β / betaStar :=
    sub_nonneg.mpr ((div_le_one hbs).2 hβ1)
  have hw1 : 0 ≤ β / betaStar := div_nonneg hβ0 (le_of_lt hbs)
  have hsum : (1 - β / betaStar) + β / betaStar = 1 := by ring
  have hb := baseChord_small_t_margin ht0 ht
  have he := mirrorEndpoint_small_t_margin ht0 ht
  nlinarith [mul_nonpos_of_nonneg_of_nonpos hw0 (sub_nonpos.mpr hb),
    mul_nonpos_of_nonneg_of_nonpos hw1 (sub_nonpos.mpr he)]

theorem qBranch_betaStar_lt_one : qBranch betaStar < 1 := by
  have hs2 := s_sq
  have hshi := s_lt_two
  unfold qBranch q0 betaStar
  ring_nf
  nlinarith

theorem qBranch_le_endpoint {β : ℝ} (hβ1 : β ≤ betaStar) :
    qBranch β ≤ qBranch betaStar := by
  have hsm1 : 0 ≤ s - 1 := by
    nlinarith [s_gt_fifty_div_twentyNine]
  have hk : 0 ≤ q0 * (3 / 2) * (s - 1) :=
    mul_nonneg (mul_nonneg (le_of_lt q0_pos) (by norm_num)) hsm1
  unfold qBranch
  nlinarith [mul_le_mul_of_nonneg_left hβ1 hk]

/-- The exact radius identity forces a fourth-power separation. -/
theorem radiusRatio_fourth_separation {β L : ℝ} (hβ0 : 0 ≤ β)
    (hL : 1 ≤ L)
    (hratio : qBranch β = L ^ 4 * qBranch (-β)) :
    3 * β * (s - 1) ≤ L ^ 4 - 1 := by
  have hqmle : qBranch (-β) ≤ q0 := by
    have hsm1 : 0 ≤ s - 1 := by nlinarith [s_gt_fifty_div_twentyNine]
    have hk : 0 ≤ q0 * (3 / 2) * (s - 1) :=
      mul_nonneg (mul_nonneg (le_of_lt q0_pos) (by norm_num)) hsm1
    unfold qBranch
    nlinarith [mul_nonneg hk hβ0]
  have hL4 : 1 ≤ L ^ 4 := one_le_pow₀ hL
  have hscaled : q0 * (3 * β * (s - 1)) ≤ q0 * (L ^ 4 - 1) := by
    calc
      q0 * (3 * β * (s - 1)) = qBranch β - qBranch (-β) := by
        unfold qBranch
        ring
      _ = (L ^ 4 - 1) * qBranch (-β) := by rw [hratio]; ring
      _ ≤ (L ^ 4 - 1) * q0 :=
        mul_le_mul_of_nonneg_left hqmle (by linarith)
      _ = q0 * (L ^ 4 - 1) := by ring
  by_contra h
  have hlt : L ^ 4 - 1 < 3 * β * (s - 1) := lt_of_not_ge h
  have hm := mul_lt_mul_of_pos_left hlt q0_pos
  linarith

theorem radiusRatio_lt_two {β L : ℝ} (hβ1 : β ≤ betaStar) (hL : 1 ≤ L)
    (hratio : qBranch β = L ^ 4 * qBranch (-β)) : L < 2 := by
  have hqp : qBranch β < 1 :=
    (qBranch_le_endpoint hβ1).trans_lt qBranch_betaStar_lt_one
  have hqm : (1 / 6 : ℝ) < qBranch (-β) :=
    sixth_lt_mirrorEndpointQ.trans_le (mirrorEndpointQ_le hβ1)
  by_contra h
  have htwo : (2 : ℝ) ≤ L := le_of_not_gt h
  have hL4 : (16 : ℝ) ≤ L ^ 4 := by
    have hp := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) htwo 4
    norm_num at hp ⊢
    exact hp
  have hL4pos : 0 < L ^ 4 := by positivity
  have hstrict : L ^ 4 * (1 / 6 : ℝ) < L ^ 4 * qBranch (-β) :=
    mul_lt_mul_of_pos_left hqm hL4pos
  have hbase : (8 / 3 : ℝ) ≤ L ^ 4 * (1 / 6 : ℝ) := by nlinarith
  rw [← hratio] at hstrict
  nlinarith

theorem fourthSeparation_implies_linear {β L : ℝ} (hL1 : 1 ≤ L)
    (hL2 : L ≤ 2) (hfourth : 3 * β * (s - 1) ≤ L ^ 4 - 1) :
    (s - 1) * β / 5 ≤ L - 1 := by
  have hL0 : 0 ≤ L := by linarith
  have hsq : L ^ 2 ≤ 4 := by
    have hp : 0 ≤ (2 - L) * (2 + L) :=
      mul_nonneg (sub_nonneg.mpr hL2) (by nlinarith)
    nlinarith
  have hcub : L ^ 3 ≤ 8 := by
    have hm := mul_le_mul hL2 hsq (sq_nonneg L) (by norm_num : (0 : ℝ) ≤ 2)
    nlinarith
  have hsum : L ^ 3 + L ^ 2 + L + 1 ≤ 15 := by linarith
  have hfactor : L ^ 4 - 1 = (L - 1) * (L ^ 3 + L ^ 2 + L + 1) := by ring
  have hprod : (L - 1) * (L ^ 3 + L ^ 2 + L + 1) ≤ 15 * (L - 1) :=
    by simpa [mul_comm] using
      mul_le_mul_of_nonneg_left hsum (sub_nonneg.mpr hL1)
  rw [hfactor] at hfourth
  nlinarith

theorem actualRadius_linear_separation {β L : ℝ} (hβ0 : 0 ≤ β)
    (hβ1 : β ≤ betaStar) (hL : 1 ≤ L)
    (hratio : qBranch β = L ^ 4 * qBranch (-β)) :
    (s - 1) * β / 5 ≤ L - 1 := by
  exact fourthSeparation_implies_linear hL (le_of_lt <|
    radiusRatio_lt_two hβ1 hL hratio)
    (radiusRatio_fourth_separation hβ0 hL hratio)

theorem companionChord_le_mirror_sub {β L M t : ℝ} (hβ : 0 ≤ β)
    (hM : M ≤ 1) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    companionChord β L M t ≤ mirrorChord β t -
      3 * s * β * (L - 1) * (2 - s) * t := by
  have hlast : 0 ≤ 3 * s * β * (1 - M) * t * (1 - t) := by
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg
          (mul_nonneg (mul_nonneg (by norm_num) (le_of_lt s_pos)) hβ)
            (sub_nonneg.mpr hM)) ht0)
      (sub_nonneg.mpr ht1)
  unfold companionChord mirrorChord branchChord baseChord nullSlope qBranch
  ring_nf at hlast ⊢
  nlinarith

theorem epsilon_sq_div_ten_le_hundredth {ε β : ℝ} (hε0 : 0 ≤ ε)
    (hεβ : ε ≤ β) (hβ1 : β ≤ betaStar) :
    ε ^ 2 / 10 ≤ (1 / 100 : ℝ) := by
  have hεq : ε < (1 / 4 : ℝ) :=
    hεβ.trans_lt (hβ1.trans_lt betaStar_lt_quarter)
  have hp : 0 ≤ (1 / 4 - ε) * (1 / 4 + ε) :=
    mul_nonneg (sub_nonneg.mpr (le_of_lt hεq)) (by nlinarith)
  nlinarith

theorem companionChord_large_t_margin {ε β L M t : ℝ}
    (hε0 : 0 ≤ ε) (hεβ : ε ≤ β) (hβ0 : 0 ≤ β)
    (hβ1 : β ≤ betaStar) (hL : 1 ≤ L) (hM : M ≤ 1)
    (hratio : qBranch β = L ^ 4 * qBranch (-β))
    (ht : 1 / 2 ≤ t) (ht1 : t ≤ 1) :
    companionChord β L M t ≤ -(ε ^ 2 / 10) := by
  have ht0 : 0 ≤ t := by linarith
  have hmirror := mirrorChord_nonpos hβ0 hβ1 ht0 ht1
  have hcompare : companionChord β L M t ≤ mirrorChord β t -
      3 * s * β * (L - 1) * (2 - s) * t :=
    companionChord_le_mirror_sub (L := L) hβ0 hM ht0 ht1
  have hsep := actualRadius_linear_separation hβ0 hβ1 hL hratio
  have htwo : 0 ≤ 2 - s := sub_nonneg.mpr (le_of_lt s_lt_two)
  have hs1 : 0 ≤ s - 1 := by nlinarith [s_gt_fifty_div_twentyNine]
  have hA : 0 ≤ 3 * s * β * (2 - s) :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (le_of_lt s_pos)) hβ0) htwo
  have hsepScaled :
      3 * s * β * (2 - s) * ((s - 1) * β / 5) ≤
        3 * s * β * (2 - s) * (L - 1) :=
    mul_le_mul_of_nonneg_left hsep hA
  have hleft0 : 0 ≤ 3 * s * β * (2 - s) * ((s - 1) * β / 5) := by
    exact mul_nonneg hA (div_nonneg (mul_nonneg hs1 hβ0) (by norm_num))
  have htScaled :
      3 * s * β * (2 - s) * ((s - 1) * β / 5) * (1 / 2) ≤
        3 * s * β * (2 - s) * (L - 1) * t := by
    calc
      3 * s * β * (2 - s) * ((s - 1) * β / 5) * (1 / 2)
          ≤ 3 * s * β * (2 - s) * ((s - 1) * β / 5) * t :=
        mul_le_mul_of_nonneg_left ht hleft0
      _ ≤ 3 * s * β * (2 - s) * (L - 1) * t :=
        mul_le_mul_of_nonneg_right hsepScaled ht0
  have hk := largeChord_constant
  have hβsq : ε ^ 2 ≤ β ^ 2 := by
    have hp : 0 ≤ (β - ε) * (β + ε) :=
      mul_nonneg (sub_nonneg.mpr hεβ) (by nlinarith)
    nlinarith
  have hmargin : ε ^ 2 / 10 ≤
      3 * s * β * (L - 1) * (2 - s) * t := by
    have hkβ : β ^ 2 / 10 ≤
        ((3 / 10) * s * (s - 1) * (2 - s)) * β ^ 2 :=
      by simpa [div_eq_mul_inv, mul_comm] using
        mul_le_mul_of_nonneg_right (le_of_lt hk) (sq_nonneg β)
    nlinarith [htScaled]
  nlinarith

/-- The actual companion chord has a quadratic uniform margin on every
truncated positive subbranch. -/
theorem companionChord_uniform_margin {ε β L M t : ℝ} (hε : 0 < ε)
    (hεβ : ε ≤ β) (hβ1 : β ≤ betaStar) (hL : 1 ≤ L) (hM : M ≤ 1)
    (hratio : qBranch β = L ^ 4 * qBranch (-β))
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    companionChord β L M t ≤ -(ε ^ 2 / 10) := by
  have hβ0 : 0 ≤ β := le_trans (le_of_lt hε) hεβ
  by_cases ht : t ≤ 1 / 2
  · have hsmall := (companionChord_le_mirror hβ0 hL hM ht0 ht1).trans
        (mirrorChord_small_t_margin hβ0 hβ1 ht0 ht)
    have hεsmall := epsilon_sq_div_ten_le_hundredth (le_of_lt hε) hεβ hβ1
    linarith
  · exact companionChord_large_t_margin (le_of_lt hε) hεβ hβ0 hβ1 hL hM
      hratio (le_of_not_ge ht) ht1

theorem mirrorRay_uniform_margin {β y : ℝ} (hβ0 : 0 ≤ β)
    (hβ1 : β ≤ betaStar) (hy : 1 ≤ y) :
    mirrorRay β y ≤ -(1 / 100 : ℝ) := by
  have hy0 : 0 ≤ y := by linarith
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
  have hnonneg : 0 ≤ y ^ 6 - 1 := by nlinarith [hgrowth, hdiff]
  have hweighted : y ^ 2 - 1 ≤ 2 * qBranch (-β) * (y ^ 6 - 1) := by
    have hthird : y ^ 2 - 1 ≤ (1 / 3 : ℝ) * (y ^ 6 - 1) := by nlinarith
    have hcoef : (1 / 3 : ℝ) ≤ 2 * qBranch (-β) := by nlinarith
    have hscale := mul_le_mul_of_nonneg_right hcoef hnonneg
    linarith
  have hK : 0 ≤ 3 * s * β * (2 - s) := by
    have htwo : 0 ≤ 2 - s := sub_nonneg.mpr (le_of_lt s_lt_two)
    exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (le_of_lt s_pos)) hβ0) htwo
  have hKdrop : -3 * s * β * (2 - s) * (y - 1) ≤ 0 := by
    nlinarith [mul_nonneg hK (sub_nonneg.mpr hy)]
  have hstartFactor := branchRay_start_factor (-β)
  have hcoef : 0 ≤ (-86 / 9 + 17 * s / 3 : ℝ) := by
    nlinarith [s_gt_fifty_div_twentyNine]
  have hstart :
      3 * s * (-β) * (2 - s) + 1 - 2 * qBranch (-β) ≤ -(1 / 100 : ℝ) := by
    rw [hstartFactor]
    have hray := rayMargin_constant
    nlinarith [mul_nonneg hcoef hβ0]
  unfold mirrorRay branchRay
  nlinarith

theorem companionRay_uniform_margin {ε β L y : ℝ} (hε : 0 < ε)
    (hεβ : ε ≤ β) (hβ1 : β ≤ betaStar) (hL : 1 ≤ L) (hy : 1 ≤ y) :
    companionRay β L y ≤ -(ε ^ 2 / 10) := by
  have hβ0 : 0 ≤ β := le_trans (le_of_lt hε) hεβ
  have hy0 : 0 ≤ y := by linarith
  have hactual := (companionRay_le_mirror hβ0 hL hy0).trans
    (mirrorRay_uniform_margin hβ0 hβ1 hy)
  have hεsmall := epsilon_sq_div_ten_le_hundredth (le_of_lt hε) hεβ hβ1
  linarith

/-- A pointwise error of half the certified margin preserves strict
negativity.  This is the final consumer used for coefficient tubes. -/
theorem uniformMargin_absorb_error {ε value error : ℝ} (hε : 0 < ε)
    (hvalue : value ≤ -(ε ^ 2 / 10)) (herror : |error| ≤ ε ^ 2 / 20) :
    value + error < 0 := by
  have herr : error ≤ ε ^ 2 / 20 := (le_abs_self error).trans herror
  have hsq : 0 < ε ^ 2 := sq_pos_of_pos hε
  nlinarith

end

end ErdosProblems.Erdos1041.SexticNullBranchUniformMargin
