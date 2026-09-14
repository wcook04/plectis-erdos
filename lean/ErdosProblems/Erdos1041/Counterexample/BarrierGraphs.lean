import ErdosProblems.Erdos1041.Counterexample.BarrierCertificates
/-! External source: ani, erdosproblems.com forum thread 1041, 7 Sept 2026.
Explicit separating barriers replacing the Riemann-Hurwitz step of Lemma 2.1, at `s = 10⁻⁶`. -/

noncomputable section
namespace Erdos1041.Counterexample.S7Proof

set_option maxRecDepth 10000
set_option maxHeartbeats 8000000

def l1_01 (x : ℝ) : ℝ := (955 / 3962) * x + (-31775 / 7924)
def l1_12 (x : ℝ) : ℝ := (-539296338829 / 44668564793666) * x + (4076722807313861 / 446685647936660)
def l1_23 (x : ℝ) : ℝ := (-1220013986006 / 25180573091109) * x + (47287422848540256709986673 / 5036114618221800000000000)
def l1_34 (x : ℝ) : ℝ := (-7548137935033 / 41210172423045) * x + (287305378858768 / 41210172423045)
def l2_01 (x : ℝ) : ℝ := (160740689651709 / 206050862085905) * x + (180400000748660 / 41210172417181)
def l2_12 (x : ℝ) : ℝ := (-578879533802 / 7002250177415) * x + (22984875809240463303357391 / 1400450035483000000000000)
def l2_23 (x : ℝ) : ℝ := (-167425171516501 / 215940137204435) * x + (288227186805049 / 43188027440887)

def phi1 (x : ℝ) : ℝ :=
  max (-(3 / 14 : ℝ) * x)
    (max (l1_34 x) (max (l1_23 x) (max (l1_12 x) (min (l1_01 x) ((9 / 40 : ℝ) * x)))))

def phi2 (x : ℝ) : ℝ :=
  max (-(37 / 46 : ℝ) * x)
    (max (l2_23 x) (max (l2_12 x) (max (l2_01 x) ((4 / 5 : ℝ) * x))))

theorem continuous_phi1 : Continuous phi1 := by
  unfold phi1 l1_01 l1_12 l1_23 l1_34
  fun_prop

theorem continuous_phi2 : Continuous phi2 := by
  unfold phi2 l2_01 l2_12 l2_23
  fun_prop

def G1 (z : ℂ) : ℝ := eta z - phi1 (xi z)
def G2 (z : ℂ) : ℝ := -eta z - phi2 (xi z)

theorem continuous_G1 : Continuous G1 :=
  continuous_eta.sub (continuous_phi1.comp continuous_xi)

theorem continuous_G2 : Continuous G2 :=
  continuous_eta.neg.sub (continuous_phi2.comp continuous_xi)

theorem affine_le_abs (m b L C x : ℝ)
    (hm0 : -L ≤ m) (hm1 : m ≤ L) (hb : b ≤ C) :
    m * x + b ≤ L * |x| + C := by
  rcases le_total 0 x with hx | hx
  · rw [abs_of_nonneg hx]
    have h := mul_le_mul_of_nonneg_right hm1 hx
    nlinarith
  · rw [abs_of_nonpos hx]
    have h := mul_le_mul_of_nonpos_right hm0 hx
    nlinarith

theorem l1_01_upper (x : ℝ) : l1_01 x ≤ (1 / 4) * |x| + 12 := by
  unfold l1_01
  apply affine_le_abs <;> norm_num

theorem l1_12_upper (x : ℝ) : l1_12 x ≤ (1 / 4) * |x| + 12 := by
  unfold l1_12
  apply affine_le_abs <;> norm_num

theorem l1_23_upper (x : ℝ) : l1_23 x ≤ (1 / 4) * |x| + 12 := by
  unfold l1_23
  apply affine_le_abs <;> norm_num

theorem l1_34_upper (x : ℝ) : l1_34 x ≤ (1 / 4) * |x| + 12 := by
  unfold l1_34
  apply affine_le_abs <;> norm_num

theorem l2_01_upper (x : ℝ) : l2_01 x ≤ 1 * |x| + 18 := by
  unfold l2_01
  apply affine_le_abs <;> norm_num

theorem l2_12_upper (x : ℝ) : l2_12 x ≤ 1 * |x| + 18 := by
  unfold l2_12
  apply affine_le_abs <;> norm_num

theorem l2_23_upper (x : ℝ) : l2_23 x ≤ 1 * |x| + 18 := by
  unfold l2_23
  apply affine_le_abs <;> norm_num

theorem phi1_upper (x : ℝ) : phi1 x ≤ (1 / 4 : ℝ) * |x| + 12 := by
  unfold phi1
  refine max_le ?_ (max_le (l1_34_upper x)
    (max_le (l1_23_upper x) (max_le (l1_12_upper x) ?_)))
  · simpa using (affine_le_abs (-(3 / 14)) 0 (1 / 4) 12 x
      (by norm_num) (by norm_num) (by norm_num))
  · exact (min_le_left _ _).trans (l1_01_upper x)

theorem phi2_upper (x : ℝ) : phi2 x ≤ |x| + 18 := by
  unfold phi2
  refine max_le ?_ (max_le (by simpa using l2_23_upper x)
    (max_le (by simpa using l2_12_upper x) (max_le (by simpa using l2_01_upper x) ?_)))
  · simpa using (affine_le_abs (-(37 / 46)) 0 1 18 x
      (by norm_num) (by norm_num) (by norm_num))
  · simpa using (affine_le_abs (4 / 5) 0 1 18 x
      (by norm_num) (by norm_num) (by norm_num))

theorem phi1_region_0 (x : ℝ) (hlo : 250 ≤ x) :
    phi1 x = (9 / 40) * x := by
  unfold phi1 l1_01 l1_12 l1_23 l1_34
  simp only [max_def, min_def]
  split_ifs <;> linarith

theorem phi1_region_1 (x : ℝ) (hlo : (519 / 10) ≤ x) (hhi : x ≤ 250) :
    phi1 x = l1_01 x := by
  unfold phi1 l1_01 l1_12 l1_23 l1_34
  simp only [max_def, min_def]
  split_ifs <;> linarith

theorem phi1_region_2 (x : ℝ) (hlo : (3615717603167 / 500000000000) ≤ x) (hhi : x ≤ (519 / 10)) :
    phi1 x = l1_12 x := by
  unfold phi1 l1_01 l1_12 l1_23 l1_34
  simp only [max_def, min_def]
  split_ifs <;> linarith

theorem phi1_region_3 (x : ℝ) (hlo : (-717965515391 / 40000000000) ≤ x) (hhi : x ≤ (3615717603167 / 500000000000)) :
    phi1 x = l1_23 x := by
  unfold phi1 l1_01 l1_12 l1_23 l1_34
  simp only [max_def, min_def]
  split_ifs <;> linarith

theorem phi1_region_4 (x : ℝ) (hlo : (-224) ≤ x) (hhi : x ≤ (-717965515391 / 40000000000)) :
    phi1 x = l1_34 x := by
  unfold phi1 l1_01 l1_12 l1_23 l1_34
  simp only [max_def, min_def]
  split_ifs <;> linarith

theorem phi1_region_5 (x : ℝ) (hhi : x ≤ (-224)) :
    phi1 x = (-3 / 14) * x := by
  unfold phi1 l1_01 l1_12 l1_23 l1_34
  simp only [max_def, min_def]
  split_ifs <;> linarith

theorem phi2_region_0 (x : ℝ) (hlo : 220 ≤ x) :
    phi2 x = (4 / 5) * x := by
  unfold phi2 l2_01 l2_12 l2_23
  simp only [max_def, min_def]
  split_ifs <;> linarith

theorem phi2_region_1 (x : ℝ) (hlo : (2789827582819 / 200000000000) ≤ x) (hhi : x ≤ 220) :
    phi2 x = l2_01 x := by
  unfold phi2 l2_01 l2_12 l2_23
  simp only [max_def, min_def]
  split_ifs <;> linarith

theorem phi2_region_2 (x : ℝ) (hlo : (-2811972559113 / 200000000000) ≤ x) (hhi : x ≤ (2789827582819 / 200000000000)) :
    phi2 x = l2_12 x := by
  unfold phi2 l2_01 l2_12 l2_23
  simp only [max_def, min_def]
  split_ifs <;> linarith

theorem phi2_region_3 (x : ℝ) (hlo : (-230) ≤ x) (hhi : x ≤ (-2811972559113 / 200000000000)) :
    phi2 x = l2_23 x := by
  unfold phi2 l2_01 l2_12 l2_23
  simp only [max_def, min_def]
  split_ifs <;> linarith

theorem phi2_region_4 (x : ℝ) (hhi : x ≤ (-230)) :
    phi2 x = (-37 / 46) * x := by
  unfold phi2 l2_01 l2_12 l2_23
  simp only [max_def, min_def]
  split_ifs <;> linarith

def Hcoord (x e : ℝ) : ℝ :=
  Hpoly ((-5 * x + 4 * e) / 41) ((4 * x + 5 * e) / 41)

theorem graph1_nonpos (x : ℝ) : Hcoord x (phi1 x) ≤ 0 := by
  by_cases h0 : 250 ≤ x
  ·
    rw [phi1_region_0 x h0]
    have hr : 0 ≤ (x / 40 - (25 / 4)) := by linarith
    have hx : (-5 * x + 4 * (((9 / 40) * x))) / 41 = (-25) + ((-29) - (-25)) * (x / 40 - (25 / 4)) := by ring
    have hy : (4 * x + 5 * (((9 / 40) * x))) / 41 = (125 / 4) + ((145 / 4) - (125 / 4)) * (x / 40 - (25 / 4)) := by ring
    unfold Hcoord
    rw [hx, hy]
    exact cert_tail_A (x / 40 - (25 / 4)) hr
  ·
    by_cases h1 : (519 / 10) ≤ x
    ·
      have hxhi : x ≤ 250 := by linarith
      rw [phi1_region_1 x h1 hxhi]
      unfold l1_01
      have hr0 : 0 ≤ ((250 - x) / (1981 / 10)) := by norm_num; linarith
      have hr1 : ((250 - x) / (1981 / 10)) ≤ 1 := by norm_num; linarith
      have hx : (-5 * x + 4 * (((955 / 3962) * x + (-31775 / 7924)))) / 41 = (-25) + ((-11 / 2) - (-25)) * ((250 - x) / (1981 / 10)) := by ring
      have hy : (4 * x + 5 * (((955 / 3962) * x + (-31775 / 7924)))) / 41 = (125 / 4) + ((61 / 10) - (125 / 4)) * ((250 - x) / (1981 / 10)) := by ring
      unfold Hcoord
      rw [hx, hy]
      exact segment_g1_01 ((250 - x) / (1981 / 10)) hr0 hr1
    ·
      by_cases h2 : (3615717603167 / 500000000000) ≤ x
      ·
        have hxhi : x ≤ (519 / 10) := by linarith
        rw [phi1_region_2 x h2 hxhi]
        unfold l1_12
        have hr0 : 0 ≤ (((519 / 10) - x) / (22334282396833 / 500000000000)) := by norm_num; linarith
        have hr1 : (((519 / 10) - x) / (22334282396833 / 500000000000)) ≤ 1 := by norm_num; linarith
        have hx : (-5 * x + 4 * (((-539296338829 / 44668564793666) * x + (4076722807313861 / 446685647936660)))) / 41 = (-11 / 2) + ((113703 / 500000000000) - (-11 / 2)) * (((519 / 10) - x) / (22334282396833 / 500000000000)) := by ring
        have hy : (4 * x + 5 * (((-539296338829 / 44668564793666) * x + (4076722807313861 / 446685647936660)))) / 41 = (61 / 10) + ((1807859085841 / 1000000000000) - (61 / 10)) * (((519 / 10) - x) / (22334282396833 / 500000000000)) := by ring
        unfold Hcoord
        rw [hx, hy]
        exact segment_g1_12 (((519 / 10) - x) / (22334282396833 / 500000000000)) hr0 hr1
      ·
        by_cases h3 : (-717965515391 / 40000000000) ≤ x
        ·
          have hxhi : x ≤ (3615717603167 / 500000000000) := by linarith
          rw [phi1_region_3 x h3 hxhi]
          unfold l1_23
          have hr0 : 0 ≤ (((3615717603167 / 500000000000) - x) / (25180573091109 / 1000000000000)) := by norm_num; linarith
          have hr1 : (((3615717603167 / 500000000000) - x) / (25180573091109 / 1000000000000)) ≤ 1 := by norm_num; linarith
          have hx : (-5 * x + 4 * (((-1220013986006 / 25180573091109) * x + (47287422848540256709986673 / 5036114618221800000000000)))) / 41 = (113703 / 500000000000) + ((637965515723 / 200000000000) - (113703 / 500000000000)) * (((3615717603167 / 500000000000) - x) / (25180573091109 / 1000000000000)) := by ring
          have hy : (4 * x + 5 * (((-1220013986006 / 25180573091109) * x + (47287422848540256709986673 / 5036114618221800000000000)))) / 41 = (1807859085841 / 1000000000000) + ((-19999999917 / 40000000000) - (1807859085841 / 1000000000000)) * (((3615717603167 / 500000000000) - x) / (25180573091109 / 1000000000000)) := by ring
          unfold Hcoord
          rw [hx, hy]
          exact segment_g1_23 (((3615717603167 / 500000000000) - x) / (25180573091109 / 1000000000000)) hr0 hr1
        ·
          by_cases h4 : (-224) ≤ x
          ·
            have hxhi : x ≤ (-717965515391 / 40000000000) := by linarith
            rw [phi1_region_4 x h4 hxhi]
            unfold l1_34
            have hr0 : 0 ≤ (((-717965515391 / 40000000000) - x) / (8242034484609 / 40000000000)) := by norm_num; linarith
            have hr1 : (((-717965515391 / 40000000000) - x) / (8242034484609 / 40000000000)) ≤ 1 := by norm_num; linarith
            have hx : (-5 * x + 4 * (((-7548137935033 / 41210172423045) * x + (287305378858768 / 41210172423045)))) / 41 = (637965515723 / 200000000000) + (32 - (637965515723 / 200000000000)) * (((-717965515391 / 40000000000) - x) / (8242034484609 / 40000000000)) := by ring
            have hy : (4 * x + 5 * (((-7548137935033 / 41210172423045) * x + (287305378858768 / 41210172423045)))) / 41 = (-19999999917 / 40000000000) + ((-16) - (-19999999917 / 40000000000)) * (((-717965515391 / 40000000000) - x) / (8242034484609 / 40000000000)) := by ring
            unfold Hcoord
            rw [hx, hy]
            exact segment_g1_34 (((-717965515391 / 40000000000) - x) / (8242034484609 / 40000000000)) hr0 hr1
          ·
            have hxlo : x ≤ (-224) := by linarith
            rw [phi1_region_5 x hxlo]
            have hr : 0 ≤ (x / (-14) - 16) := by linarith
            have hx : (-5 * x + 4 * (((-3 / 14) * x))) / 41 = 32 + (34 - 32) * (x / (-14) - 16) := by ring
            have hy : (4 * x + 5 * (((-3 / 14) * x))) / 41 = (-16) + ((-17) - (-16)) * (x / (-14) - 16) := by ring
            unfold Hcoord
            rw [hx, hy]
            exact cert_tail_B (x / (-14) - 16) hr

theorem graph2_nonpos (x : ℝ) : Hcoord x (-phi2 x) ≤ 0 := by
  by_cases h0 : 220 ≤ x
  ·
    rw [phi2_region_0 x h0]
    have hr : 0 ≤ (x / 5 - 44) := by linarith
    have hx : (-5 * x + 4 * (-((4 / 5) * x))) / 41 = (-44) + ((-45) - (-44)) * (x / 5 - 44) := by ring
    have hy : (4 * x + 5 * (-((4 / 5) * x))) / 41 = 0 + (0 - 0) * (x / 5 - 44) := by ring
    unfold Hcoord
    rw [hx, hy]
    exact cert_tail_C (x / 5 - 44) hr
  ·
    by_cases h1 : (2789827582819 / 200000000000) ≤ x
    ·
      have hxhi : x ≤ 220 := by linarith
      rw [phi2_region_1 x h1 hxhi]
      unfold l2_01
      have hr0 : 0 ≤ ((220 - x) / (41210172417181 / 200000000000)) := by norm_num; linarith
      have hr1 : ((220 - x) / (41210172417181 / 200000000000)) ≤ 1 := by norm_num; linarith
      have hx : (-5 * x + 4 * (-((160740689651709 / 206050862085905) * x + (180400000748660 / 41210172417181)))) / 41 = (-44) + ((-3189827584479 / 1000000000000) - (-44)) * ((220 - x) / (41210172417181 / 200000000000)) := by ring
      have hy : (4 * x + 5 * (-((160740689651709 / 206050862085905) * x + (180400000748660 / 41210172417181)))) / 41 = 0 + ((-20000000083 / 40000000000) - 0) * ((220 - x) / (41210172417181 / 200000000000)) := by ring
      unfold Hcoord
      rw [hx, hy]
      exact segment_g2_01 ((220 - x) / (41210172417181 / 200000000000)) hr0 hr1
    ·
      by_cases h2 : (-2811972559113 / 200000000000) ≤ x
      ·
        have hxhi : x ≤ (2789827582819 / 200000000000) := by linarith
        rw [phi2_region_2 x h2 hxhi]
        unfold l2_12
        have hr0 : 0 ≤ (((2789827582819 / 200000000000) - x) / (1400450035483 / 50000000000)) := by norm_num; linarith
        have hr1 : (((2789827582819 / 200000000000) - x) / (1400450035483 / 50000000000)) ≤ 1 := by norm_num; linarith
        have hx : (-5 * x + 4 * (-((-578879533802 / 7002250177415) * x + (22984875809240463303357391 / 1400450035483000000000000)))) / 41 = (-3189827584479 / 1000000000000) + ((1069 / 1000000000000) - (-3189827584479 / 1000000000000)) * (((2789827582819 / 200000000000) - x) / (1400450035483 / 50000000000)) := by ring
        have hy : (4 * x + 5 * (-((-578879533802 / 7002250177415) * x + (22984875809240463303357391 / 1400450035483000000000000)))) / 41 = (-20000000083 / 40000000000) + ((-702993139511 / 200000000000) - (-20000000083 / 40000000000)) * (((2789827582819 / 200000000000) - x) / (1400450035483 / 50000000000)) := by ring
        unfold Hcoord
        rw [hx, hy]
        exact segment_g2_12 (((2789827582819 / 200000000000) - x) / (1400450035483 / 50000000000)) hr0 hr1
      ·
        by_cases h3 : (-230) ≤ x
        ·
          have hxhi : x ≤ (-2811972559113 / 200000000000) := by linarith
          rw [phi2_region_3 x h3 hxhi]
          unfold l2_23
          have hr0 : 0 ≤ (((-2811972559113 / 200000000000) - x) / (43188027440887 / 200000000000)) := by norm_num; linarith
          have hr1 : (((-2811972559113 / 200000000000) - x) / (43188027440887 / 200000000000)) ≤ 1 := by norm_num; linarith
          have hx : (-5 * x + 4 * (-((-167425171516501 / 215940137204435) * x + (288227186805049 / 43188027440887)))) / 41 = (1069 / 1000000000000) + (10 - (1069 / 1000000000000)) * (((-2811972559113 / 200000000000) - x) / (43188027440887 / 200000000000)) := by ring
          have hy : (4 * x + 5 * (-((-167425171516501 / 215940137204435) * x + (288227186805049 / 43188027440887)))) / 41 = (-702993139511 / 200000000000) + ((-45) - (-702993139511 / 200000000000)) * (((-2811972559113 / 200000000000) - x) / (43188027440887 / 200000000000)) := by ring
          unfold Hcoord
          rw [hx, hy]
          exact segment_g2_23 (((-2811972559113 / 200000000000) - x) / (43188027440887 / 200000000000)) hr0 hr1
        ·
          have hxlo : x ≤ (-230) := by linarith
          rw [phi2_region_4 x hxlo]
          have hr : 0 ≤ (x / (-46) - 5) := by linarith
          have hx : (-5 * x + 4 * (-((-37 / 46) * x))) / 41 = 10 + (12 - 10) * (x / (-46) - 5) := by ring
          have hy : (4 * x + 5 * (-((-37 / 46) * x))) / 41 = (-45) + ((-54) - (-45)) * (x / (-46) - 5) := by ring
          unfold Hcoord
          rw [hx, hy]
          exact cert_tail_D (x / (-46) - 5) hr

theorem G1_zero_norm (w : ℂ) (hw : G1 w = 0) :
    1 ≤ ‖f.eval ((ρ : ℂ) * (ε : ℂ) * w)‖ := by
  have he : eta w = phi1 (xi w) := sub_eq_zero.mp hw
  apply norm_ge_one_of_Hpoly
  have h := graph1_nonpos (xi w)
  unfold Hcoord at h
  rw [← he, ← re_from_coordinates w, ← im_from_coordinates w] at h
  exact h

theorem G2_zero_norm (w : ℂ) (hw : G2 w = 0) :
    1 ≤ ‖f.eval ((ρ : ℂ) * (ε : ℂ) * w)‖ := by
  have he : eta w = -phi2 (xi w) := by unfold G2 at hw; linarith
  apply norm_ge_one_of_Hpoly
  have h := graph2_nonpos (xi w)
  unfold Hcoord at h
  rw [← he, ← re_from_coordinates w, ← im_from_coordinates w] at h
  exact h

end Erdos1041.Counterexample.S7Proof
