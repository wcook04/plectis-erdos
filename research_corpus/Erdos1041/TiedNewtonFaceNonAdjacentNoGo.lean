import ErdosProblems.Erdos1041.TiedNewtonFaceRationalHubRescue
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

/-!
# Erdős #1041: exact nonadjacent tied-face chart

This module checks the finite algebraic kernel for
`Q(z)=-(65/27)z+(100/27)z²-z⁵`.  The ordinary proof owns the harmonic
component count and the identification of its five asymptotic sectors.
-/

namespace ErdosProblems.Erdos1041.TiedNewtonFaceNonAdjacentNoGo

noncomputable section

open ErdosProblems.Erdos1041.TiedNewtonFaceRationalHubRescue

def q (z : ℂ) : ℂ := -(65 / 27) * z + (100 / 27) * z ^ 2 - z ^ 5
def qDeriv (z : ℂ) : ℂ := -(65 / 27) + (200 / 27) * z - 5 * z ^ 4

theorem derivative_factorization (z : ℂ) :
    qDeriv z = -5 * (z - 1) * (z - 1 / 3) *
      (z + 2 / 3 - Complex.I) * (z + 2 / 3 + Complex.I) := by
  dsimp [qDeriv]
  ring_nf
  norm_num [Complex.I_sq]
  ring

def modelRe (x y : ℝ) : ℝ :=
  -(65 / 27) * x + (100 / 27) * (x ^ 2 - y ^ 2) -
    (x ^ 5 - 10 * x ^ 3 * y ^ 2 + 5 * x * y ^ 4)

theorem critical_heights :
    modelRe 1 0 = 8 / 27 ∧
    modelRe (1 / 3) 0 = -(32 / 81) ∧
    modelRe (-(2 / 3)) 1 = 4 / 81 ∧
    modelRe (-(2 / 3)) (-1) = 4 / 81 := by
  norm_num [modelRe]

def hubX : ℝ := 1 / 3
def radius : ℝ := 1 / 2
def uX : ℝ := 5 / 13
def uY : ℝ := 12 / 13
def vX : ℝ := 5 / 13
def vY : ℝ := -(12 / 13)

theorem u_unit : uX ^ 2 + uY ^ 2 = 1 := by norm_num [uX, uY]
theorem v_unit : vX ^ 2 + vY ^ 2 = 1 := by norm_num [vX, vY]

theorem direction_fifth_real :
    uX ^ 5 - 10 * uX ^ 3 * uY ^ 2 + 5 * uX * uY ^ 4 =
      341525 / 371293 ∧
    vX ^ 5 - 10 * vX ^ 3 * vY ^ 2 + 5 * vX * vY ^ 4 =
      341525 / 371293 := by
  norm_num [uX, uY, vX, vY]

def armU (t : ℝ) : ℝ :=
  modelRe ((1-t)*hubX+t*(radius*uX)) (t*(radius*uY))
def armV (t : ℝ) : ℝ :=
  modelRe ((1-t)*hubX+t*(radius*vX)) (t*(radius*vY))

def tailRecipU (s : ℝ) : ℝ :=
  -(radius^5) * (uX^5-10*uX^3*uY^2+5*uX*uY^4) +
    (100/27)*radius^2*(uX^2-uY^2)*s^3 -
    (65/27)*radius*uX*s^4
def tailRecipV (s : ℝ) : ℝ :=
  -(radius^5) * (vX^5-10*vX^3*vY^2+5*vX*vY^4) +
    (100/27)*radius^2*(vX^2-vY^2)*s^3 -
    (65/27)*radius*vX*s^4

def tailU (T : ℝ) : ℝ := modelRe (T*uX) (T*uY)
def tailV (T : ℝ) : ℝ := modelRe (T*vX) (T*vY)

theorem armU_bernstein (t : ℝ) : armU t =
    (-32/81)*(1-t)^5 +
    5*(-32/81)*t*(1-t)^4 +
    10*(-25157/54756)*t^2*(1-t)^3 +
    10*(-2553583/4270968)*t^3*(1-t)^2 +
    5*(-3400915/4112784)*t^4*(1-t) +
    (-366892775/320797152)*t^5 := by
  dsimp [armU, modelRe, hubX, radius, uX, uY]
  ring

theorem armV_eq_armU (t : ℝ) : armV t = armU t := by
  dsimp [armV, armU, modelRe, hubX, radius, uX, uY, vX, vY]
  ring

theorem tailRecipU_bernstein (s : ℝ) : tailRecipU s =
    (-341525/11881376)*(1-s)^5 +
    5*(-341525/11881376)*s*(1-s)^4 +
    10*(-341525/11881376)*s^2*(1-s)^3 +
    10*(-30136615/320797152)*s^3*(1-s)^2 +
    5*(-40862125/106932384)*s^4*(1-s) +
    (-366892775/320797152)*s^5 := by
  dsimp [tailRecipU, radius, uX, uY]
  ring

theorem tailRecipV_eq_tailRecipU (s : ℝ) : tailRecipV s = tailRecipU s := by
  dsimp [tailRecipV, tailRecipU, radius, uX, uY, vX, vY]
  ring

theorem armU_nonpos {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) : armU t ≤ 0 := by
  rw [armU_bernstein]
  exact bernsteinQuintic_nonpos h0 h1 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem armV_nonpos {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) : armV t ≤ 0 := by
  rw [armV_eq_armU]
  exact armU_nonpos h0 h1

theorem tailRecipU_nonpos {s : ℝ} (h0 : 0 ≤ s) (h1 : s ≤ 1) :
    tailRecipU s ≤ 0 := by
  rw [tailRecipU_bernstein]
  exact bernsteinQuintic_nonpos h0 h1 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem tailRecipV_nonpos {s : ℝ} (h0 : 0 ≤ s) (h1 : s ≤ 1) :
    tailRecipV s ≤ 0 := by
  rw [tailRecipV_eq_tailRecipU]
  exact tailRecipU_nonpos h0 h1

theorem tailU_reciprocal_identity {T : ℝ} (hT : T ≠ 0) :
    (radius/T)^5 * tailU T = tailRecipU (radius/T) := by
  dsimp [tailU, tailRecipU, modelRe, radius, uX, uY]
  field_simp [hT]
  ring

theorem tailV_reciprocal_identity {T : ℝ} (hT : T ≠ 0) :
    (radius/T)^5 * tailV T = tailRecipV (radius/T) := by
  dsimp [tailV, tailRecipV, modelRe, radius, vX, vY]
  field_simp [hT]
  ring

theorem tailU_nonpos {T : ℝ} (hT : radius ≤ T) : tailU T ≤ 0 := by
  have hR : 0 < radius := by norm_num [radius]
  have hTp : 0 < T := lt_of_lt_of_le hR hT
  have hs0 : 0 ≤ radius/T := le_of_lt (div_pos hR hTp)
  have hs1 : radius/T ≤ 1 := (div_le_one hTp).mpr hT
  have hp := tailRecipU_nonpos hs0 hs1
  rw [← tailU_reciprocal_identity (ne_of_gt hTp)] at hp
  by_contra hn
  have htail : 0 < tailU T := lt_of_not_ge hn
  have hfac : 0 < (radius/T)^5 := by positivity
  nlinarith [mul_pos hfac htail]

theorem tailV_nonpos {T : ℝ} (hT : radius ≤ T) : tailV T ≤ 0 := by
  have hR : 0 < radius := by norm_num [radius]
  have hTp : 0 < T := lt_of_lt_of_le hR hT
  have hs0 : 0 ≤ radius/T := le_of_lt (div_pos hR hTp)
  have hs1 : radius/T ≤ 1 := (div_le_one hTp).mpr hT
  have hp := tailRecipV_nonpos hs0 hs1
  rw [← tailV_reciprocal_identity (ne_of_gt hTp)] at hp
  by_contra hn
  have htail : 0 < tailV T := lt_of_not_ge hn
  have hfac : 0 < (radius/T)^5 := by positivity
  nlinarith [mul_pos hfac htail]

def distSq : ℝ := (radius*uX-hubX)^2 + (radius*uY)^2

theorem distSq_value : distSq = 1417/6084 := by
  norm_num [distSq, radius, uX, uY, hubX]

theorem squared_metric_margin : radius^2 - distSq = 2/117 := by
  norm_num [distSq, radius, uX, uY, hubX]

/-- By conjugate symmetry the connector length is `2*sqrt(distSq)`, strictly
less than `2R`. -/
theorem connector_length_lt_two_mul_radius :
    2 * Real.sqrt distSq < 2 * radius := by
  have hdist0 : 0 ≤ distSq := by
    dsimp [distSq]
    positivity
  have hsqrt : Real.sqrt distSq < radius := by
    rw [Real.sqrt_lt' (by norm_num [radius]), distSq_value]
    norm_num [radius]
  linarith

/-! ## Quantitative open coefficient chart

The symbolic checker identifies the perturbed Bernstein controls as affine
functions of the four real coefficient perturbations.  The theorem below
checks the load-bearing box domination.  The displayed expressions are the
numerators of the nonconstant controls; their denominators are positive.
-/

def InOpenChartBox (da ea db eb : ℝ) : Prop :=
  |da| ≤ 2 / 3 ∧ |ea| ≤ 2 / 3 ∧ |db| ≤ 2 / 3 ∧ |eb| ≤ 2 / 3

theorem open_chart_control_numerators_strict
    {da ea db eb : ℝ} (hbox : InOpenChartBox da ea db eb) :
    27*da + 9*db - 32 < 0 ∧
    3213*da + 972*db - 972*ea - 648*eb - 4160 < 0 ∧
    151632*da + 29673*db - 101088*ea - 60264*eb - 251570 < 0 ∧
    5311332*da - 69147*db - 5913648*ea - 3108456*eb - 12767915 < 0 ∧
    4534608*da - 1644708*db - 7592832*ea - 3455712*eb - 17004575 < 0 ∧
    61691760*da - 56471688*db - 148060224*ea - 56946240*eb - 366892775 < 0 ∧
    3213*da + 972*db + 972*ea + 648*eb - 4160 < 0 ∧
    151632*da + 29673*db + 101088*ea + 60264*eb - 251570 < 0 ∧
    5311332*da - 69147*db + 5913648*ea + 3108456*eb - 12767915 < 0 ∧
    4534608*da - 1644708*db + 7592832*ea + 3455712*eb - 17004575 < 0 ∧
    61691760*da - 56471688*db + 148060224*ea + 56946240*eb - 366892775 < 0 ∧
    -(28235844*db + 28473120*eb + 150683075) < 0 ∧
    20563920*da - 37647792*db - 49353408*ea - 37964160*eb - 204310625 < 0 ∧
    -(28235844*db - 28473120*eb + 150683075) < 0 ∧
    20563920*da - 37647792*db + 49353408*ea + 37964160*eb - 204310625 < 0 := by
  rcases hbox with ⟨hda, hea, hdb, heb⟩
  rw [abs_le] at hda hea hdb heb
  rcases hda with ⟨hdaL, hdaU⟩
  rcases hea with ⟨heaL, heaU⟩
  rcases hdb with ⟨hdbL, hdbU⟩
  rcases heb with ⟨hebL, hebU⟩
  norm_num at hdaL hdaU heaL heaU hdbL hdbU hebL hebU
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  · linarith

end

end ErdosProblems.Erdos1041.TiedNewtonFaceNonAdjacentNoGo
