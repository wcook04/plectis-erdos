import Mathlib.Tactic

/-!
# Erdős #1041: an exact rational rescue of the minimum-real-selector no-go

For `Q(z)=-(379/256)z+3z^2-z^5`, the companion no-go proves that the unique
minimum-real critical hub cannot support adjacent arms and tails.  This module
checks a different, completely rational connector.  All arm and reciprocal-tail
Bernstein controls are strictly negative, and its central length is below the
budget `2R=3`.
-/

namespace ErdosProblems.Erdos1041.TiedNewtonFaceRationalHubRescue

noncomputable section

def modelRe (x y : ℝ) : ℝ :=
  -(379 / 256) * x + 3 * (x ^ 2 - y ^ 2) -
    (x ^ 5 - 10 * x ^ 3 * y ^ 2 + 5 * x * y ^ 4)

def hubX : ℝ := -(3 / 5)
def hubY : ℝ := 9 / 10
def radius : ℝ := 3 / 2
def uX : ℝ := 57 / 185
def uY : ℝ := 176 / 185
def vX : ℝ := -(1431 / 1769)
def vY : ℝ := 1040 / 1769

theorem u_unit : uX ^ 2 + uY ^ 2 = 1 := by norm_num [uX, uY]
theorem v_unit : vX ^ 2 + vY ^ 2 = 1 := by norm_num [vX, vY]

def armU (t : ℝ) : ℝ :=
  modelRe ((1-t)*hubX+t*(radius*uX)) ((1-t)*hubY+t*(radius*uY))
def armV (t : ℝ) : ℝ :=
  modelRe ((1-t)*hubX+t*(radius*vX)) ((1-t)*hubY+t*(radius*vY))

/-- `s^5 Q(Rw/s)` written without division. -/
def tailRecipU (s : ℝ) : ℝ :=
  -(radius^5) * (uX^5-10*uX^3*uY^2+5*uX*uY^4) +
    3*radius^2*(uX^2-uY^2)*s^3 - (379/256)*radius*uX*s^4
def tailRecipV (s : ℝ) : ℝ :=
  -(radius^5) * (vX^5-10*vX^3*vY^2+5*vX*vY^4) +
    3*radius^2*(vX^2-vY^2)*s^3 - (379/256)*radius*vX*s^4

def tailU (T : ℝ) : ℝ := modelRe (T*uX) (T*uY)
def tailV (T : ℝ) : ℝ := modelRe (T*vX) (T*vY)

/-- A degree-five polynomial with nonpositive Bernstein controls is
nonpositive on the unit interval. -/
theorem bernsteinQuintic_nonpos
    {t b0 b1 b2 b3 b4 b5 : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (h0 : b0 ≤ 0) (h1 : b1 ≤ 0) (h2 : b2 ≤ 0)
    (h3 : b3 ≤ 0) (h4 : b4 ≤ 0) (h5 : b5 ≤ 0) :
    b0*(1-t)^5 + 5*b1*t*(1-t)^4 + 10*b2*t^2*(1-t)^3 +
      10*b3*t^3*(1-t)^2 + 5*b4*t^4*(1-t) + b5*t^5 ≤ 0 := by
  have hnt : 0 ≤ 1-t := by linarith
  have hB0 : 0 ≤ (1-t)^5 := by positivity
  have hB1 : 0 ≤ 5*t*(1-t)^4 := by positivity
  have hB2 : 0 ≤ 10*t^2*(1-t)^3 := by positivity
  have hB3 : 0 ≤ 10*t^3*(1-t)^2 := by positivity
  have hB4 : 0 ≤ 5*t^4*(1-t) := by positivity
  have hB5 : 0 ≤ t^5 := by positivity
  have := mul_nonpos_of_nonpos_of_nonneg h0 hB0
  have := mul_nonpos_of_nonpos_of_nonneg h1 hB1
  have := mul_nonpos_of_nonpos_of_nonneg h2 hB2
  have := mul_nonpos_of_nonpos_of_nonneg h3 hB3
  have := mul_nonpos_of_nonpos_of_nonneg h4 hB4
  have := mul_nonpos_of_nonpos_of_nonneg h5 hB5
  nlinarith

theorem armU_bernstein (t : ℝ) : armU t =
    (-132207/800000)*(1-t)^5 +
    5*(-16434861/59200000)*t*(1-t)^4 +
    10*(-503256429/547600000)*t^2*(1-t)^3 +
    10*(-301233516771/81044800000)*t^3*(1-t)^2 +
    5*(-13348359283413/1499328800000)*t^4*(1-t) +
    (-1525158400631481/110950331200000)*t^5 := by
  dsimp [armU, modelRe, hubX, hubY, radius, uX, uY]
  ring

theorem armV_bernstein (t : ℝ) : armV t =
    (-132207/800000)*(1-t)^5 +
    5*(-74316957/566080000)*t*(1-t)^4 +
    10*(-22332225357/50069776000)*t^2*(1-t)^3 +
    10*(-84388858722579/70858746995200)*t^3*(1-t)^2 +
    5*(-29431513450668693/12534912343450880)*t^4*(1-t) +
    (-32936329163470829481/8869703974225842688)*t^5 := by
  dsimp [armV, modelRe, hubX, hubY, radius, vX, vY]
  ring

theorem tailRecipU_bernstein (s : ℝ) : tailRecipU s =
    (-52657466386491/6934395700000)*(1-s)^5 +
    5*(-52657466386491/6934395700000)*s*(1-s)^4 +
    10*(-52657466386491/6934395700000)*s^2*(1-s)^3 +
    10*(-56449496860191/6934395700000)*s^3*(1-s)^2 +
    5*(-1100392225031781/110950331200000)*s^4*(1-s) +
    (-1525158400631481/110950331200000)*s^5 := by
  dsimp [tailRecipU, radius, uX, uY]
  ring

theorem tailRecipV_bernstein (s : ℝ) : tailRecipV s =
    (-4209643549210103307/554356498389115168)*(1-s)^5 +
    5*(-4209643549210103307/554356498389115168)*s*(1-s)^4 +
    10*(-4209643549210103307/554356498389115168)*s^2*(1-s)^3 +
    10*(-20470578414143643243/2771782491945575840)*s^3*(1-s)^2 +
    5*(-56773811538379499157/8869703974225842688)*s^4*(1-s) +
    (-32936329163470829481/8869703974225842688)*s^5 := by
  dsimp [tailRecipV, radius, vX, vY]
  ring

theorem armU_nonpos {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) : armU t ≤ 0 := by
  rw [armU_bernstein]
  exact bernsteinQuintic_nonpos h0 h1 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem armV_nonpos {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) : armV t ≤ 0 := by
  rw [armV_bernstein]
  exact bernsteinQuintic_nonpos h0 h1 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem tailRecipU_nonpos {s : ℝ} (h0 : 0 ≤ s) (h1 : s ≤ 1) :
    tailRecipU s ≤ 0 := by
  rw [tailRecipU_bernstein]
  exact bernsteinQuintic_nonpos h0 h1 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem tailRecipV_nonpos {s : ℝ} (h0 : 0 ≤ s) (h1 : s ≤ 1) :
    tailRecipV s ≤ 0 := by
  rw [tailRecipV_bernstein]
  exact bernsteinQuintic_nonpos h0 h1 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

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

def distUSq : ℝ := (radius*uX-hubX)^2 + (radius*uY-hubY)^2
def distVSq : ℝ := (radius*vX-hubX)^2 + (radius*vY-hubY)^2

theorem distUSq_value : distUSq = 2601/1850 := by
  norm_num [distUSq, radius, uX, uY, hubX, hubY]
theorem distVSq_value : distVSq = 33309/88450 := by
  norm_num [distVSq, radius, vX, vY, hubX, hubY]

/-- The central two-arm connector is strictly shorter than `2R=3`. -/
theorem connector_length_lt_two_mul_radius :
    Real.sqrt distUSq + Real.sqrt distVSq < 2*radius := by
  have hu0 : 0 ≤ distUSq := by
    dsimp [distUSq]
    positivity
  have hv0 : 0 ≤ distVSq := by
    dsimp [distVSq]
    positivity
  have husq : (Real.sqrt distUSq)^2 = distUSq := Real.sq_sqrt hu0
  have hvsq : (Real.sqrt distVSq)^2 = distVSq := Real.sq_sqrt hv0
  have hur : 0 ≤ Real.sqrt distUSq := Real.sqrt_nonneg _
  have hvr : 0 ≤ Real.sqrt distVSq := Real.sqrt_nonneg _
  rw [distUSq_value] at husq
  rw [distVSq_value] at hvsq
  dsimp [radius]
  have hu : Real.sqrt distUSq < 3/2 := by
    rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < 3/2), distUSq_value]
    norm_num
  have hv : Real.sqrt distVSq < 3/2 := by
    rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < 3/2), distVSq_value]
    norm_num
  linarith

end

end ErdosProblems.Erdos1041.TiedNewtonFaceRationalHubRescue
