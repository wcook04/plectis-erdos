import ErdosProblems.Erdos1041.TiedNewtonFaceRationalHubRescue
import Mathlib.Tactic

/-!
# Erdős #1041: rational rescue of a positive leftmost fibre

The model is `Q(z)=15z+5z²-z⁵`.  Its canonical leftmost horizontal fibre
has positive defect, but this file checks a strict rational noncritical-hub
connector.
-/

namespace ErdosProblems.Erdos1041.TiedNewtonFacePositiveFibreRationalRescue

noncomputable section

open ErdosProblems.Erdos1041.TiedNewtonFaceRationalHubRescue

def modelRe (x y : ℝ) : ℝ :=
  15*x + 5*(x^2-y^2) - (x^5-10*x^3*y^2+5*x*y^4)

def hubX : ℝ := -8/5
def radius : ℝ := 7/5
def uX : ℝ := -3/5
def uY : ℝ := 4/5
def vX : ℝ := -3/5
def vY : ℝ := -4/5

theorem u_unit : uX^2+uY^2=1 := by norm_num [uX, uY]
theorem v_unit : vX^2+vY^2=1 := by norm_num [vX, vY]

theorem direction_fifth_real :
    uX^5-10*uX^3*uY^2+5*uX*uY^4=237/3125 ∧
    vX^5-10*vX^3*vY^2+5*vX*vY^4=237/3125 := by
  norm_num [uX, uY, vX, vY]

def armU (t : ℝ) : ℝ :=
  modelRe ((1-t)*hubX+t*(radius*uX)) (t*(radius*uY))
def armV (t : ℝ) : ℝ :=
  modelRe ((1-t)*hubX+t*(radius*vX)) (t*(radius*vY))

def tailRecipU (s : ℝ) : ℝ :=
  15*radius*uX*s^4 + 5*radius^2*(uX^2-uY^2)*s^3 -
    radius^5*(uX^5-10*uX^3*uY^2+5*uX*uY^4)
def tailRecipV (s : ℝ) : ℝ :=
  15*radius*vX*s^4 + 5*radius^2*(vX^2-vY^2)*s^3 -
    radius^5*(vX^5-10*vX^3*vY^2+5*vX*vY^4)

def tailU (T : ℝ) : ℝ := modelRe (T*uX) (T*uY)
def tailV (T : ℝ) : ℝ := modelRe (T*vX) (T*vY)

theorem armU_bernstein (t : ℝ) : armU t =
    (-2232/3125)*(1-t)^5 +
    5*(-91359/15625)*t*(1-t)^4 +
    10*(-2201607/156250)*t^2*(1-t)^3 +
    10*(-15036143/781250)*t^3*(1-t)^2 +
    5*(-37150741/1953125)*t^4*(1-t) +
    (-153827009/9765625)*t^5 := by
  dsimp [armU, modelRe, hubX, radius, uX, uY]
  ring

theorem armV_eq_armU (t : ℝ) : armV t=armU t := by
  dsimp [armV, armU, modelRe, hubX, radius, uX, uY, vX, vY]
  ring

theorem tailRecipU_bernstein (s : ℝ) : tailRecipU s =
    (-3983259/9765625)*(1-s)^5 +
    5*(-3983259/9765625)*s*(1-s)^4 +
    10*(-3983259/9765625)*s^2*(1-s)^3 +
    10*(-13325893/19531250)*s^3*(1-s)^2 +
    5*(-39311384/9765625)*s^4*(1-s) +
    (-153827009/9765625)*s^5 := by
  dsimp [tailRecipU, radius, uX, uY]
  ring

theorem tailRecipV_eq_tailRecipU (s : ℝ) : tailRecipV s=tailRecipU s := by
  dsimp [tailRecipV, tailRecipU, radius, uX, uY, vX, vY]
  ring

theorem armU_nonpos {t : ℝ} (h0 : 0≤t) (h1 : t≤1) : armU t≤0 := by
  rw [armU_bernstein]
  exact bernsteinQuintic_nonpos h0 h1 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem armV_nonpos {t : ℝ} (h0 : 0≤t) (h1 : t≤1) : armV t≤0 := by
  rw [armV_eq_armU]
  exact armU_nonpos h0 h1

theorem tailRecipU_nonpos {s : ℝ} (h0 : 0≤s) (h1 : s≤1) :
    tailRecipU s≤0 := by
  rw [tailRecipU_bernstein]
  exact bernsteinQuintic_nonpos h0 h1 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem tailRecipV_nonpos {s : ℝ} (h0 : 0≤s) (h1 : s≤1) :
    tailRecipV s≤0 := by
  rw [tailRecipV_eq_tailRecipU]
  exact tailRecipU_nonpos h0 h1

theorem tailU_reciprocal_identity {T : ℝ} (hT : T≠0) :
    (radius/T)^5*tailU T=tailRecipU (radius/T) := by
  dsimp [tailU, tailRecipU, modelRe, radius, uX, uY]
  field_simp [hT]

theorem tailV_reciprocal_identity {T : ℝ} (hT : T≠0) :
    (radius/T)^5*tailV T=tailRecipV (radius/T) := by
  dsimp [tailV, tailRecipV, modelRe, radius, vX, vY]
  field_simp [hT]

theorem tailU_nonpos {T : ℝ} (hT : radius≤T) : tailU T≤0 := by
  have hR : 0<radius := by norm_num [radius]
  have hTp : 0<T := lt_of_lt_of_le hR hT
  have hp := tailRecipU_nonpos (le_of_lt (div_pos hR hTp))
    ((div_le_one hTp).mpr hT)
  rw [← tailU_reciprocal_identity (ne_of_gt hTp)] at hp
  by_contra hn
  have htail : 0<tailU T := lt_of_not_ge hn
  have hfac : 0<(radius/T)^5 := by positivity
  nlinarith [mul_pos hfac htail]

theorem tailV_nonpos {T : ℝ} (hT : radius≤T) : tailV T≤0 := by
  have hR : 0<radius := by norm_num [radius]
  have hTp : 0<T := lt_of_lt_of_le hR hT
  have hp := tailRecipV_nonpos (le_of_lt (div_pos hR hTp))
    ((div_le_one hTp).mpr hT)
  rw [← tailV_reciprocal_identity (ne_of_gt hTp)] at hp
  by_contra hn
  have htail : 0<tailV T := lt_of_not_ge hn
  have hfac : 0<(radius/T)^5 := by positivity
  nlinarith [mul_pos hfac htail]

def distSq : ℝ := (radius*uX-hubX)^2+(radius*uY)^2

theorem distSq_value : distSq=229/125 := by
  norm_num [distSq, radius, uX, uY, hubX]

theorem squared_metric_margin : radius^2-distSq=16/125 := by
  norm_num [distSq, radius, uX, uY, hubX]

theorem connector_length_lt_two_mul_radius :
    2*Real.sqrt distSq < 2*radius := by
  have hdist0 : 0≤distSq := by dsimp [distSq]; positivity
  have hsqrt : Real.sqrt distSq<radius := by
    rw [Real.sqrt_lt' (by norm_num [radius]), distSq_value]
    norm_num [radius]
  linarith

/-! The same rational connector works uniformly on an explicit coefficient
box.  These fifteen affine inequalities are the distinct arm/tail Bernstein
control obligations after symmetry and deletion of constant controls. -/

def InOpenChartBox (da ea db eb : ℝ) : Prop :=
  |da| ≤ 1/6 ∧ |ea| ≤ 1/6 ∧ |db| ≤ 1/6 ∧ |eb| ≤ 1/6

theorem open_chart_control_linear_forms {da ea db eb : ℝ}
    (hbox : InOpenChartBox da ea db eb) :
    625*da-1000*db+279 > 0 ∧
    22625*da-32400*db+3500*ea-11200*eb+91359 > 0 ∧
    202500*da-237425*db+70000*ea-197400*eb+2201607 > 0 ∧
    893750*da-701375*db+525000*ea-1281000*eb+15036143 > 0 ∧
    1937500*da-406875*db+1750000*ea-3605000*eb+37150741 > 0 ∧
    1171875*da+765625*db+1562500*ea-2625000*eb+21975287 > 0 ∧
    22625*da-32400*db-3500*ea+11200*eb+91359 > 0 ∧
    202500*da-237425*db-70000*ea+197400*eb+2201607 > 0 ∧
    893750*da-701375*db-525000*ea+1281000*eb+15036143 > 0 ∧
    1937500*da-406875*db-1750000*ea+3605000*eb+37150741 > 0 ∧
    1171875*da+765625*db-1562500*ea+2625000*eb+21975287 > 0 ∧
    21875*db-75000*eb+271957 > 0 ∧
    234375*da+306250*db+312500*ea-1050000*eb+5615912 > 0 ∧
    21875*db+75000*eb+271957 > 0 ∧
    234375*da+306250*db-312500*ea+1050000*eb+5615912 > 0 := by
  rcases hbox with ⟨hda, hea, hdb, heb⟩
  rw [abs_le] at hda hea hdb heb
  rcases hda with ⟨hda0, hda1⟩
  rcases hea with ⟨hea0, hea1⟩
  rcases hdb with ⟨hdb0, hdb1⟩
  rcases heb with ⟨heb0, heb1⟩
  norm_num at hda0 hda1 hea0 hea1 hdb0 hdb1 heb0 heb1
  constructor <;> try linarith
  constructor <;> try linarith
  constructor <;> try linarith
  constructor <;> try linarith
  constructor <;> try linarith
  constructor <;> try linarith
  constructor <;> try linarith
  constructor <;> try linarith
  constructor <;> try linarith
  constructor <;> try linarith
  constructor <;> try linarith
  constructor <;> try linarith
  constructor <;> try linarith
  constructor <;> linarith

end

end ErdosProblems.Erdos1041.TiedNewtonFacePositiveFibreRationalRescue
