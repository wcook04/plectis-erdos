import Mathlib.Tactic

/-!
# Erdős #1041: component-selector finite kernels and critical-hub rescue

The companion note proves the component degree/ramification/end formula by
proper mapping, Riemann mapping, finite Blaschke products, and Riemann--Hurwitz.
Those analytic adapters are not formalized here.  This module checks their
finite arithmetic fan-in, the radial-defect monotonicity kernel, and the exact
radical Bernstein/tail/metric certificate at the calibration quintic's
original critical point.
-/

namespace ErdosProblems.Erdos1041.TiedNewtonFaceComponentSelector

noncomputable section

/-- Finite fan-in of `degree=endCount` and `ramification=degree-1`. -/
theorem endCount_eq_one_add_ramification
    {degree endCount ramification : ℕ}
    (hdegree : 1 ≤ degree) (hends : endCount = degree)
    (hram : ramification = degree - 1) :
    endCount = 1 + ramification := by
  omega

def renormalizedDefect (distance : ℝ → ℝ) (R : ℝ) : ℝ :=
  distance R - 2*R

/-- Appending two radial segments makes the renormalized intrinsic defect
nonincreasing. -/
theorem renormalizedDefect_antitone
    {distance : ℝ → ℝ} {R₁ R₂ : ℝ} (_hR : R₁ ≤ R₂)
    (hextend : distance R₂ ≤ distance R₁ + 2*(R₂-R₁)) :
    renormalizedDefect distance R₂ ≤ renormalizedDefect distance R₁ := by
  dsimp [renormalizedDefect]
  linarith

/-- A strict negative limiting upper bound forces a finite strict connector;
the non-strict zero case deliberately is not claimed. -/
theorem finite_negative_of_eventual_upper_bound
    {defect beta : ℝ} (hdefect : defect ≤ beta) (hbeta : beta < 0) :
    defect < 0 := lt_of_le_of_lt hdefect hbeta

def sqrtFive : ℝ := Real.sqrt 5
def hubX : ℝ := 1/4
def radius : ℝ := 1/2
def omegaX : ℝ := (sqrtFive-1)/4
/-- The squared imaginary coordinate of the fifth-root direction. -/
def omegaYSq : ℝ := (5+sqrtFive)/8

theorem sqrtFive_sq : sqrtFive^2 = 5 := by
  dsimp [sqrtFive]
  norm_num

theorem sqrtFive_gt_two : 2 < sqrtFive := by
  have hs0 : 0 ≤ sqrtFive := Real.sqrt_nonneg _
  nlinarith [sqrtFive_sq]

theorem sqrtFive_lt_three : sqrtFive < 3 := by
  have hs0 : 0 ≤ sqrtFive := Real.sqrt_nonneg _
  nlinarith [sqrtFive_sq]

theorem sqrtFive_pow_three : sqrtFive^3 = 5*sqrtFive := by
  calc
    sqrtFive^3 = sqrtFive*sqrtFive^2 := by ring
    _ = 5*sqrtFive := by rw [sqrtFive_sq]; ring

theorem sqrtFive_pow_four : sqrtFive^4 = 25 := by
  calc
    sqrtFive^4 = (sqrtFive^2)^2 := by ring
    _ = 25 := by rw [sqrtFive_sq]; norm_num

theorem sqrtFive_pow_five : sqrtFive^5 = 25*sqrtFive := by
  calc
    sqrtFive^5 = sqrtFive*sqrtFive^4 := by ring
    _ = 25*sqrtFive := by rw [sqrtFive_pow_four]; ring

theorem omega_unit_sq : omegaX^2 + omegaYSq = 1 := by
  dsimp [omegaX, omegaYSq]
  nlinarith [sqrtFive_sq]

/-- `Re Q(x+iy)` expressed using `y²`, avoiding an irrelevant nested radical. -/
def modelReSq (x ySq : ℝ) : ℝ :=
  -(379/256)*x + 3*(x^2-ySq) -
    (x^5-10*x^3*ySq+5*x*ySq^2)

def armPlus (t : ℝ) : ℝ :=
  modelReSq ((1-t)*hubX+t*(radius*omegaX))
    ((t*radius)^2*omegaYSq)

def tailPlus (r : ℝ) : ℝ :=
  modelReSq (r*omegaX) (r^2*omegaYSq)

theorem armPlus_bernstein (t : ℝ) : armPlus t =
    (-(47/256))*(1-t)^5 +
    5*(-(47/256))*t*(1-t)^4 +
    10*(-(849+182*sqrtFive)/5120)*t^2*(1-t)^3 +
    10*(-(1319+1117*sqrtFive)/10240)*t^3*(1-t)^2 +
    5*(-(369+1162*sqrtFive)/5120)*t^4*(1-t) +
    (-(69+763*sqrtFive)/2048)*t^5 := by
  simp only [armPlus, modelReSq, hubX, radius, omegaX, omegaYSq]
  ring_nf
  rw [sqrtFive_sq, sqrtFive_pow_three, sqrtFive_pow_four, sqrtFive_pow_five]
  ring

/-- Convexity of the degree-five Bernstein basis: if every control is at most
a fixed negative constant, so is the represented polynomial. -/
theorem bernsteinQuintic_le_const
    {t b0 b1 b2 b3 b4 b5 k : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (h0 : b0 ≤ k) (h1 : b1 ≤ k) (h2 : b2 ≤ k)
    (h3 : b3 ≤ k) (h4 : b4 ≤ k) (h5 : b5 ≤ k) :
    b0*(1-t)^5 + 5*b1*t*(1-t)^4 + 10*b2*t^2*(1-t)^3 +
      10*b3*t^3*(1-t)^2 + 5*b4*t^4*(1-t) + b5*t^5 ≤ k := by
  have hnt : 0 ≤ 1-t := by linarith
  have hB0 : 0 ≤ (1-t)^5 := by positivity
  have hB1 : 0 ≤ 5*t*(1-t)^4 := by positivity
  have hB2 : 0 ≤ 10*t^2*(1-t)^3 := by positivity
  have hB3 : 0 ≤ 10*t^3*(1-t)^2 := by positivity
  have hB4 : 0 ≤ 5*t^4*(1-t) := by positivity
  have hB5 : 0 ≤ t^5 := by positivity
  have h0' := mul_le_mul_of_nonneg_right h0 hB0
  have h1' := mul_le_mul_of_nonneg_right h1 hB1
  have h2' := mul_le_mul_of_nonneg_right h2 hB2
  have h3' := mul_le_mul_of_nonneg_right h3 hB3
  have h4' := mul_le_mul_of_nonneg_right h4 hB4
  have h5' := mul_le_mul_of_nonneg_right h5 hB5
  have hsum : (1-t)^5 + 5*t*(1-t)^4 + 10*t^2*(1-t)^3 +
      10*t^3*(1-t)^2 + 5*t^4*(1-t) + t^5 = 1 := by ring
  nlinarith

theorem armPlus_neg {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : armPlus t < 0 := by
  rw [armPlus_bernstein]
  have hs := sqrtFive_gt_two
  have hle :
      (-(47/256 : ℝ))*(1-t)^5 +
      5*(-(47/256 : ℝ))*t*(1-t)^4 +
      10*(-(849+182*sqrtFive)/5120)*t^2*(1-t)^3 +
      10*(-(1319+1117*sqrtFive)/10240)*t^3*(1-t)^2 +
      5*(-(369+1162*sqrtFive)/5120)*t^4*(1-t) +
      (-(69+763*sqrtFive)/2048)*t^5 ≤ -(47/256 : ℝ) :=
    bernsteinQuintic_le_const
      (t := t)
      (b0 := -(47/256 : ℝ)) (b1 := -(47/256 : ℝ))
      (b2 := -(849+182*sqrtFive)/5120)
      (b3 := -(1319+1117*sqrtFive)/10240)
      (b4 := -(369+1162*sqrtFive)/5120)
      (b5 := -(69+763*sqrtFive)/2048)
      (k := -(47/256 : ℝ)) ht0 ht1
      (by norm_num) (by norm_num) (by nlinarith) (by nlinarith)
      (by nlinarith) (by nlinarith)
  exact lt_of_le_of_lt hle (by norm_num)

theorem tailPlus_formula (r : ℝ) : tailPlus r =
    -r^5-3*(1+sqrtFive)/4*r^2-379*(sqrtFive-1)/1024*r := by
  simp only [tailPlus, modelReSq, omegaX, omegaYSq]
  ring_nf
  rw [sqrtFive_sq, sqrtFive_pow_three, sqrtFive_pow_four, sqrtFive_pow_five]
  ring

theorem tailPlus_neg {r : ℝ} (hr : 0 < r) : tailPlus r < 0 := by
  rw [tailPlus_formula]
  have hs := sqrtFive_gt_two
  have hr2 : 0 < r^2 := sq_pos_of_pos hr
  have hr5 : 0 < r^5 := pow_pos hr _
  nlinarith [mul_pos hr (sub_pos.mpr hs)]

def armDistSq : ℝ := (radius*omegaX-hubX)^2 + radius^2*omegaYSq

theorem armDistSq_value : armDistSq = 3/8-sqrtFive/16 := by
  dsimp [armDistSq, radius, omegaX, hubX, omegaYSq]
  nlinarith [sqrtFive_sq]

theorem connector_length_lt_two_mul_radius :
    2*Real.sqrt armDistSq < 2*radius := by
  have hd0 : 0 ≤ armDistSq := by
    rw [armDistSq_value]
    nlinarith [sqrtFive_lt_three]
  have hsqrt : Real.sqrt armDistSq < radius := by
    rw [Real.sqrt_lt' (by norm_num [radius]), armDistSq_value]
    dsimp [radius]
    nlinarith [sqrtFive_gt_two]
  linarith

end

end ErdosProblems.Erdos1041.TiedNewtonFaceComponentSelector
