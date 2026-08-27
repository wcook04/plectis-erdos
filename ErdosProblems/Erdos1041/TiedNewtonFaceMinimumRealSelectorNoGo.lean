import Mathlib.Tactic

/-!
# Erdős #1041: the minimum-real critical-value hub can be the wrong hub

For the exact real quintic

`Q(z) = -(379/256) z + 3 z^2 - z^5`,

the critical point `c = 1/4` uniquely minimizes the real part of the critical
values.  Nevertheless, every radial cutoff based at `c` fails on the positive
real fifth-root direction: `Q(2/3) > 0`, and `2/3` lies either on the finite
arm or on its outward tail.

The companion note supplies the complex-root classification.  This file
checks its exact rational kernels: the derivative factorization, the critical
values, the real cubic-root comparison, the conjugate-pair gap after Viete
reduction, and the cutoff dichotomy.  The theorem is a selector no-go, not a
counterexample to the adjacent-hub existence problem or to Erdős #1041.
-/

namespace ErdosProblems.Erdos1041.TiedNewtonFaceMinimumRealSelectorNoGo

noncomputable section

def model (x : ℝ) : ℝ :=
  -(379 / 256) * x + 3 * x ^ 2 - x ^ 5

def derivativeModel (x : ℝ) : ℝ :=
  -(379 / 256) + 6 * x - 5 * x ^ 4

def cubicFactor (x : ℝ) : ℝ :=
  320 * x ^ 3 + 80 * x ^ 2 + 20 * x - 379

/-- At a critical point the quintic value reduces to this quadratic. -/
def criticalValue (x : ℝ) : ℝ :=
  (9 / 5) * x ^ 2 - (379 / 320) * x

/-- Real part of `criticalValue (x+iy)`. -/
def criticalValueRealPart (x y : ℝ) : ℝ :=
  (9 / 5) * (x ^ 2 - y ^ 2) - (379 / 320) * x

/-- The derivative has one rational root and one cubic factor. -/
theorem derivative_factorization (x : ℝ) :
    derivativeModel x = -((4 * x - 1) * cubicFactor x) / 256 := by
  dsimp [derivativeModel, cubicFactor]
  ring

theorem quarter_is_critical : derivativeModel (1 / 4) = 0 := by
  norm_num [derivativeModel]

theorem model_quarter : model (1 / 4) = -(47 / 256) := by
  norm_num [model]

theorem model_two_thirds : model (2 / 3) = 6677 / 31104 := by
  norm_num [model]

theorem model_two_thirds_pos : 0 < model (2 / 3) := by
  rw [model_two_thirds]
  norm_num

/-- Eliminate the fifth power at any real critical point. -/
theorem model_eq_criticalValue_of_critical {x : ℝ}
    (hx : derivativeModel x = 0) : model x = criticalValue x := by
  have hid : model x = criticalValue x + (x / 5) * derivativeModel x := by
    dsimp [model, criticalValue, derivativeModel]
    ring
  rw [hid, hx]
  ring

/-- The cubic factor is strictly increasing, in division-free difference
form. -/
theorem cubicFactor_difference (r s : ℝ) :
    cubicFactor r - cubicFactor s =
      (r - s) * (320 * (r ^ 2 + r * s + s ^ 2) + 80 * (r + s) + 20) := by
  dsimp [cubicFactor]
  ring

theorem cubicDifferenceMultiplier_pos (r s : ℝ) :
    0 < 320 * (r ^ 2 + r * s + s ^ 2) + 80 * (r + s) + 20 := by
  have h₁ : 0 ≤ (r - s) ^ 2 := sq_nonneg (r - s)
  have h₂ : 0 ≤ (r + s + 1 / 6) ^ 2 := sq_nonneg (r + s + 1 / 6)
  nlinarith

theorem cubicFactor_twentyFour_twentyFive :
    cubicFactor (24 / 25) = -(9239 / 3125) := by
  norm_num [cubicFactor]

/-- The unique real root of the cubic factor lies to the right of `24/25`.
Only this lower bound is needed downstream. -/
theorem cubic_root_gt_twentyFour_twentyFive {r : ℝ}
    (hr : cubicFactor r = 0) : 24 / 25 < r := by
  by_contra hnot
  have hrs : r ≤ 24 / 25 := le_of_not_gt hnot
  have hmul := cubicDifferenceMultiplier_pos (24 / 25) r
  have hdiff := cubicFactor_difference (24 / 25) r
  rw [hr, cubicFactor_twentyFour_twentyFive] at hdiff
  nlinarith

/-- The other real critical value is positive, hence strictly larger than the
value `-47/256` at the rational critical point. -/
theorem real_cubic_criticalValue_gt_quarter {r : ℝ}
    (hr : cubicFactor r = 0) :
    criticalValue (1 / 4) < criticalValue r := by
  have hrlo := cubic_root_gt_twentyFour_twentyFive hr
  have hrpos : 0 < r := by nlinarith
  have hfactor : 0 < (9 / 5 : ℝ) * r - 379 / 320 := by nlinarith
  have hcv : 0 < criticalValue r := by
    rw [show criticalValue r = r * ((9 / 5) * r - 379 / 320) by
      dsimp [criticalValue]; ring]
    positivity
  have hquarter : criticalValue (1 / 4) = -(47 / 256) := by
    norm_num [criticalValue]
  rw [hquarter]
  linarith

/-- After using the cubic equation, the real-part gap for the nonreal
conjugate pair is this rational function of its real companion root. -/
def conjugatePairGap (r : ℝ) : ℝ :=
  (10460 * r ^ 2 + 4245 * r - 13644) / (12800 * r)

theorem conjugatePairGap_pos_of_gt {r : ℝ} (hr : 24 / 25 < r) :
    0 < conjugatePairGap r := by
  have hrpos : 0 < r := by nlinarith
  have hlinear : 0 < 10460 * (r + 24 / 25) + 4245 := by nlinarith
  have hprod :
      0 < (r - 24 / 25) * (10460 * (r + 24 / 25) + 4245) :=
    mul_pos (sub_pos.mpr hr) hlinear
  have hbase :
      (10460 : ℝ) * (24 / 25) ^ 2 + 4245 * (24 / 25) - 13644 =
        8892 / 125 := by norm_num
  have hnum : 0 < 10460 * r ^ 2 + 4245 * r - 13644 := by
    nlinarith
  exact div_pos hnum (mul_pos (by norm_num) hrpos)

theorem conjugatePairGap_pos_of_cubic_root {r : ℝ}
    (hr : cubicFactor r = 0) : 0 < conjugatePairGap r :=
  conjugatePairGap_pos_of_gt (cubic_root_gt_twentyFour_twentyFive hr)

/-- Viete's relations for the nonreal pair convert its real critical-value
gap into the unreduced cubic rational expression. -/
theorem conjugate_pair_gap_identity
    {r x y : ℝ} (hr0 : r ≠ 0)
    (hsum : 2 * x + r = -(1 / 4))
    (hprod : x ^ 2 + y ^ 2 = 379 / (320 * r)) :
    criticalValueRealPart x y - criticalValue (1 / 4) =
      (11520 * r ^ 3 + 13340 * r ^ 2 + 4965 * r - 27288) /
        (12800 * r) := by
  dsimp [criticalValueRealPart, criticalValue]
  have hx : x = -(r + 1 / 4) / 2 := by linarith
  subst x
  field_simp [hr0] at hprod ⊢
  nlinarith

theorem cubic_gap_reduction {r : ℝ} (hr0 : r ≠ 0)
    (hr : cubicFactor r = 0) :
    (11520 * r ^ 3 + 13340 * r ^ 2 + 4965 * r - 27288) /
        (12800 * r) = conjugatePairGap r := by
  dsimp [cubicFactor, conjugatePairGap] at hr ⊢
  field_simp [hr0]
  nlinarith

/-- Exact minimum-real-value kernel for the two nonreal critical points.  In
the ordinary proof `r` is the real cubic root and `x±iy` the conjugate roots;
the two hypotheses are precisely their Viete sum and product relations. -/
theorem conjugate_pair_criticalValueRealPart_gt_quarter
    {r x y : ℝ} (hr : cubicFactor r = 0)
    (hsum : 2 * x + r = -(1 / 4))
    (hprod : x ^ 2 + y ^ 2 = 379 / (320 * r)) :
    criticalValue (1 / 4) < criticalValueRealPart x y := by
  have hrlo := cubic_root_gt_twentyFour_twentyFive hr
  have hr0 : r ≠ 0 := by nlinarith
  have hid := conjugate_pair_gap_identity hr0 hsum hprod
  have hreduce := cubic_gap_reduction hr0 hr
  have hgap := conjugatePairGap_pos_of_cubic_root hr
  rw [hreduce] at hid
  linarith

def onQuarterArm (R x : ℝ) : Prop := 1 / 4 ≤ x ∧ x ≤ R

def onOutwardTail (R x : ℝ) : Prop := R ≤ x

/-- Every cutoff puts `2/3` either on the finite positive-real arm from the
hub or on its outward tail. -/
theorem twoThirds_on_arm_or_tail (R : ℝ) :
    onQuarterArm R (2 / 3) ∨ onOutwardTail R (2 / 3) := by
  by_cases hR : R ≤ 2 / 3
  · exact Or.inr hR
  · left
    constructor
    · norm_num
    · linarith

/-- No radial cutoff based at the minimum-real critical point can make both
the finite positive-real arm and its outward tail nonpositive. -/
theorem no_safe_positive_real_cutoff :
    ¬ ∃ R : ℝ,
      (∀ x : ℝ, onQuarterArm R x → model x ≤ 0) ∧
      (∀ x : ℝ, onOutwardTail R x → model x ≤ 0) := by
  rintro ⟨R, harm, htail⟩
  rcases twoThirds_on_arm_or_tail R with h | h
  · have := harm (2 / 3) h
    linarith [model_two_thirds_pos]
  · have := htail (2 / 3) h
    linarith [model_two_thirds_pos]

end

end ErdosProblems.Erdos1041.TiedNewtonFaceMinimumRealSelectorNoGo
