import Mathlib.Tactic

/-!
# Erdős #1041: the smallest-gap Form-A selector is false

This module checks the exact rational core of
`ConcyclicSmallestGapSelectorCounterexample.md`.

Five Gaussian-rational points `w0,...,w4` occur in cyclic order on the unit
circle, with the `w3,w4` gap uniquely shortest.  The full spoke to `w4` is
unsafe, so common radius zero is inadmissible.  At every positive common radius
`s ≤ 1`, the midpoint of the truncated `w3,w4` chord already has five-factor
product strictly above one.

The uniform-in-`s` assertion is certified by an exact degree-ten Bernstein
expansion with strictly positive coefficients.  This refutes only the rule
"always choose the smallest angular gap"; it does not refute the unrestricted
Form-A-cut objective or Erdős #1041.
-/

namespace ErdosProblems.Erdos1041.ConcyclicSmallestGapSelectorCounterexample

noncomputable section

def w0 : ℂ := 1439999 / 1440001 + (2400 / 1440001) * Complex.I
def w1 : ℂ := 57 / 185 + (176 / 185) * Complex.I
def w2 : ℂ := -1431 / 1769 + (1040 / 1769) * Complex.I
def w3 : ℂ := -3080 / 3809 - (2241 / 3809) * Complex.I
def w4 : ℂ := 57 / 185 - (176 / 185) * Complex.I

def midpoint : ℂ := -352687 / 1409330 - (1084969 / 1409330) * Complex.I

def cross (a b : ℂ) : ℝ := a.re * b.im - a.im * b.re

def pentagonNormSq (z : ℂ) : ℝ :=
  Complex.normSq (z - w0) * Complex.normSq (z - w1) *
  Complex.normSq (z - w2) * Complex.normSq (z - w3) *
  Complex.normSq (z - w4)

/-- Integer power-basis numerator of `(pentagonNormSq (s * midpoint) - 1) / s`,
up to the positive rational scale recorded in `midpoint_product_identity`. -/
def powerPoly (s : ℝ) : ℝ :=
    329437356222324912321505567967594520865 * s ^ 9
  + 614883766066998361025096710029353434 * s ^ 8
  - 2644906528549297448207157859926314686 * s ^ 7
  - 3269816058220021712592183722255917728 * s ^ 6
  + 1167839891730480656123602663407383336 * s ^ 5
  + 1895474209514799107401125898138172544464 * s ^ 4
  + 1782170405017880809526450336938659280 * s ^ 3
  - 7614741505777075939304079097375171200 * s ^ 2
  - 9399572300480629462367408687627462000 * s
  + 3334699563498365822801058045903940000

/-- The first ten nonnegative Bernstein terms. -/
def bernsteinRest (s : ℝ) : ℝ :=
    4201721450007940936729333137838964400000 * (1 - s) ^ 10
  + 10 * 3017375340147381624471039643197904188000 * s * (1 - s) ^ 9
  + 45 * 1619816468125064185912231933830339182400 * s ^ 2 * (1 - s) ^ 8
  + 120 * 27757623193676369552937738274125305640 * s ^ 3 * (1 - s) ^ 7
  + 210 * 9632756851694700568299940173896153746944 * s ^ 4 * (1 - s) ^ 6
  + 252 * 53205056656517066222747395760209387879000 * s ^ 5 * (1 - s) ^ 5
  + 210 * 164879804300206482094181899329856364668272 * s ^ 6 * (1 - s) ^ 4
  + 120 * 390095881693175680784105820679729934274741 * s ^ 7 * (1 - s) ^ 3
  + 45 * 785476790093915683831181440512582833433024 * s ^ 8 * (1 - s) ^ 2
  + 10 * 1460169358477571010623116817491275419731962 * s ^ 9 * (1 - s)

def bernsteinNumerator (s : ℝ) : ℝ :=
  bernsteinRest s + 2783191474942717508220142424063525535063900 * s ^ 10

theorem roots_unit :
    Complex.normSq w0 = 1 ∧ Complex.normSq w1 = 1 ∧
    Complex.normSq w2 = 1 ∧ Complex.normSq w3 = 1 ∧
    Complex.normSq w4 = 1 := by
  norm_num [w0, w1, w2, w3, w4, Complex.normSq_apply]

theorem midpoint_eq : midpoint = (w3 + w4) / 2 := by
  apply Complex.ext <;> norm_num [midpoint, w3, w4]

/-- Every displayed cyclic gap is strictly shorter than `π`. -/
theorem cyclic_gaps_are_minor :
    0 < cross w0 w1 ∧ 0 < cross w1 w2 ∧ 0 < cross w2 w3 ∧
    0 < cross w3 w4 ∧ 0 < cross w4 w0 := by
  norm_num [cross, w0, w1, w2, w3, w4]

/-- The `w3,w4` chord is strictly shorter than every other adjacent chord.
Together with `cyclic_gaps_are_minor`, the elementary strict monotonicity of
`2 sin(δ/2)` on `0 < δ < π` identifies it as the unique smallest angular gap. -/
theorem selected_chord_uniquely_shortest :
    Complex.normSq (w3 - w4) < Complex.normSq (w0 - w1) ∧
    Complex.normSq (w3 - w4) < Complex.normSq (w1 - w2) ∧
    Complex.normSq (w3 - w4) < Complex.normSq (w2 - w3) ∧
    Complex.normSq (w3 - w4) < Complex.normSq (w4 - w0) := by
  norm_num [w0, w1, w2, w3, w4, Complex.normSq_apply]

/-- Radius zero cannot be used for the selected pair: the full spoke to `w4`
already exits the unit sublevel at the exact waypoint `w4/10`. -/
theorem endpoint_four_full_spoke_unsafe :
    1 < pentagonNormSq ((1 / 10 : ℂ) * w4) := by
  norm_num [pentagonNormSq, w0, w1, w2, w3, w4, Complex.normSq_apply]

/-- Exact conversion from power basis to a degree-ten Bernstein basis. -/
theorem power_eq_bernstein (s : ℝ) :
    1260 * powerPoly s = bernsteinNumerator s := by
  unfold powerPoly bernsteinNumerator bernsteinRest
  ring

theorem bernsteinRest_nonneg {s : ℝ} (hs : 0 ≤ s) (h1 : s ≤ 1) :
    0 ≤ bernsteinRest s := by
  have hsub : 0 ≤ 1 - s := sub_nonneg.mpr h1
  unfold bernsteinRest
  positivity

theorem bernsteinNumerator_pos {s : ℝ} (hs : 0 < s) (h1 : s ≤ 1) :
    0 < bernsteinNumerator s := by
  have hrest : 0 ≤ bernsteinRest s := bernsteinRest_nonneg (le_of_lt hs) h1
  have hlast :
      0 < (2783191474942717508220142424063525535063900 : ℝ) * s ^ 10 := by
    positivity
  unfold bernsteinNumerator
  exact add_pos_of_nonneg_of_pos hrest hlast

theorem powerPoly_pos {s : ℝ} (hs : 0 < s) (h1 : s ≤ 1) :
    0 < powerPoly s := by
  have hb : 0 < bernsteinNumerator s := bernsteinNumerator_pos hs h1
  have hid := power_eq_bernstein s
  nlinarith

/-- Exact product factorization at the selected chord midpoint. -/
theorem midpoint_product_identity (s : ℝ) :
    pentagonNormSq ((s : ℂ) * midpoint) - 1 =
      s * ((961 / 2620148092600599198725979487928148264500000 : ℝ) * powerPoly s) := by
  norm_num [pentagonNormSq, midpoint, w0, w1, w2, w3, w4,
    powerPoly, Complex.normSq_apply]
  ring

/-- At every positive common radius, the midpoint of the selected truncated
chord already lies strictly outside the unit lemniscate. -/
theorem midpoint_unsafe_at_every_positive_radius {s : ℝ} (hs : 0 < s)
    (h1 : s ≤ 1) :
    1 < pentagonNormSq ((s : ℂ) * midpoint) := by
  have hp : 0 < powerPoly s := powerPoly_pos hs h1
  have hc : 0 < (961 / 2620148092600599198725979487928148264500000 : ℝ) := by
    norm_num
  have hprod :
      0 < s * ((961 / 2620148092600599198725979487928148264500000 : ℝ) * powerPoly s) := by
    positivity
  have hid := midpoint_product_identity s
  linarith

/-- The formal counterexample package: common radius zero is blocked by an
unsafe arm, and every positive common radius is blocked by the chord midpoint. -/
theorem smallest_gap_common_radius_selector_fails :
    1 < pentagonNormSq ((1 / 10 : ℂ) * w4) ∧
    ∀ s : ℝ, 0 < s → s ≤ 1 → 1 < pentagonNormSq ((s : ℂ) * midpoint) := by
  exact ⟨endpoint_four_full_spoke_unsafe,
    fun _ hs h1 => midpoint_unsafe_at_every_positive_radius hs h1⟩

end


end ErdosProblems.Erdos1041.ConcyclicSmallestGapSelectorCounterexample
