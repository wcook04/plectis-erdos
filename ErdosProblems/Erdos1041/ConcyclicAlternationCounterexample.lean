import Mathlib.Tactic

/-!
# Erdős #1041: exact counterexample to concentric alternation

This module checks the rational core of the counterexample in
`ConcyclicAlternationCounterexample.md`.  The five `w` points and five `x`
points lie on the unit circle.  Each `x_k` lies on the closed positively
oriented minor arc from `w_k` to `w_(k+1)`.  At radius `3/20`, the squared
five-factor product at every `x_k` is strictly larger than
`(1 + (3/20)^5)^2`.

Thus every one of the five root gaps contains a point violating the proposed
concentric-alternation bound.  This refutes that auxiliary conjecture only;
it does not refute the Form-A cut inequality or Erdős #1041.
-/

namespace ErdosProblems.Erdos1041.ConcyclicAlternationCounterexample

noncomputable section

def w0 : ℂ := 44 / 125 + (117 / 125) * Complex.I
def w1 : ℂ := -1809 / 2609 + (1880 / 2609) * Complex.I
def w2 : ℂ := -4 / 5 - (3 / 5) * Complex.I
def w3 : ℂ := 24 / 145 - (143 / 145) * Complex.I
def w4 : ℂ := 1012 / 1013 - (45 / 1013) * Complex.I

def x0 : ℂ := w1
def x1 : ℂ := -9999 / 10001 + (200 / 10001) * Complex.I
def x2 : ℂ := w2
def x3 : ℂ := 91 / 109 - (60 / 109) * Complex.I
def x4 : ℂ := w4

def cross (a b : ℂ) : ℝ := a.re * b.im - a.im * b.re

def pentagonNormSq (z : ℂ) : ℝ :=
  Complex.normSq (z - w0) * Complex.normSq (z - w1) *
  Complex.normSq (z - w2) * Complex.normSq (z - w3) *
  Complex.normSq (z - w4)

def radius : ℂ := 3 / 20
def thresholdSq : ℝ := (1 + (3 / 20 : ℝ) ^ 5) ^ 2

/-- All five roots and all five gap test directions are exactly on the unit
circle. -/
theorem all_points_unit :
    Complex.normSq w0 = 1 ∧ Complex.normSq w1 = 1 ∧
    Complex.normSq w2 = 1 ∧ Complex.normSq w3 = 1 ∧
    Complex.normSq w4 = 1 ∧ Complex.normSq x0 = 1 ∧
    Complex.normSq x1 = 1 ∧ Complex.normSq x2 = 1 ∧
    Complex.normSq x3 = 1 ∧ Complex.normSq x4 = 1 := by
  norm_num [w0, w1, w2, w3, w4, x0, x1, x2, x3, x4,
    Complex.normSq_apply]

/-- The listed cyclic order uses five counterclockwise gaps, each strictly
shorter than `π`.  Positivity of the cross product is the exact algebraic
certificate for the sine of each consecutive angular gap. -/
theorem root_gaps_are_minor :
    0 < cross w0 w1 ∧ 0 < cross w1 w2 ∧ 0 < cross w2 w3 ∧
    0 < cross w3 w4 ∧ 0 < cross w4 w0 := by
  norm_num [cross, w0, w1, w2, w3, w4]

/-- `x_k` belongs to the closed counterclockwise minor arc from `w_k` to
`w_(k+1)`.  The two cross-product inequalities are an algebraic arc
certificate; consecutive root gaps in this witness are all shorter than π. -/
theorem test_points_in_gaps :
    (0 ≤ cross w0 x0 ∧ 0 ≤ cross x0 w1) ∧
    (0 ≤ cross w1 x1 ∧ 0 ≤ cross x1 w2) ∧
    (0 ≤ cross w2 x2 ∧ 0 ≤ cross x2 w3) ∧
    (0 ≤ cross w3 x3 ∧ 0 ≤ cross x3 w4) ∧
    (0 ≤ cross w4 x4 ∧ 0 ≤ cross x4 w0) := by
  norm_num [cross, w0, w1, w2, w3, w4, x0, x1, x2, x3, x4]

/-- The exact five-gap refutation at `s = 3/20`.  Each conjunct says that the
squared modulus of the five-factor product is strictly larger than the square
of the conjectured bound `1 + s^5`. -/
theorem every_gap_exceeds_regular_bound :
    thresholdSq < pentagonNormSq (radius * x0) ∧
    thresholdSq < pentagonNormSq (radius * x1) ∧
    thresholdSq < pentagonNormSq (radius * x2) ∧
    thresholdSq < pentagonNormSq (radius * x3) ∧
    thresholdSq < pentagonNormSq (radius * x4) := by
  norm_num [thresholdSq, pentagonNormSq, radius,
    w0, w1, w2, w3, w4, x0, x1, x2, x3, x4,
    Complex.normSq_apply]

end

end ErdosProblems.Erdos1041.ConcyclicAlternationCounterexample
