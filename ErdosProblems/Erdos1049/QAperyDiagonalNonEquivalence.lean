import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-!
# Erdős #1049: the q-Apéry recurrence fails on Van Assche's diagonal

This module checks one finite polynomial identity.  Van Assche's diagonal
`P_n(p^n | p⁻¹)` has the three displayed initial values below.  Substitution
in the `n = 0` Amdeberhan--Zeilberger operator leaves a strictly negative
residual for every real `p > 1`.  Hence that diagonal does not satisfy that
operator.

No general recurrence, endpoint asymptotic, or irrationality statement is
asserted here.
-/

namespace ErdosProblems.Erdos1049

/-- The `n = 0` value of Van Assche's moving diagonal. -/
def vanAsscheDiagonalZero (_p : ℝ) : ℝ := 1

/-- The `n = 1` little-`q`-Legendre coefficient sum after evaluating at
`x = p`. -/
def vanAsscheDiagonalOne (p : ℝ) : ℝ := 1 - (1 + p)

/-- The `n = 2` little-`q`-Legendre coefficient sum after evaluating at
`x = p²`.  The three summands are the `k = 0, 1, 2` terms. -/
def vanAsscheDiagonalTwo (p : ℝ) : ℝ :=
  1 - (1 + p) * (1 + p + p ^ 2) +
    p * (1 + p + 2 * p ^ 2 + p ^ 3 + p ^ 4)

/-- The first three Van Assche diagonal values in expanded form. -/
theorem vanAsscheDiagonal_initial_values (p : ℝ) :
    vanAsscheDiagonalZero p = 1 ∧
      vanAsscheDiagonalOne p = -p ∧
      vanAsscheDiagonalTwo p =
        p * (p ^ 4 + p ^ 3 + p ^ 2 - p - 1) := by
  constructor
  · rfl
  constructor
  · simp [vanAsscheDiagonalOne]
  · simp only [vanAsscheDiagonalTwo]
    ring

/-- The coefficient `y₀(0)` in the Amdeberhan--Zeilberger operator. -/
def qAperyYZeroAtZero (p : ℝ) : ℝ :=
  p * (p - 1) * (p ^ 2 + 2)

/-- The coefficient `y₂(0)` in the Amdeberhan--Zeilberger operator. -/
def qAperyYTwoAtZero (p : ℝ) : ℝ :=
  (p ^ 2 - 1) * (p + 2)

/-- The coefficient `y₁(0)` in the Amdeberhan--Zeilberger operator. -/
def qAperyYOneAtZero (p : ℝ) : ℝ :=
  p ^ 8 + 2 * p ^ 6 * (p + 1) + p ^ 5 -
    4 * p ^ 3 * (p + 1) + (p ^ 2 - 4 * p + 1) * p +
    2 * (p + 1)

/-- The Amdeberhan--Zeilberger operator applied at `n = 0` to the first
three values of Van Assche's diagonal. -/
def vanAsscheQAperyResidualAtZero (p : ℝ) : ℝ :=
  qAperyYTwoAtZero p * vanAsscheDiagonalTwo p +
    qAperyYOneAtZero p * vanAsscheDiagonalOne p +
    qAperyYZeroAtZero p * vanAsscheDiagonalZero p

/-- Exact factorisation of the `n = 0` residual. -/
theorem vanAsscheQAperyResidualAtZero_eq (p : ℝ) :
    vanAsscheQAperyResidualAtZero p =
      -p * (p - 1) ^ 2 * (p + 1) *
        (p ^ 5 + 2 * p ^ 4 + 2 * p ^ 3 + 2 * p ^ 2 + 2) := by
  simp only [vanAsscheQAperyResidualAtZero, qAperyYTwoAtZero,
    qAperyYOneAtZero, qAperyYZeroAtZero, vanAsscheDiagonalZero,
    vanAsscheDiagonalOne, vanAsscheDiagonalTwo]
  ring

/-- For every real `p > 1`, the `n = 0` residual is strictly negative. -/
theorem vanAsscheQAperyResidualAtZero_neg {p : ℝ} (hp : 1 < p) :
    vanAsscheQAperyResidualAtZero p < 0 := by
  rw [vanAsscheQAperyResidualAtZero_eq]
  have hp0 : 0 < p := by linarith
  have hpm1 : 0 < p - 1 := sub_pos.mpr hp
  have hpp1 : 0 < p + 1 := by linarith
  have hpoly :
      0 < p ^ 5 + 2 * p ^ 4 + 2 * p ^ 3 + 2 * p ^ 2 + 2 := by
    positivity
  have hprod :
      0 < p * (p - 1) ^ 2 * (p + 1) *
        (p ^ 5 + 2 * p ^ 4 + 2 * p ^ 3 + 2 * p ^ 2 + 2) := by
    positivity
  nlinarith

/-- Van Assche's diagonal fails the Amdeberhan--Zeilberger recurrence already
at `n = 0`. -/
theorem vanAsscheQAperyResidualAtZero_ne_zero {p : ℝ} (hp : 1 < p) :
    vanAsscheQAperyResidualAtZero p ≠ 0 :=
  ne_of_lt (vanAsscheQAperyResidualAtZero_neg hp)

#print axioms vanAsscheDiagonal_initial_values
#print axioms vanAsscheQAperyResidualAtZero_eq
#print axioms vanAsscheQAperyResidualAtZero_ne_zero

end ErdosProblems.Erdos1049
