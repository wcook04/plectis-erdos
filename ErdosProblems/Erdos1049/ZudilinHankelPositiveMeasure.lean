import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic

/-!
# Erdős #1049: combinatorial core of the positive-moment Hankel argument

Zudilin (Res. Number Theory 2 (2016), Art. 15, eq. (6) and §4) studies the
normalized moments `v_m^*` at `x = z = 1` and proves `ord_q V_N^* ≥ B_N`.
The associated-graded leading coefficient `C_N = (N!)²(N+1)!/2^N` is already
landed, conditionally on row initial monomials, in
`ZudilinSharpHankelCoefficient.lean`.  That module is a *formal* power-series
argument.  It does not produce a positive measure, nor a fixed-`q` residual.

This file Lean-checks the algebraic skeleton of the companion ordinary-proof
note `ZudilinHankelPositiveMeasure.md`:

* the product identity `∏_{i<N} c_i = C_N` with `c_k = (k+1)²(k+2)/2`;
* the diagonal `q`-exponent `∑_i i + 2 ∑_i i(N-1-i) = B_N`;
* the `q=0` generating-function coefficients `[w^k](1+2w)/(1-w)^4 = c_k`.

The q-binomial nonnegativity, cubic comparison, finite Gram identity,
infinite discrete measure, two-sided `O_q(N)` residual, and positivity of
`γ_k(q)` remain ordinary mathematics in the companion note.
-/

open scoped BigOperators
open Finset

namespace ErdosProblems.Erdos1049

/-! ## Leading coefficient and order constants -/

/-- The associated-graded row coefficient `c_k = (k+1)²(k+2)/2`. -/
def zudilinMomentRowC (k : ℕ) : ℚ :=
  ((k + 1 : ℚ) ^ 2 * (k + 2)) / 2

/-- Zudilin's leading Hankel coefficient `C_N = (N!)²(N+1)!/2^N`. -/
def zudilinHankelLeadingC (N : ℕ) : ℚ :=
  ((N.factorial : ℚ) ^ 2 * ((N + 1).factorial : ℚ)) / (2 : ℚ) ^ N

/-- The exact formal order `B_N = N(N-1)(2N-1)/6`. -/
def zudilinHankelOrderB (N : ℕ) : ℚ :=
  (N : ℚ) * (N - 1) * (2 * N - 1) / 6

@[simp] theorem zudilinMomentRowC_zero : zudilinMomentRowC 0 = 1 := by
  simp [zudilinMomentRowC]

@[simp] theorem zudilinHankelLeadingC_zero : zudilinHankelLeadingC 0 = 1 := by
  simp [zudilinHankelLeadingC]

@[simp] theorem zudilinHankelOrderB_zero : zudilinHankelOrderB 0 = 0 := by
  simp [zudilinHankelOrderB]

lemma factorial_succ_cast (n : ℕ) :
    ((n + 1).factorial : ℚ) = (n + 1 : ℚ) * n.factorial := by
  rw [Nat.factorial_succ]
  exact_mod_cast rfl

/-- The product of the first `N` row coefficients is exactly `C_N`. -/
theorem prod_zudilinMomentRowC (N : ℕ) :
    ∏ i ∈ range N, zudilinMomentRowC i = zudilinHankelLeadingC N := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [prod_range_succ, ih]
      unfold zudilinMomentRowC zudilinHankelLeadingC
      -- Rewrite `(N+2)!` before `(N+1)!`, otherwise the latter is
      -- reintroduced on the right-hand side.
      rw [factorial_succ_cast (N + 1), factorial_succ_cast N, pow_succ (2 : ℚ) N]
      push_cast
      field_simp
      ring

/-- The summand of the diagonal `q`-exponent at index `i` in rank `N`. -/
def diagExponentSummand (N i : ℕ) : ℚ :=
  (i : ℚ) + 2 * i * ((N : ℚ) - 1 - i)

theorem sum_range_cast_id (N : ℕ) :
    (∑ i ∈ range N, (i : ℚ)) = (N : ℚ) * (N - 1) / 2 := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [sum_range_succ, ih]
      push_cast
      ring

/-- The diagonal tuple `k_i = i` forces total exponent `B_N`. -/
theorem sum_diag_zudilinHankelExponent (N : ℕ) :
    ∑ i ∈ range N, diagExponentSummand N i = zudilinHankelOrderB N := by
  induction N with
  | zero => simp [diagExponentSummand, zudilinHankelOrderB]
  | succ N ih =>
      have hinc :
          ∑ i ∈ range (N + 1), diagExponentSummand (N + 1) i =
            ∑ i ∈ range N, diagExponentSummand N i + N ^ 2 := by
        rw [sum_range_succ]
        have hlast : diagExponentSummand (N + 1) N = N := by
          simp [diagExponentSummand]
        have hshift :
            ∑ i ∈ range N, diagExponentSummand (N + 1) i =
              ∑ i ∈ range N, diagExponentSummand N i +
                ∑ i ∈ range N, (2 * (i : ℚ)) := by
          rw [← sum_add_distrib]
          refine sum_congr rfl fun i _ => ?_
          simp [diagExponentSummand]
          ring
        have h2sum : ∑ i ∈ range N, (2 * (i : ℚ)) = (N : ℚ) * (N - 1) := by
          calc
            ∑ i ∈ range N, (2 * (i : ℚ)) = 2 * ∑ i ∈ range N, (i : ℚ) := by
              simp [mul_sum]
            _ = 2 * ((N : ℚ) * (N - 1) / 2) := by rw [sum_range_cast_id]
            _ = (N : ℚ) * (N - 1) := by ring
        rw [hshift, hlast, h2sum]
        ring
      have hB : zudilinHankelOrderB (N + 1) = zudilinHankelOrderB N + N ^ 2 := by
        simp [zudilinHankelOrderB]
        field_simp
        ring
      rw [hinc, ih, hB]

/-! ## The formal `q = 0` generating function -/

/-- `[w^k] (1-w)^{-4}` is related to `\binom{k+3}{3}` via descending factorials. -/
theorem choose_three_cast (n : ℕ) :
    (n.choose 3 : ℚ) = (n.descFactorial 3 : ℚ) / 6 := by
  have h : n.descFactorial 3 = 6 * n.choose 3 := by
    rw [Nat.descFactorial_eq_factorial_mul_choose]
    norm_num
  rw [h]
  push_cast
  field_simp

/-- `n.descFactorial 3 = n(n-1)(n-2)` after the Nat subtractions reduce. -/
theorem descFactorial_three_of_add_two (k : ℕ) :
    ((k + 2).descFactorial 3 : ℚ) = (k + 2 : ℚ) * (k + 1) * k := by
  rw [Nat.descFactorial_succ, Nat.descFactorial_succ, Nat.descFactorial_one]
  simp
  ring

theorem descFactorial_three (k : ℕ) :
    ((k + 3).descFactorial 3 : ℚ) = (k + 3 : ℚ) * (k + 2) * (k + 1) := by
  rw [Nat.descFactorial_succ, Nat.descFactorial_succ, Nat.descFactorial_one]
  simp
  ring

/-- The constant-term generating function of `G_q` at `q = 0` has coefficients `c_k`. -/
theorem coeff_G0_eq_zudilinMomentRowC (k : ℕ) :
    ((k + 3).choose 3 : ℚ) + 2 * ((k + 2).choose 3 : ℚ) = zudilinMomentRowC k := by
  rw [choose_three_cast, choose_three_cast, descFactorial_three,
    descFactorial_three_of_add_two]
  simp [zudilinMomentRowC]
  field_simp
  ring

/- Cubic comparison, q-binomial nonnegativity, and the finite Gram expansion
of an atomic moment Hankel remain ordinary proofs in
`ZudilinHankelPositiveMeasure.md`. They are not kernel-checked here. -/

end ErdosProblems.Erdos1049
