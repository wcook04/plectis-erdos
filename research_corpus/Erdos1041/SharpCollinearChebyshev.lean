import ErdosProblems.Erdos1041.SharpCollinearAlternation
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.RootsExtrema
import Mathlib.RingTheory.Polynomial.ScaleRoots
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The sharp Chebyshev comparator for collinear Erdos #1041

For degree `n`, put `r = cos (pi / (2n))`.  The polynomial

`T_n(r X) / (2^(n-1) r^n)`

is monic, vanishes at `-1` and `1`, and has absolute value at most

`1 / (2^(n-1) r^n)`

on `[-1,1]`.  Combining these facts with the constrained alternation theorem
gives the sharp upper bound for one of the alternating interior peaks of any
monic comparison polynomial with the same endpoint zeros.
-/

namespace ErdosProblems.Erdos1041.SharpCollinearChebyshev

open Set
open Polynomial

open ErdosProblems.Erdos1041.SharpCollinearAlternation

/-- The scale that sends the two outermost roots of `T_n` to `-1` and `1`. -/
noncomputable def endpointScale (n : ℕ) : ℝ :=
  Real.cos (Real.pi / (2 * (n : ℝ)))

/-- The endpoint-normalised monic Chebyshev comparison polynomial. -/
noncomputable def monicScaledChebyshev (n : ℕ) : ℝ[X] :=
  C (((2 : ℝ) ^ (n - 1))⁻¹) *
    (Polynomial.Chebyshev.T ℝ (n : ℤ)).scaleRoots (endpointScale n)⁻¹

/-- The sharp normalised height.  A later algebraic simplification rewrites
this as `1 / (2^(n-1) * cos(pi/(2n))^n)`. -/
noncomputable def comparisonBound (n : ℕ) : ℝ :=
  |((2 : ℝ) ^ (n - 1))⁻¹ * (endpointScale n)⁻¹ ^ n|

theorem endpointScale_pos {n : ℕ} (hn : 2 ≤ n) :
    0 < endpointScale n := by
  apply Real.cos_pos_of_mem_Ioo
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hden : 0 < (2 : ℝ) * n := by positivity
  have hangle : 0 < Real.pi / ((2 : ℝ) * n) :=
    div_pos Real.pi_pos hden
  constructor
  · linarith [Real.pi_pos]
  · have hdenlt : (2 : ℝ) < 2 * n := by nlinarith
    have hinv : (1 : ℝ) / (2 * n) < 1 / 2 :=
      one_div_lt_one_div_of_lt (by norm_num) hdenlt
    calc
      Real.pi / (2 * (n : ℝ)) = Real.pi * (1 / (2 * n)) := by ring
      _ < Real.pi * (1 / 2) := mul_lt_mul_of_pos_left hinv Real.pi_pos
      _ = Real.pi / 2 := by ring

theorem endpointScale_ne_zero {n : ℕ} (hn : 2 ≤ n) :
    endpointScale n ≠ 0 :=
  (endpointScale_pos hn).ne'

/-- Evaluation formula exposing the ordinary Chebyshev polynomial at the
contracted point `r*x`. -/
theorem eval_monicScaledChebyshev {n : ℕ} (hn : 2 ≤ n) (x : ℝ) :
    (monicScaledChebyshev n).eval x =
      ((2 : ℝ) ^ (n - 1))⁻¹ * (endpointScale n)⁻¹ ^ n *
        (Polynomial.Chebyshev.T ℝ (n : ℤ)).eval (endpointScale n * x) := by
  have hr := endpointScale_ne_zero hn
  have hscale := Polynomial.scaleRoots_eval_mul
    (Polynomial.Chebyshev.T ℝ (n : ℤ)) (endpointScale n * x) (endpointScale n)⁻¹
  have hscale' :
      ((Polynomial.Chebyshev.T ℝ (n : ℤ)).scaleRoots (endpointScale n)⁻¹).eval x =
        (endpointScale n)⁻¹ ^ n *
          (Polynomial.Chebyshev.T ℝ (n : ℤ)).eval (endpointScale n * x) := by
    simpa [Polynomial.Chebyshev.natDegree_T, hr, mul_assoc] using hscale
  simp [monicScaledChebyshev, eval_mul, hscale', mul_assoc]

/-- The comparison polynomial is genuinely monic of degree `n`. -/
theorem monicScaledChebyshev_isMonicOfDegree {n : ℕ} (hn : 2 ≤ n) :
    (monicScaledChebyshev n).IsMonicOfDegree n := by
  have ha : ((2 : ℝ) ^ (n - 1))⁻¹ ≠ 0 := by positivity
  constructor
  · simp [monicScaledChebyshev, Polynomial.natDegree_C_mul ha,
      Polynomial.Chebyshev.natDegree_T]
  · rw [Polynomial.Monic]
    simp [monicScaledChebyshev, Polynomial.leadingCoeff_mul,
      Polynomial.Chebyshev.leadingCoeff_T]

private theorem eval_chebyshev_endpointScale {n : ℕ} (hn : 2 ≤ n) :
    (Polynomial.Chebyshev.T ℝ (n : ℤ)).eval (endpointScale n) = 0 := by
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  rw [endpointScale, Polynomial.Chebyshev.T_real_cos]
  rw [show ((n : ℤ) : ℝ) * (Real.pi / (2 * (n : ℝ))) = Real.pi / 2 by
    norm_num
    field_simp]
  exact Real.cos_pi_div_two

theorem eval_monicScaledChebyshev_one {n : ℕ} (hn : 2 ≤ n) :
    (monicScaledChebyshev n).eval 1 = 0 := by
  rw [eval_monicScaledChebyshev hn]
  simp [eval_chebyshev_endpointScale hn]

theorem eval_monicScaledChebyshev_neg_one {n : ℕ} (hn : 2 ≤ n) :
    (monicScaledChebyshev n).eval (-1) = 0 := by
  rw [eval_monicScaledChebyshev hn]
  rw [show endpointScale n * (-1 : ℝ) = -endpointScale n by ring,
    Polynomial.Chebyshev.T_eval_neg]
  simp [eval_chebyshev_endpointScale hn]

/-- Uniform sharp comparison bound on the normalised root interval. -/
theorem abs_eval_monicScaledChebyshev_le {n : ℕ} (hn : 2 ≤ n)
    {x : ℝ} (hx : |x| ≤ 1) :
    |(monicScaledChebyshev n).eval x| ≤ comparisonBound n := by
  have hrpos := endpointScale_pos hn
  have hrle : endpointScale n ≤ 1 := Real.cos_le_one _
  have hrx : |endpointScale n * x| ≤ 1 := by
    rw [abs_mul, abs_of_pos hrpos]
    exact mul_le_one₀ hrle (abs_nonneg x) hx
  have hT := Polynomial.Chebyshev.abs_eval_T_real_le_one (n : ℤ) hrx
  rw [eval_monicScaledChebyshev hn, abs_mul]
  exact (mul_le_mul_of_nonneg_left hT (abs_nonneg _)).trans_eq (by
    simp [comparisonBound])

/-- Concrete sharp alternation consequence in degree `m+2`.  This is the
formal core of the sharp collinear diameter theorem after affine
normalisation and the elementary choice of one extremum in each root gap. -/
theorem exists_peak_le_comparisonBound
    {m : ℕ} {p : ℝ[X]} {c : Fin (m + 1) → ℝ}
    (hp : p.IsMonicOfDegree (m + 2))
    (hc : StrictMono c) (ha : -1 < c 0) (hb : c (Fin.last m) < 1)
    (hpa : p.eval (-1) = 0) (hpb : p.eval 1 = 0)
    (hpalt : ∀ i : Fin m,
      p.eval (c i.castSucc) * p.eval (c i.succ) < 0)
    (hc_mem : ∀ i : Fin (m + 1), |c i| ≤ 1) :
    ∃ i : Fin (m + 1), |p.eval (c i)| ≤ comparisonBound (m + 2) := by
  apply exists_peak_le_of_monic_comparison hp
    (monicScaledChebyshev_isMonicOfDegree (n := m + 2) (Nat.le_add_left 2 m))
    hc ha hb hpa hpb
    (eval_monicScaledChebyshev_neg_one (n := m + 2) (Nat.le_add_left 2 m))
    (eval_monicScaledChebyshev_one (n := m + 2) (Nat.le_add_left 2 m))
    hpalt
  intro i
  exact abs_eval_monicScaledChebyshev_le (n := m + 2) (Nat.le_add_left 2 m) (hc_mem i)

end ErdosProblems.Erdos1041.SharpCollinearChebyshev
