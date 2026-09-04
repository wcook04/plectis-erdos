import ErdosProblems.Erdos1049.ZudilinConeArithmetic
import Mathlib.Topology.MetricSpace.Pseudo.Defs

/-!
# Erdős #1049: scalar moving-diagonal rational-clearing obstruction

Van Assche's little-`q`-Legendre construction has quadratic source decay on
every fixed moving diagonal.  At the rational base `3 / 2`, however, exact
homogeneous denominator clearing contributes a second quadratic term.  The
net exponent is the positive quantity defined below, so the forced
homogeneous-cleared forms grow instead of tending to zero.

The source asymptotics and polynomial degree calculation are recorded by the
exact companion receipt.  This module checks the elementary exponent identity,
its strict sign, and the source-independent topological consumer saying that
forms eventually bounded below by one cannot tend to zero.  The second part
records the corresponding two-parameter main term for every outward scalar
evaluation `x = p^m` with `m ≥ n`.  It does not formalize the little-`q`-
Legendre asymptotics themselves, bound primitive common odd content of the two
integer coefficients, or decide irrationality at `3 / 2`.
-/

namespace ErdosProblems.Erdos1049

open Filter

/-- The quadratic logarithmic growth left after minimally clearing a fixed
little-`q`-Legendre diagonal at the rational base `3 / 2`.

The first summand is the rational-base denominator tax left by the polynomial
degree `3 n² / 2`; the second is the cyclotomic clearing contribution. -/
noncomputable def fixedDiagonalRationalClearingExponent : ℝ :=
  (3 / 2 : ℝ) * Real.log (4 / 3) +
    (3 / Real.pi ^ 2) * Real.log 3

/-- The positive-form exponent is exactly the source decay/clearing balance

`(3/2 + 3/π²) log 2 + (3/π² - 3/2) log(3/2)`.

This is the all-fixed-offset leading exponent: changing the diagonal by a
fixed integer changes only lower-order terms. -/
theorem fixedDiagonalRationalClearingExponent_eq_sourceBalance :
    fixedDiagonalRationalClearingExponent =
      ((3 / 2 : ℝ) + 3 / Real.pi ^ 2) * Real.log 2 +
        (3 / Real.pi ^ 2 - (3 / 2 : ℝ)) * Real.log (3 / 2) := by
  have hlogFourThirds :
      Real.log (4 / 3 : ℝ) = Real.log 2 - Real.log (3 / 2) := by
    rw [show (4 / 3 : ℝ) = 2 / (3 / 2) by norm_num,
      Real.log_div (by norm_num) (by norm_num)]
  have hlogThree :
      Real.log (3 : ℝ) = Real.log 2 + Real.log (3 / 2) := by
    calc
      Real.log (3 : ℝ) = Real.log (2 * (3 / 2)) := by norm_num
      _ = Real.log 2 + Real.log (3 / 2) := by
        rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [fixedDiagonalRationalClearingExponent, hlogFourThirds, hlogThree]
  ring

/-- The rational-clearing exponent is strictly positive.  Therefore the
fixed-diagonal source forms grow exponentially on the `n²` scale after the
forced homogeneous rational-base clearing.  A separate common-content theorem
is required before transferring this sign to primitive integer rows. -/
theorem fixedDiagonalRationalClearingExponent_pos :
    0 < fixedDiagonalRationalClearingExponent := by
  have hlogFourThirds : 0 < Real.log (4 / 3 : ℝ) :=
    Real.log_pos (by norm_num)
  have hlogThree : 0 < Real.log (3 : ℝ) :=
    Real.log_pos (by norm_num)
  have hpiSq : 0 < Real.pi ^ 2 := sq_pos_of_pos Real.pi_pos
  unfold fixedDiagonalRationalClearingExponent
  exact add_pos
    (mul_pos (by norm_num) hlogFourThirds)
    (mul_pos (div_pos (by norm_num) hpiSq) hlogThree)

/-- The source-balance presentation of the exponent is strictly positive. -/
theorem fixedDiagonalSourceBalance_pos :
    0 < ((3 / 2 : ℝ) + 3 / Real.pi ^ 2) * Real.log 2 +
      (3 / Real.pi ^ 2 - (3 / 2 : ℝ)) * Real.log (3 / 2) := by
  rw [← fixedDiagonalRationalClearingExponent_eq_sourceBalance]
  exact fixedDiagonalRationalClearingExponent_pos

/-- The logarithmic main term for an outward scalar evaluation `x = p^m`.

The polynomial endpoint has degree `n*m + n^2/2 + o(n^2)`, while the
cyclotomic cutoff `m + O(1)` has degree `(3/π²)m² + o(m²)`.  At the rational
base `3/2`, composing source size with the unavoidable power-of-two clearing
leaves precisely this positive-form expression. -/
noncomputable def movingDiagonalRationalClearingMainTerm (n m : ℝ) : ℝ :=
  (n * m + n ^ 2 / 2) * Real.log (4 / 3) +
    (3 / Real.pi ^ 2) * m ^ 2 * Real.log 3

/-- The positive-form moving-diagonal main term is the same quantity obtained
by adding homogeneous denominator clearing to the source error balance. -/
theorem movingDiagonalRationalClearingMainTerm_eq_sourceBalance (n m : ℝ) :
    movingDiagonalRationalClearingMainTerm n m =
      (n * m + n ^ 2 / 2 + (3 / Real.pi ^ 2) * m ^ 2) * Real.log 2 +
        ((3 / Real.pi ^ 2) * m ^ 2 - (n * m + n ^ 2 / 2)) *
          Real.log (3 / 2) := by
  have hlogFourThirds :
      Real.log (4 / 3 : ℝ) = Real.log 2 - Real.log (3 / 2) := by
    rw [show (4 / 3 : ℝ) = 2 / (3 / 2) by norm_num,
      Real.log_div (by norm_num) (by norm_num)]
  have hlogThree :
      Real.log (3 : ℝ) = Real.log 2 + Real.log (3 / 2) := by
    calc
      Real.log (3 : ℝ) = Real.log (2 * (3 / 2)) := by norm_num
      _ = Real.log 2 + Real.log (3 / 2) := by
        rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [movingDiagonalRationalClearingMainTerm, hlogFourThirds, hlogThree]
  ring

/-- Every outward scalar moving diagonal has a strictly positive forced-
clearing main term.  This statement is deliberately finite-scale in `n,m`; it
also covers sequences for which `m/n` has no finite limit.  It does not bound
division by primitive common content. -/
theorem movingDiagonalRationalClearingMainTerm_pos
    {n m : ℝ} (hn : 0 < n) (hnm : n ≤ m) :
    0 < movingDiagonalRationalClearingMainTerm n m := by
  have hm : 0 < m := lt_of_lt_of_le hn hnm
  have hnmProd : 0 < n * m := mul_pos hn hm
  have hnSqHalf : 0 < n ^ 2 / 2 := div_pos (sq_pos_of_pos hn) (by norm_num)
  have hpoly : 0 < n * m + n ^ 2 / 2 := add_pos hnmProd hnSqHalf
  have hlogFourThirds : 0 < Real.log (4 / 3 : ℝ) :=
    Real.log_pos (by norm_num)
  have hlogThree : 0 < Real.log (3 : ℝ) :=
    Real.log_pos (by norm_num)
  have hpiSq : 0 < Real.pi ^ 2 := sq_pos_of_pos Real.pi_pos
  unfold movingDiagonalRationalClearingMainTerm
  exact add_pos
    (mul_pos hpoly hlogFourThirds)
    (mul_pos (mul_pos (div_pos (by norm_num) hpiSq) (sq_pos_of_pos hm))
      hlogThree)

/-- The `n²`-normalized exponent along a diagonal with limiting ratio
`m/n = beta`. -/
noncomputable def movingDiagonalRatioExponent (beta : ℝ) : ℝ :=
  (beta + 1 / 2) * Real.log (4 / 3) +
    (3 / Real.pi ^ 2) * beta ^ 2 * Real.log 3

/-- Ratio one recovers the fixed-offset exponent. -/
theorem movingDiagonalRatioExponent_one :
    movingDiagonalRatioExponent 1 = fixedDiagonalRationalClearingExponent := by
  rw [movingDiagonalRatioExponent, fixedDiagonalRationalClearingExponent]
  ring

/-- Every nonnegative limiting ratio has positive normalized exponent; the
outward scalar regime used in the source has `1 ≤ beta`. -/
theorem movingDiagonalRatioExponent_pos {beta : ℝ} (hbeta : 0 ≤ beta) :
    0 < movingDiagonalRatioExponent beta := by
  have hcoeff : 0 < beta + 1 / 2 := by linarith
  have hlogFourThirds : 0 < Real.log (4 / 3 : ℝ) :=
    Real.log_pos (by norm_num)
  have hlogThree : 0 < Real.log (3 : ℝ) :=
    Real.log_pos (by norm_num)
  have hpiSq : 0 < Real.pi ^ 2 := sq_pos_of_pos Real.pi_pos
  unfold movingDiagonalRatioExponent
  exact add_pos_of_pos_of_nonneg
    (mul_pos hcoeff hlogFourThirds)
    (mul_nonneg
      (mul_nonneg (le_of_lt (div_pos (by norm_num) hpiSq)) (sq_nonneg beta))
      (le_of_lt hlogThree))

/-- Any common divisor of one denominator/numerator Padé pair divides its
adjacent second-kind determinant.  This is the source-independent arithmetic
consumer of the exact little-`q`-Legendre determinant identity. -/
theorem commonDivisor_dvd_adjacentSecondKindDeterminant
    {g P Q Pprev Qprev : ℤ} (hP : g ∣ P) (hQ : g ∣ Q) :
    g ∣ Q * Pprev - P * Qprev := by
  exact dvd_sub (dvd_mul_of_dvd_left hQ Pprev) (dvd_mul_of_dvd_left hP Qprev)

/-- After the source identity identifies the adjacent determinant with the
negative of its explicit numerator, every common divisor divides that
numerator.  For the rational base `3/2`, the external identity supplies
`numerator = 3^n + 2^n`. -/
theorem commonDivisor_dvd_adjacentSecondKindNumerator
    {g P Q Pprev Qprev numerator : ℤ}
    (hP : g ∣ P) (hQ : g ∣ Q)
    (hdet : Q * Pprev - P * Qprev = -numerator) :
    g ∣ numerator := by
  have hneg : g ∣ -numerator := by
    rw [← hdet]
    exact commonDivisor_dvd_adjacentSecondKindDeterminant hP hQ
  simpa using hneg

/-- An integer Bézout certificate bounds common row content.  Applied to
coefficient polynomials after homogeneous specialization, the certificate
constant is their resultant (up to a power of the homogeneous denominator).
For odd content at `(3,2)`, that power of two is harmless. -/
theorem commonDivisor_dvd_bezoutCertificate
    {g A C U V R : ℤ} (hA : g ∣ A) (hC : g ∣ C)
    (hbezout : U * A + V * C = R) :
    g ∣ R := by
  rw [← hbezout]
  exact dvd_add (dvd_mul_of_dvd_right hA U) (dvd_mul_of_dvd_right hC V)

/-- A real sequence whose absolute values are eventually at least one cannot
tend to zero.  This is the source-independent consumer of the exact lower
bounds and of the positive asymptotic exponent. -/
theorem not_tendsto_zero_of_eventually_one_le_abs
    (u : ℕ → ℝ) (hlarge : ∀ᶠ n in atTop, 1 ≤ |u n|) :
    ¬ Tendsto u atTop (nhds 0) := by
  intro hzero
  rcases (eventually_atTop.1 hlarge) with ⟨N₁, hN₁⟩
  rcases Metric.tendsto_atTop.1 hzero 1 (by norm_num) with ⟨N₂, hN₂⟩
  let N := max N₁ N₂
  have hge : 1 ≤ |u N| := hN₁ N (le_max_left _ _)
  have hlt : |u N| < 1 := by
    simpa [Real.dist_eq] using hN₂ N (le_max_right _ _)
  exact (not_lt_of_ge hge) hlt

end ErdosProblems.Erdos1049
