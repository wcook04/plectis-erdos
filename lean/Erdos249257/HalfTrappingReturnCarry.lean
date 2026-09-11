import Erdos249257.AdelicHeightObstruction
import Erdos249257.BooleanMobiusCarry
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# Carry transfer at overlapping half-trapping returns

This module records two exact conclusions from the trapping-return analysis
for the greedy `1 / 2` Mersenne achievement-set problem.

First, a family of rational-linear channels that is invariant under every
zero-valued formal relation has rank at most one.  Consequently every square
minor of size at least two vanishes.  This closes the raw shifted-channel
determinant route at all ranks, rather than only at the experimentally tested
ranks two through four.

Second, two reverse-carry presentations with a common coefficient word, a
single `1/0` seam, and a common word on the following overlap have a carry
difference equal to a power of two times an odd integer.  Combining this exact
factorisation with any common Archimedean carry bound gives the corresponding
power-of-two spacing inequality.

The results below deliberately isolate the proof-bearing algebraic core.  They
do not assert that a failed greedy separation produces the required reverse
carry presentation, nor do they supply an earlier overlapping return.  The
remaining endpoint obligation is the predecessor-supply theorem tying the
greedy threshold orbit to this carry interface.
-/

namespace Erdos249257.HalfTrappingReturnCarry

open Matrix

/-! ## All-rank no-go for scalar-relation-invariant linear channels -/

/-- If every channel kills every relation killed by scalar evaluation, then
the evaluation matrix has rank at most one.  Hence every square minor indexed
by a nontrivial finite type has determinant zero.

This is the all-rank determinant consequence of
`AdelicHeightObstruction.linearDescender_eq_smul_eval`. -/
theorem relationInvariantLinearChannels_det_eq_zero
    {V ι : Type*} [AddCommGroup V] [Module ℚ V]
    [Fintype ι] [DecidableEq ι] [Nontrivial ι]
    (ev : V →ₗ[ℚ] ℚ) (channel : ι → V →ₗ[ℚ] ℚ)
    (hker : ∀ j : ι, LinearMap.ker ev ≤ LinearMap.ker (channel j))
    (he : ∃ e : V, ev e = 1) (row : ι → V) :
    Matrix.det (fun i j : ι ↦ channel j (row i)) = 0 := by
  choose c hc using fun j : ι ↦
    AdelicHeightObstruction.linearDescender_eq_smul_eval
      ev (channel j) (hker j) he
  have hmatrix :
      (fun i j : ι ↦ channel j (row i)) =
        Matrix.vecMulVec (fun i : ι ↦ ev (row i)) c := by
    ext i j
    rw [hc j]
    simp [Matrix.vecMulVec]
  rw [hmatrix]
  exact Matrix.det_vecMulVec _ _

/-! ## Reverse-carry words -/

/-- A finite or infinite coefficient word together with a binary-normalized
reverse carry.  The intended equation is

`bit m + 2 * carry m = coeff m + carry (m + 1)`.

No Boolean hypothesis is built into the structure: the overlap theorem needs
only the explicit seam and overlap bits that it consumes. -/
structure ReverseCarryWord where
  coeff : ℕ → ℤ
  bit : ℕ → ℤ
  carry : ℕ → ℤ
  normalized : ∀ m : ℕ,
    bit m + 2 * carry m = coeff m + carry (m + 1)

/-- Carry difference between two reverse-carry words. -/
def carryDifference (left right : ReverseCarryWord) (m : ℕ) : ℤ :=
  left.carry m - right.carry m

/-- When the coefficient and output bits agree at one position, the carry
difference doubles across that position. -/
theorem carryDifference_succ_eq_two_mul
    (left right : ReverseCarryWord) (m : ℕ)
    (hcoeff : left.coeff m = right.coeff m)
    (hbit : left.bit m = right.bit m) :
    carryDifference left right (m + 1) =
      2 * carryDifference left right m := by
  unfold carryDifference
  have hleft := left.normalized m
  have hright := right.normalized m
  omega

/-- A `1/0` output-bit seam with a common coefficient makes the next carry
difference `2D + 1`, hence odd. -/
theorem carryDifference_succ_eq_two_mul_add_one
    (left right : ReverseCarryWord) (m : ℕ)
    (hcoeff : left.coeff m = right.coeff m)
    (hleft : left.bit m = 1) (hright : right.bit m = 0) :
    carryDifference left right (m + 1) =
      2 * carryDifference left right m + 1 := by
  unfold carryDifference
  have hl := left.normalized m
  have hr := right.normalized m
  omega

/-- Iterating a pure doubling recurrence over an interval. -/
private theorem iterate_doubling
    (D : ℕ → ℤ) (start length : ℕ)
    (hdouble : ∀ j < length,
      D (start + j + 1) = 2 * D (start + j)) :
    D (start + length) = (2 : ℤ) ^ length * D start := by
  induction length with
  | zero => simp
  | succ length ih =>
      rw [Nat.add_succ, hdouble length (Nat.lt_succ_self length),
        ih (fun j hj ↦ hdouble j (hj.trans (Nat.lt_succ_self length)))]
      ring

/-- **Nonlinear carry-transfer core.**  A common coefficient at the seam,
a `1/0` seam bit, and a common coefficient/output word for `length` further
positions force the terminal carry difference to be `2^length` times an odd
integer. -/
theorem overlappingReverseCarryWords_carryDifference_eq_twoPow_mul_odd
    (left right : ReverseCarryWord) (seam length : ℕ)
    (hcoeffSeam : left.coeff seam = right.coeff seam)
    (hleftSeam : left.bit seam = 1)
    (hrightSeam : right.bit seam = 0)
    (hcoeffOverlap : ∀ j < length,
      left.coeff (seam + 1 + j) = right.coeff (seam + 1 + j))
    (hbitOverlap : ∀ j < length,
      left.bit (seam + 1 + j) = right.bit (seam + 1 + j)) :
    ∃ z : ℤ, Odd z ∧
      carryDifference left right (seam + 1 + length) =
        (2 : ℤ) ^ length * z := by
  let D := carryDifference left right
  have hseam : D (seam + 1) = 2 * D seam + 1 :=
    carryDifference_succ_eq_two_mul_add_one
      left right seam hcoeffSeam hleftSeam hrightSeam
  have hdouble : ∀ j < length,
      D (seam + 1 + j + 1) = 2 * D (seam + 1 + j) := by
    intro j hj
    exact carryDifference_succ_eq_two_mul left right (seam + 1 + j)
      (hcoeffOverlap j hj) (hbitOverlap j hj)
  refine ⟨D (seam + 1), ?_, ?_⟩
  · rw [hseam]
    exact odd_two_mul_add_one _
  · exact iterate_doubling D (seam + 1) length hdouble

/-- If both terminal carries lie between zero and a common real bound, the
exact odd factorisation forces the same-scale Archimedean inequality
`2^length ≤ bound`. -/
theorem twoPow_le_realBound_of_carryDifference_eq_twoPow_mul_odd
    (left right : ReverseCarryWord) (top length : ℕ) (bound : ℝ)
    (hfactor : ∃ z : ℤ, Odd z ∧
      carryDifference left right top = (2 : ℤ) ^ length * z)
    (hleftNonneg : 0 ≤ left.carry top)
    (hrightNonneg : 0 ≤ right.carry top)
    (hleftBound : (left.carry top : ℝ) ≤ bound)
    (hrightBound : (right.carry top : ℝ) ≤ bound) :
    (2 : ℝ) ^ length ≤ bound := by
  obtain ⟨z, hzOdd, hfactor⟩ := hfactor
  obtain ⟨k, hk⟩ := hzOdd
  have hzNe : z ≠ 0 := by
    rw [hk]
    omega
  have hzAbs : (1 : ℤ) ≤ |z| := Int.one_le_abs hzNe
  have hpowNonneg : (0 : ℤ) ≤ (2 : ℤ) ^ length := by positivity
  have hlowerInt :
      (2 : ℤ) ^ length ≤ |carryDifference left right top| := by
    rw [hfactor, abs_mul, abs_of_nonneg hpowNonneg]
    simpa using mul_le_mul_of_nonneg_left hzAbs hpowNonneg
  have hlowerReal :
      (2 : ℝ) ^ length ≤
        |(left.carry top : ℝ) - (right.carry top : ℝ)| := by
    exact_mod_cast hlowerInt
  have hdiffBound :
      |(left.carry top : ℝ) - (right.carry top : ℝ)| ≤ bound := by
    rw [abs_le]
    have hleftNonnegReal : (0 : ℝ) ≤ left.carry top := by
      exact_mod_cast hleftNonneg
    have hrightNonnegReal : (0 : ℝ) ≤ right.carry top := by
      exact_mod_cast hrightNonneg
    constructor
    · linarith
    · linarith
  exact hlowerReal.trans hdiffBound

/-- Combined overlap-and-smallness theorem.  This is the precise abstract
same-scale obstruction used by the trapping-return route. -/
theorem overlappingReverseCarryWords_twoPow_le_realBound
    (left right : ReverseCarryWord) (seam length : ℕ) (bound : ℝ)
    (hcoeffSeam : left.coeff seam = right.coeff seam)
    (hleftSeam : left.bit seam = 1)
    (hrightSeam : right.bit seam = 0)
    (hcoeffOverlap : ∀ j < length,
      left.coeff (seam + 1 + j) = right.coeff (seam + 1 + j))
    (hbitOverlap : ∀ j < length,
      left.bit (seam + 1 + j) = right.bit (seam + 1 + j))
    (hleftNonneg : 0 ≤ left.carry (seam + 1 + length))
    (hrightNonneg : 0 ≤ right.carry (seam + 1 + length))
    (hleftBound : (left.carry (seam + 1 + length) : ℝ) ≤ bound)
    (hrightBound : (right.carry (seam + 1 + length) : ℝ) ≤ bound) :
    (2 : ℝ) ^ length ≤ bound := by
  apply twoPow_le_realBound_of_carryDifference_eq_twoPow_mul_odd
    left right (seam + 1 + length) length bound
  · exact overlappingReverseCarryWords_carryDifference_eq_twoPow_mul_odd
      left right seam length hcoeffSeam hleftSeam hrightSeam
      hcoeffOverlap hbitOverlap
  · exact hleftNonneg
  · exact hrightNonneg
  · exact hleftBound
  · exact hrightBound

/-! ## Midpoint-indexed form -/

/-- Midpoint-indexed form of the exact overlap factorisation.  Under
`M ≤ 2N-2`, the seam is `M+1`, the overlap length is `2N-M-1`, and its top
carry index is exactly `2N+1`. -/
theorem overlappingMidpointReturns_carryDifference_eq_twoPow_mul_odd
    (left right : ReverseCarryWord) (N M : ℕ) (hN : 1 ≤ N)
    (hNM : M ≤ 2 * N - 2)
    (hcoeffSeam : left.coeff (M + 1) = right.coeff (M + 1))
    (hleftSeam : left.bit (M + 1) = 1)
    (hrightSeam : right.bit (M + 1) = 0)
    (hcoeffOverlap : ∀ j < 2 * N - M - 1,
      left.coeff (M + 2 + j) = right.coeff (M + 2 + j))
    (hbitOverlap : ∀ j < 2 * N - M - 1,
      left.bit (M + 2 + j) = right.bit (M + 2 + j)) :
    ∃ z : ℤ, Odd z ∧
      carryDifference left right (2 * N + 1) =
        (2 : ℤ) ^ (2 * N - M - 1) * z := by
  have htop : M + 1 + 1 + (2 * N - M - 1) = 2 * N + 1 := by omega
  simpa [htop, Nat.add_assoc] using
    overlappingReverseCarryWords_carryDifference_eq_twoPow_mul_odd
      left right (M + 1) (2 * N - M - 1)
      hcoeffSeam hleftSeam hrightSeam
      (fun j hj ↦ by simpa [Nat.add_assoc] using hcoeffOverlap j hj)
      (fun j hj ↦ by simpa [Nat.add_assoc] using hbitOverlap j hj)

/-- Midpoint-indexed same-scale spacing inequality.  Once the two endpoint
carries have a common nonnegative real bound, their overlap length cannot
exceed the dyadic size permitted by that bound. -/
theorem overlappingMidpointReturns_twoPow_le_realBound
    (left right : ReverseCarryWord) (N M : ℕ) (bound : ℝ) (hN : 1 ≤ N)
    (hNM : M ≤ 2 * N - 2)
    (hcoeffSeam : left.coeff (M + 1) = right.coeff (M + 1))
    (hleftSeam : left.bit (M + 1) = 1)
    (hrightSeam : right.bit (M + 1) = 0)
    (hcoeffOverlap : ∀ j < 2 * N - M - 1,
      left.coeff (M + 2 + j) = right.coeff (M + 2 + j))
    (hbitOverlap : ∀ j < 2 * N - M - 1,
      left.bit (M + 2 + j) = right.bit (M + 2 + j))
    (hleftNonneg : 0 ≤ left.carry (2 * N + 1))
    (hrightNonneg : 0 ≤ right.carry (2 * N + 1))
    (hleftBound : (left.carry (2 * N + 1) : ℝ) ≤ bound)
    (hrightBound : (right.carry (2 * N + 1) : ℝ) ≤ bound) :
    (2 : ℝ) ^ (2 * N - M - 1) ≤ bound := by
  apply twoPow_le_realBound_of_carryDifference_eq_twoPow_mul_odd
    left right (2 * N + 1) (2 * N - M - 1) bound
  · exact overlappingMidpointReturns_carryDifference_eq_twoPow_mul_odd
      left right N M hN hNM hcoeffSeam hleftSeam hrightSeam
      hcoeffOverlap hbitOverlap
  · exact hleftNonneg
  · exact hrightNonneg
  · exact hleftBound
  · exact hrightBound

#print axioms relationInvariantLinearChannels_det_eq_zero
#print axioms overlappingReverseCarryWords_carryDifference_eq_twoPow_mul_odd
#print axioms overlappingReverseCarryWords_twoPow_le_realBound
#print axioms overlappingMidpointReturns_carryDifference_eq_twoPow_mul_odd
#print axioms overlappingMidpointReturns_twoPow_le_realBound

end Erdos249257.HalfTrappingReturnCarry
