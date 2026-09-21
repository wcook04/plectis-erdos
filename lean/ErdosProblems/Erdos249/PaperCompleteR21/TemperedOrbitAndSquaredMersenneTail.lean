import Erdos249257.GenericTailOrbitRigidity
import Erdos249257.SquaredMersenneDiagonalEnclosure

/-! Paper-form restatements of three long-paper statements about the doubling
orbit and the squared-Mersenne remainder:

* *Uniqueness under the growth condition* — a real sequence with
  `d(N+1) = 2 d(N)` and `d(N) = o(2^N)` is identically zero;
* *An exact rational approximation formula* — the residual left in
  `R_{2H} - R_H` by the exactly summed first-order Lambert term;
* *A geometric tail bound* — `|∑_{d>D} μ(d)/(2^d-1)^2| ≤ 4/(3(2^{D+1}-1)^2)`,
  together with the two elementary facts the paper cites for it.

Here `R_N = totientTail N` and `Φ_N = totientPrefix N`. -/
namespace ErdosProblems.Erdos249.PaperCompleteR21

open scoped BigOperators
open Erdos249257
open Erdos249257.TotientTailPeriodKiller
open Erdos249257.FullTargetPrimeAdjunctionNoGo
open Erdos249257.SquaredMersenneDiagonalEnclosure

/-! ### Uniqueness under the growth condition -/

/-- **Uniqueness under the growth condition.**  A real sequence `d` with
`d(N+1) = 2 d(N)` and `d(N) = o(2^N)` is identically zero.  The growth
condition is transcribed as `d N / 2^N → 0`. -/
theorem doubling_tempered_sequence_eq_zero
    (d : ℕ → ℝ) (hrec : ∀ N : ℕ, d (N + 1) = 2 * d N)
    (hlittleO :
      Filter.Tendsto (fun N : ℕ ↦ d N / (2 : ℝ) ^ N) Filter.atTop (nhds 0)) :
    ∀ N : ℕ, d N = 0 :=
  Erdos249257.doublingOrbit_eq_zero_of_tempered d hrec hlittleO

/-! ### An exact rational approximation formula -/

private theorem sum_Icc_one_eq_sum_range {M : Type*} [AddCommMonoid M]
    (D : ℕ) (f : ℕ → M) :
    ∑ d ∈ Finset.Icc 1 D, f d = ∑ k ∈ Finset.range D, f (k + 1) := by
  induction D with
  | zero => simp
  | succ D ih =>
      rw [Finset.sum_range_succ, ← ih, Finset.sum_Icc_succ_top (by omega)]

private theorem diagonalCoefficient_cast (H : ℕ) :
    ((diagonalCoefficient H : ℕ) : ℝ) = (2 : ℝ) ^ H * ((2 : ℝ) ^ H - 1) := by
  have h1 : (1 : ℕ) ≤ 2 ^ H := Nat.one_le_pow H 2 (by norm_num)
  rw [diagonalCoefficient, Nat.cast_mul, Nat.cast_sub h1]
  push_cast
  ring

private theorem diagonalPrefixCorrection_cast (H : ℕ) :
    ((diagonalPrefixCorrection H : ℤ) : ℝ) =
      ((totientPrefix H : ℕ) : ℝ) - ((totientPrefix (2 * H) : ℕ) : ℝ) := by
  rw [diagonalPrefixCorrection]
  push_cast
  ring

private theorem mobiusSquarePartialRat_cast (D : ℕ) :
    ((mobiusSquarePartialRat D : ℚ) : ℝ) =
      1 / 2 +
        ∑ d ∈ Finset.Icc 1 D,
          ((ArithmeticFunction.moebius d : ℤ) : ℝ) / (((2 : ℝ) ^ d - 1) ^ 2) := by
  rw [sum_Icc_one_eq_sum_range, mobiusSquarePartialRat]
  push_cast
  ring

private theorem lambertProjectedDiagonal_paper (H D : ℕ) :
    lambertProjectedDiagonal H D =
      ((totientPrefix H : ℕ) : ℝ) - ((totientPrefix (2 * H) : ℕ) : ℝ) +
        (2 : ℝ) ^ H * ((2 : ℝ) ^ H - 1) *
          (1 / 2 +
            ∑ d ∈ Finset.Icc 1 D,
              ((ArithmeticFunction.moebius d : ℤ) : ℝ) /
                (((2 : ℝ) ^ d - 1) ^ 2)) := by
  have h1 : lambertProjectedDiagonal H D =
      ((diagonalPrefixCorrection H : ℤ) : ℝ) +
        ((diagonalCoefficient H : ℕ) : ℝ) *
          ((mobiusSquarePartialRat D : ℚ) : ℝ) := by
    rw [lambertProjectedDiagonal, lambertProjectedDiagonalRat]
    push_cast
    ring
  rw [h1, diagonalPrefixCorrection_cast, diagonalCoefficient_cast,
    mobiusSquarePartialRat_cast]

/-- The exact generic-scale identity the squared-denominator formula is
substituted into: `R_{2H} - R_H = 2^H(2^H-1) S + Φ_H - Φ_{2H}`. -/
theorem tailDifference_eq_coefficient_mul_series (H : ℕ) :
    totientTail (2 * H) - totientTail H =
      (2 : ℝ) ^ H * ((2 : ℝ) ^ H - 1) *
          (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) +
        (((totientPrefix H : ℕ) : ℝ) - ((totientPrefix (2 * H) : ℕ) : ℝ)) := by
  have h := scaleDiagonalTailDifference_eq H
  rw [scaleDiagonalTailDifference, diagonalCoefficient_cast,
    diagonalPrefixCorrection_cast, totientSeries] at h
  exact h

/-- The `ℕ+` display of `S` used by the squared-denominator identity. -/
theorem totientSeries_pnat_form :
    (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) =
      ∑' n : ℕ+, (Nat.totient (n : ℕ) : ℝ) * ((1 : ℝ) / 2) ^ (n : ℕ) := by
  have h := totientSeries_eq_pnat_half_pow
  rwa [totientSeries] at h

/-- The squared-denominator identity for `S`. -/
theorem totientSeries_eq_half_add_moebius_sq :
    (∑' n : ℕ+, (Nat.totient (n : ℕ) : ℝ) * ((1 : ℝ) / 2) ^ (n : ℕ)) =
      1 / 2 +
        ∑' d : ℕ+,
          ((ArithmeticFunction.moebius (d : ℕ) : ℤ) : ℝ) /
            (((2 : ℝ) ^ (d : ℕ) - 1) ^ 2) :=
  MersenneLambertLadder.tsum_totient_half_pow_eq_half_add_moebius_sq

/-- **An exact rational approximation formula.**  For all integers `H, D ≥ 0`,
`R_{2H} - R_H - [Φ_H - Φ_{2H} + 2^H(2^H-1)(1/2 + ∑_{d=1}^{D} μ(d)/(2^d-1)^2)]
= 2^H(2^H-1) ∑_{d>D} μ(d)/(2^d-1)^2`.  No ordering between `D` and `H` is
required. -/
theorem tailDifference_sub_rationalApproximation (H D : ℕ) :
    totientTail (2 * H) - totientTail H -
        (((totientPrefix H : ℕ) : ℝ) - ((totientPrefix (2 * H) : ℕ) : ℝ) +
          (2 : ℝ) ^ H * ((2 : ℝ) ^ H - 1) *
            (1 / 2 +
              ∑ d ∈ Finset.Icc 1 D,
                ((ArithmeticFunction.moebius d : ℤ) : ℝ) /
                  (((2 : ℝ) ^ d - 1) ^ 2))) =
      (2 : ℝ) ^ H * ((2 : ℝ) ^ H - 1) *
        ∑' k : ℕ,
          ((ArithmeticFunction.moebius (D + 1 + k) : ℤ) : ℝ) /
            (((2 : ℝ) ^ (D + 1 + k) - 1) ^ 2) := by
  have hkey := scaleDiagonalTailDifference_sub_lambertProjectedDiagonal H D
  rw [lambertProjectedDiagonal_paper, diagonalCoefficient_cast,
    scaleDiagonalTailDifference, mobiusSquareTail] at hkey
  exact hkey

/-! ### A geometric tail bound -/

/-- Every Möbius value has absolute value at most one. -/
theorem abs_moebius_cast_le_one (d : ℕ) :
    |((ArithmeticFunction.moebius d : ℤ) : ℝ)| ≤ 1 := by
  rw [← Int.cast_abs]
  exact_mod_cast MersenneLambertLadder.abs_moebius_le_one d

/-- `2^(D+1+j) - 1 ≥ 2^j (2^(D+1) - 1)` for every `j ≥ 0`. -/
theorem mersenne_geometric_shift (D j : ℕ) :
    (2 : ℝ) ^ j * ((2 : ℝ) ^ (D + 1) - 1) ≤ (2 : ℝ) ^ (D + 1 + j) - 1 :=
  mersenne_shift_lower_bound D j

/-- The geometric majorant sums to `4/3`. -/
theorem tsum_quarter_geometric : ∑' j : ℕ, ((1 : ℝ) / 4) ^ j = 4 / 3 := by
  rw [tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
  norm_num

/-- **A geometric tail bound.**  For every integer `D ≥ 0`,
`|∑_{d>D} μ(d)/(2^d-1)^2| ≤ 4/(3(2^{D+1}-1)^2)`. -/
theorem abs_mobiusSquareTail_le_paper (D : ℕ) :
    |∑' k : ℕ,
        ((ArithmeticFunction.moebius (D + 1 + k) : ℤ) : ℝ) /
          (((2 : ℝ) ^ (D + 1 + k) - 1) ^ 2)| ≤
      4 / (3 * (((2 : ℝ) ^ (D + 1) - 1) ^ 2)) := by
  have h := abs_mobiusSquareTail_le D
  rwa [mobiusSquareTail] at h

end ErdosProblems.Erdos249.PaperCompleteR21

#print axioms ErdosProblems.Erdos249.PaperCompleteR21.doubling_tempered_sequence_eq_zero
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.tailDifference_eq_coefficient_mul_series
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.totientSeries_pnat_form
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.totientSeries_eq_half_add_moebius_sq
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.tailDifference_sub_rationalApproximation
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.abs_moebius_cast_le_one
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.mersenne_geometric_shift
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.tsum_quarter_geometric
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.abs_mobiusSquareTail_le_paper
