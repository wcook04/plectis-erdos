import Erdos249257.MersenneLambertLadder
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# Periodic Mersenne tail atoms

This module gives the primitive-conductor Lambert expansion its pointed
coordinates.  The atom of conductor `d` at tail index `N` is

`ω_d(N) = 2^(N mod d) / (2^d - 1)`.

The first theorem records the exact carry step.  The matrix theorems then
make the finite exterior boundary explicit: after clearing the one Mersenne
denominator attached to each column, every minor is an integer determinant.
Consequently a nonzero cleared minor has absolute value at least one.  This is
a no-go for obtaining a small nonzero integer from finite atom denominators
alone; it is not an irrationality theorem for the totient series.
-/

namespace Erdos249257

/-- The periodic tail atom of positive conductor `d` at index `N`. -/
noncomputable def mersenneTailAtom (d : ℕ+) (N : ℕ) : ℚ :=
  (2 : ℚ) ^ (N % (d : ℕ)) / ((2 : ℚ) ^ (d : ℕ) - 1)

/-- A periodic atom advances by doubling except at its unique wrap point,
where the Mersenne numerator contributes exactly one carry. -/
theorem mersenneTailAtom_step (d : ℕ+) (N : ℕ) :
    2 * mersenneTailAtom d N - mersenneTailAtom d (N + 1) =
      if (d : ℕ) ∣ N + 1 then 1 else 0 := by
  have hd : 0 < (d : ℕ) := d.pos
  by_cases hd1 : (d : ℕ) = 1
  · norm_num [mersenneTailAtom, hd1, Nat.mod_one]
  have hdgt : 1 < (d : ℕ) := lt_of_le_of_ne hd (Ne.symm hd1)
  have hone : 1 % (d : ℕ) = 1 := Nat.mod_eq_of_lt hdgt
  have hsuccmod : (N + 1) % (d : ℕ) = (N % (d : ℕ) + 1) % (d : ℕ) := by
    rw [Nat.add_mod, hone]
  by_cases hwrap : (d : ℕ) ∣ N + 1
  · have hsucc : (N + 1) % (d : ℕ) = 0 := Nat.mod_eq_zero_of_dvd hwrap
    have hmodlt : N % (d : ℕ) < (d : ℕ) := Nat.mod_lt _ hd
    have hmod : N % (d : ℕ) + 1 = (d : ℕ) := by
      have hdvd : (d : ℕ) ∣ N % (d : ℕ) + 1 := by
        apply Nat.dvd_of_mod_eq_zero
        rw [← hsuccmod]
        exact hsucc
      have hle : (d : ℕ) ≤ N % (d : ℕ) + 1 :=
        Nat.le_of_dvd (by omega) hdvd
      omega
    have hden : (2 : ℚ) ^ (d : ℕ) - 1 ≠ 0 := by
      have : (1 : ℚ) < (2 : ℚ) ^ (d : ℕ) := one_lt_pow₀ (by norm_num) hd.ne'
      linarith
    simp only [if_pos hwrap, mersenneTailAtom, hsucc, pow_zero]
    rw [show N % (d : ℕ) = (d : ℕ) - 1 by omega]
    have hpow : (2 : ℚ) * (2 : ℚ) ^ ((d : ℕ) - 1) = (2 : ℚ) ^ (d : ℕ) := by
      calc
        (2 : ℚ) * (2 : ℚ) ^ ((d : ℕ) - 1) =
            (2 : ℚ) ^ ((d : ℕ) - 1) * 2 := by ring
        _ = (2 : ℚ) ^ (((d : ℕ) - 1) + 1) := (pow_succ _ _).symm
        _ = (2 : ℚ) ^ (d : ℕ) := by congr 1; omega
    field_simp [hden]
    rw [hpow]
  · have hsucc0 : (N + 1) % (d : ℕ) ≠ 0 := by
      intro hzero
      exact hwrap (Nat.dvd_of_mod_eq_zero hzero)
    have hmodlt : N % (d : ℕ) < (d : ℕ) := Nat.mod_lt _ hd
    have hnextlt : N % (d : ℕ) + 1 < (d : ℕ) := by
      have hle : N % (d : ℕ) + 1 ≤ (d : ℕ) := by omega
      apply lt_of_le_of_ne hle
      intro heq
      apply hsucc0
      rw [hsuccmod, heq, Nat.mod_self]
    have hsucc : (N + 1) % (d : ℕ) = N % (d : ℕ) + 1 := by
      rw [hsuccmod, Nat.mod_eq_of_lt hnextlt]
    simp only [if_neg hwrap, mersenneTailAtom, hsucc]
    rw [pow_succ]
    ring

/-- Integer numerator matrix for a finite family of pointed atoms. -/
def mersenneAtomNumeratorMatrix
    {m : ℕ} (d : Fin m → ℕ+) (idx : Fin m → Fin m → ℕ) :
    Matrix (Fin m) (Fin m) ℤ :=
  fun i j => (2 : ℤ) ^ (idx i j % (d j : ℕ))

/-- Rational matrix formed from a finite family of pointed atoms, with one
conductor (and therefore one Mersenne denominator) assigned to each column. -/
noncomputable def mersenneAtomMatrix
    {m : ℕ} (d : Fin m → ℕ+) (idx : Fin m → Fin m → ℕ) :
    Matrix (Fin m) (Fin m) ℚ :=
  fun i j => mersenneTailAtom (d j) (idx i j)

/-- Exact finite atom determinant factorisation.  The numerator is literally
the cast of an integer determinant; all apparent smallness is carried by the
same column denominators that must be cleared to recover integrality. -/
theorem det_mersenneAtomMatrix
    {m : ℕ} (d : Fin m → ℕ+) (idx : Fin m → Fin m → ℕ) :
    Matrix.det (mersenneAtomMatrix d idx) =
      ((Matrix.det (mersenneAtomNumeratorMatrix d idx) : ℤ) : ℚ) /
        ∏ j, ((2 : ℚ) ^ (d j : ℕ) - 1) := by
  have hmatrix : mersenneAtomMatrix d idx = Matrix.of fun i j =>
      (1 / ((2 : ℚ) ^ (d j : ℕ) - 1)) *
        ((mersenneAtomNumeratorMatrix d idx i j : ℤ) : ℚ) := by
    ext i j
    simp only [mersenneAtomMatrix, mersenneTailAtom,
      mersenneAtomNumeratorMatrix, Matrix.of_apply]
    push_cast
    ring
  rw [hmatrix]
  rw [Matrix.det_mul_row]
  have hcast : Matrix.det (fun i j =>
      ((mersenneAtomNumeratorMatrix d idx i j : ℤ) : ℚ)) =
      ((Matrix.det (mersenneAtomNumeratorMatrix d idx) : ℤ) : ℚ) := by
    symm
    simpa only [Matrix.map_apply] using
      (Int.cast_det (R := ℚ) (mersenneAtomNumeratorMatrix d idx))
  rw [hcast]
  simp only [div_eq_mul_inv, one_mul]
  rw [Finset.prod_inv_distrib]
  ring

/-- Clearing the finite Mersenne denominator product recovers the integer
numerator determinant exactly. -/
theorem mersenneAtom_denominatorProduct_mul_det
    {m : ℕ} (d : Fin m → ℕ+) (idx : Fin m → Fin m → ℕ) :
    (∏ j, ((2 : ℚ) ^ (d j : ℕ) - 1)) *
      Matrix.det (mersenneAtomMatrix d idx) =
      ((Matrix.det (mersenneAtomNumeratorMatrix d idx) : ℤ) : ℚ) := by
  rw [det_mersenneAtomMatrix]
  have hne : ∏ j, ((2 : ℚ) ^ (d j : ℕ) - 1) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro j _
    have hj : (1 : ℚ) < (2 : ℚ) ^ (d j : ℕ) :=
      one_lt_pow₀ (by norm_num) (d j).pos.ne'
    linarith
  field_simp

/-- Height-tight finite-atom boundary: a nonzero numerator determinant gives
a cleared rational minor whose absolute value is at least one. -/
theorem one_le_abs_mersenneAtom_cleared_det
    {m : ℕ} (d : Fin m → ℕ+) (idx : Fin m → Fin m → ℕ)
    (hdet : Matrix.det (mersenneAtomNumeratorMatrix d idx) ≠ 0) :
    (1 : ℚ) ≤
      |(∏ j, ((2 : ℚ) ^ (d j : ℕ) - 1)) *
        Matrix.det (mersenneAtomMatrix d idx)| := by
  rw [mersenneAtom_denominatorProduct_mul_det]
  rw [← Int.cast_abs, ← Int.cast_one, Int.cast_le]
  exact Int.one_le_abs hdet

/-- Column-weighted atom matrix.  In the totient application the weights are
`v * A(d_j)`, hence integers supplied by the rationality multiplier and the
primitive-conductor arithmetic. -/
noncomputable def weightedMersenneAtomMatrix
    {m : ℕ} (d : Fin m → ℕ+) (idx : Fin m → Fin m → ℕ)
    (w : Fin m → ℤ) : Matrix (Fin m) (Fin m) ℚ :=
  fun i j => (w j : ℚ) * mersenneTailAtom (d j) (idx i j)

/-- Integer weights do not create an extra height surplus: after the same
Mersenne clearing, they multiply the integer numerator determinant. -/
theorem weightedMersenneAtom_denominatorProduct_mul_det
    {m : ℕ} (d : Fin m → ℕ+) (idx : Fin m → Fin m → ℕ)
    (w : Fin m → ℤ) :
    (∏ j, ((2 : ℚ) ^ (d j : ℕ) - 1)) *
        Matrix.det (weightedMersenneAtomMatrix d idx w) =
      ((Matrix.det (mersenneAtomNumeratorMatrix d idx) * ∏ j, w j : ℤ) : ℚ) := by
  change (∏ j, ((2 : ℚ) ^ (d j : ℕ) - 1)) *
      Matrix.det (Matrix.of fun i j => (w j : ℚ) * mersenneAtomMatrix d idx i j) = _
  rw [Matrix.det_mul_row]
  calc
    (∏ j, ((2 : ℚ) ^ (d j : ℕ) - 1)) *
          ((∏ j, (w j : ℚ)) * Matrix.det (mersenneAtomMatrix d idx)) =
        (∏ j, (w j : ℚ)) *
          ((∏ j, ((2 : ℚ) ^ (d j : ℕ) - 1)) *
            Matrix.det (mersenneAtomMatrix d idx)) := by ring
    _ = (∏ j, (w j : ℚ)) *
          ((Matrix.det (mersenneAtomNumeratorMatrix d idx) : ℤ) : ℚ) := by
        rw [mersenneAtom_denominatorProduct_mul_det]
    _ = ((Matrix.det (mersenneAtomNumeratorMatrix d idx) * ∏ j, w j : ℤ) : ℚ) := by
        push_cast
        ring

/-- Weighted height-tight boundary in absolute-value form. -/
theorem one_le_abs_weightedMersenneAtom_cleared_det
    {m : ℕ} (d : Fin m → ℕ+) (idx : Fin m → Fin m → ℕ)
    (w : Fin m → ℤ)
    (hdet : Matrix.det (mersenneAtomNumeratorMatrix d idx) * ∏ j, w j ≠ 0) :
    (1 : ℚ) ≤
      |(∏ j, ((2 : ℚ) ^ (d j : ℕ) - 1)) *
        Matrix.det (weightedMersenneAtomMatrix d idx w)| := by
  rw [weightedMersenneAtom_denominatorProduct_mul_det]
  rw [← Int.cast_abs, ← Int.cast_one, Int.cast_le]
  exact Int.one_le_abs hdet

#print axioms mersenneTailAtom_step
#print axioms det_mersenneAtomMatrix
#print axioms one_le_abs_weightedMersenneAtom_cleared_det

end Erdos249257
