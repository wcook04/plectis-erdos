import Erdos249257.MersenneLambertLadder
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Finite incidence-quotient rigidity for Erdős #249

This module isolates the exact finite algebra behind the Möbius-companion
proposal.  At jet horizon `N`, the coefficient of `q^(i+1)` in the companion
`M_mu(q^(j+1))` is `mu ((i+1)/(j+1))` when `(j+1) ∣ (i+1)`.  The resulting
matrix is lower triangular with diagonal `1`, hence has determinant `1` over
`ℤ`.  It is therefore an integral change of basis, not a rank reduction.

The scope is deliberately finite and exact.  The stronger global claim that
`1`, the totient series, and finitely many Möbius dilates are linearly
independent over `ℚ(q)` needs separate analytic-number-theory input and is not
claimed here.  No irrationality statement for Erdős #249 follows.
-/

namespace IncidenceQuotientHermitePade

open ArithmeticFunction

/-- Coefficient of `q^n` in the Möbius companion `M_mu(q^r)`. -/
def mobiusCompanionCoeff (r n : ℕ) : ℤ :=
  if r ∣ n then moebius (n / r) else 0

/-- The finite Möbius-incidence matrix on the positive jet coordinates
`q, q^2, ..., q^N`.  Columns are companion jets. -/
def incidenceMobiusMatrix (N : ℕ) : Matrix (Fin N) (Fin N) ℤ :=
  fun i j => mobiusCompanionCoeff (j.val + 1) (i.val + 1)

@[simp] theorem incidenceMobiusMatrix_apply (N : ℕ) (i j : Fin N) :
    incidenceMobiusMatrix N i j =
      if j.val + 1 ∣ i.val + 1 then moebius ((i.val + 1) / (j.val + 1)) else 0 :=
  rfl

@[simp] theorem incidenceMobiusMatrix_diagonal (N : ℕ) (i : Fin N) :
    incidenceMobiusMatrix N i i = 1 := by
  simp [incidenceMobiusMatrix, mobiusCompanionCoeff]

/-- The companion coefficient matrix has no entries strictly above the
diagonal. -/
theorem incidenceMobiusMatrix_lowerTriangular (N : ℕ) :
    (incidenceMobiusMatrix N).BlockTriangular OrderDual.toDual := by
  intro i j hji
  change i < j at hji
  rw [incidenceMobiusMatrix_apply, if_neg]
  intro hdvd
  have hle : j.val + 1 ≤ i.val + 1 :=
    Nat.le_of_dvd (Nat.succ_pos i.val) hdvd
  omega

/-- **Finite incidence unimodularity.**  Möbius incidence is an integral
change of basis on every positive jet space. -/
theorem incidenceMobius_det_eq_one (N : ℕ) :
    Matrix.det (incidenceMobiusMatrix N) = 1 := by
  rw [Matrix.det_of_lowerTriangular _ (incidenceMobiusMatrix_lowerTriangular N)]
  simp

/-- The finite incidence matrix is a unit over `ℤ`; in particular its inverse
also has integer entries. -/
theorem incidenceMobius_isUnit (N : ℕ) : IsUnit (incidenceMobiusMatrix N) := by
  rw [Matrix.isUnit_iff_isUnit_det, incidenceMobius_det_eq_one]
  exact isUnit_one

/-- Companion jets are linearly independent over `ℤ`. -/
theorem mobiusCompanionJet_linearIndependent (N : ℕ) :
    LinearIndependent ℤ (incidenceMobiusMatrix N).col := by
  exact Matrix.linearIndependent_cols_of_det_ne_zero (by
    rw [incidenceMobius_det_eq_one]
    norm_num)

/-- The evaluated finite companion family has zero kernel.  This is the exact
finite no-compression statement needed to reject a non-trivial incidence
quotient at jet horizon `N`. -/
theorem mobiusCompanionJetMap_injective (N : ℕ) :
    Function.Injective (incidenceMobiusMatrix N).mulVec :=
  Matrix.mulVec_injective_iff.mpr (mobiusCompanionJet_linearIndependent N)

theorem mobiusCompanionJetMap_eq_zero_iff (N : ℕ) (c : Fin N → ℤ) :
    (incidenceMobiusMatrix N).mulVec c = 0 ↔ c = 0 := by
  constructor
  · intro h
    exact mobiusCompanionJetMap_injective N (h.trans (Matrix.mulVec_zero _).symm)
  · rintro rfl
    exact Matrix.mulVec_zero _

/-- A finite incidence-quotient relation is a coefficient vector whose actual
companion jet evaluates to zero.  The definition builds evaluation
compatibility into the named class. -/
def IsFiniteIncidenceQuotientRelation (N : ℕ) (c : Fin N → ℤ) : Prop :=
  (incidenceMobiusMatrix N).mulVec c = 0

/-- **Finite incidence-quotient non-compression.**  The named class has only
the zero relation at every horizon. -/
theorem finiteIncidenceQuotientRelation_iff (N : ℕ) (c : Fin N → ℤ) :
    IsFiniteIncidenceQuotientRelation N c ↔ c = 0 :=
  mobiusCompanionJetMap_eq_zero_iff N c

end IncidenceQuotientHermitePade
