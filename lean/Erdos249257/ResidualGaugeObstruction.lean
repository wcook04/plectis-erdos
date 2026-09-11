import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

/-!
# Residual-gauge obstruction for monomial minors

A common residual weight multiplies each supplier column by a nonzero scalar.
Consequently determinant nonvanishing of a residual-weighted monomial matrix
cannot see whether the exponent-one row reconstructs the distinguished phase
`1`.  The results below make that all-rank obstruction exact.

This rules out residual-blind rank, determinant, and conditioning criteria as
standalone first-harmonic certificates.  It does not rule out determinants
whose rows satisfy an additional arithmetic coupling identity.
-/

namespace Erdos249257
namespace ResidualGaugeObstruction

open scoped BigOperators

/-- The coefficient-side monomial matrix before residual column scaling. -/
def phasePowerMatrix
    {d : ℕ} (e : Fin d → ℕ) (z : Fin d → ℂ) :
    Matrix (Fin d) (Fin d) ℂ :=
  fun i j ↦ z j ^ e i

/-- A common residual weight applied to every row of a supplier column. -/
def residualMonomialMatrix
    {d : ℕ} (e : Fin d → ℕ) (W z : Fin d → ℂ) :
    Matrix (Fin d) (Fin d) ℂ :=
  fun i j ↦ W j * z j ^ e i

/-- Common residual weights are exactly a right diagonal gauge action. -/
theorem residualMonomialMatrix_eq_mul_diagonal
    {d : ℕ} (e : Fin d → ℕ) (W z : Fin d → ℂ) :
    residualMonomialMatrix e W z =
      phasePowerMatrix e z * Matrix.diagonal W := by
  classical
  ext i j
  rw [Matrix.mul_diagonal]
  simp [residualMonomialMatrix, phasePowerMatrix, mul_comm]

/-- Determinants factor into the coefficient-side determinant and the
product of residual column gauges. -/
theorem det_residualMonomialMatrix
    {d : ℕ} (e : Fin d → ℕ) (W z : Fin d → ℂ) :
    Matrix.det (residualMonomialMatrix e W z) =
      Matrix.det (phasePowerMatrix e z) * ∏ j, W j := by
  rw [residualMonomialMatrix_eq_mul_diagonal, Matrix.det_mul,
    Matrix.det_diagonal]

/-- Nonzero column gauges preserve determinant nonvanishing at every rank. -/
theorem det_residualMonomialMatrix_ne_zero_iff
    {d : ℕ} (e : Fin d → ℕ) (W z : Fin d → ℂ)
    (hW : ∏ j, W j ≠ 0) :
    Matrix.det (residualMonomialMatrix e W z) ≠ 0 ↔
      Matrix.det (phasePowerMatrix e z) ≠ 0 := by
  rw [det_residualMonomialMatrix]
  exact mul_ne_zero_iff_right hW

/-- Unit residual gauges preserve determinant magnitude. -/
theorem norm_det_residualMonomialMatrix
    {d : ℕ} (e : Fin d → ℕ) (W z : Fin d → ℂ)
    (hW : ∀ j, ‖W j‖ = 1) :
    ‖Matrix.det (residualMonomialMatrix e W z)‖ =
      ‖Matrix.det (phasePowerMatrix e z)‖ := by
  rw [det_residualMonomialMatrix, norm_mul]
  simp [hW]

/-- The locked reconstruction gauge is the inverse pivot phase. -/
noncomputable def lockedResidual {d : ℕ} (z : Fin d → ℂ) : Fin d → ℂ :=
  fun j ↦ (z j)⁻¹

/-- Unit pivot phases give unit locked residuals. -/
theorem norm_lockedResidual
    {d : ℕ} (z : Fin d → ℂ) (hz : ∀ j, ‖z j‖ = 1) :
    ∀ j, ‖lockedResidual z j‖ = 1 := by
  intro j
  simp [lockedResidual, hz j]

/-- Under the locked gauge, any exponent-one row is identically the bad
target phase `1`, while the other rows remain available to carry rank. -/
theorem residualMonomialMatrix_locked_row_one
    {d : ℕ} (e : Fin d → ℕ) (z : Fin d → ℂ) (i : Fin d)
    (hi : e i = 1) (hz : ∀ j, z j ≠ 0) :
    ∀ j, residualMonomialMatrix e (lockedResidual z) z i j = 1 := by
  intro j
  simp [residualMonomialMatrix, lockedResidual, hi, hz j]

/-- The locked bad row and a nonzero coefficient-side determinant coexist.
This is the all-rank countermodel to a residual-blind minor certificate. -/
theorem locked_reconstruction_preserves_nonzero_minor
    {d : ℕ} (e : Fin d → ℕ) (z : Fin d → ℂ) (i : Fin d)
    (hi : e i = 1) (hz : ∀ j, z j ≠ 0)
    (hdet : Matrix.det (phasePowerMatrix e z) ≠ 0) :
    Matrix.det (residualMonomialMatrix e (lockedResidual z) z) ≠ 0 ∧
      ∀ j, residualMonomialMatrix e (lockedResidual z) z i j = 1 := by
  constructor
  · rw [det_residualMonomialMatrix_ne_zero_iff]
    · exact hdet
    · exact Finset.prod_ne_zero_iff.mpr fun j _ ↦ inv_ne_zero (hz j)
  · exact residualMonomialMatrix_locked_row_one e z i hi hz

/-! ## Row-dependent relaxation -/

/-- Monomial rows with a residual allowed to vary across both rows and
columns. -/
def rowResidualMonomialMatrix
    {d : ℕ} (e : Fin d → ℕ) (W : Fin d → Fin d → ℂ)
    (z : Fin d → ℂ) : Matrix (Fin d) (Fin d) ℂ :=
  fun i j ↦ W i j * z j ^ e i

/-- A row-dependent residual can reconstruct the ordinary consecutive-power
matrix for arbitrary requested exponents. -/
noncomputable def rowReconstructingResidual
    {d : ℕ} (e : Fin d → ℕ) (z : Fin d → ℂ) :
    Fin d → Fin d → ℂ :=
  fun i j ↦ z j ^ i.1 / z j ^ e i

/-- The explicit row-dependent residual relaxation reconstructs an ordinary
Vandermonde-shaped consecutive-power matrix exactly. -/
theorem rowResidualMonomialMatrix_reconstructs_phasePowerMatrix
    {d : ℕ} (e : Fin d → ℕ) (z : Fin d → ℂ)
    (hz : ∀ j, z j ≠ 0) :
    rowResidualMonomialMatrix e (rowReconstructingResidual e z) z =
      phasePowerMatrix (fun i : Fin d ↦ i.1) z := by
  ext i j
  simp [rowResidualMonomialMatrix, rowReconstructingResidual,
    phasePowerMatrix, pow_ne_zero _ (hz j)]

/-- When the pivot phases are unit, every entry of the reconstructing
row-dependent residual is also unit. -/
theorem norm_rowReconstructingResidual
    {d : ℕ} (e : Fin d → ℕ) (z : Fin d → ℂ)
    (hz : ∀ j, ‖z j‖ = 1) :
    ∀ i j, ‖rowReconstructingResidual e z i j‖ = 1 := by
  intro i j
  simp [rowReconstructingResidual, norm_pow, hz j]

/-- The reconstructed zeroth row is identically `1`.  Thus even allowing
row-dependent unit residuals does not let a fixed-rank nonzero minor exclude
the locked affine target without an additional arithmetic coupling law. -/
theorem rowReconstruction_zero_row_one
    {d : ℕ} (e : Fin d → ℕ) (z : Fin d → ℂ)
    (hz : ∀ j, z j ≠ 0) (i : Fin d) (hi : i.1 = 0) :
    ∀ j, rowResidualMonomialMatrix e (rowReconstructingResidual e z) z i j = 1 := by
  intro j
  rw [rowResidualMonomialMatrix_reconstructs_phasePowerMatrix e z hz]
  simp [phasePowerMatrix, hi]

#print axioms residualMonomialMatrix_eq_mul_diagonal
#print axioms det_residualMonomialMatrix
#print axioms locked_reconstruction_preserves_nonzero_minor
#print axioms rowResidualMonomialMatrix_reconstructs_phasePowerMatrix
#print axioms rowReconstruction_zero_row_one

end ResidualGaugeObstruction
end Erdos249257
