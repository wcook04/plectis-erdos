import Erdos249257.AdelicHeightObstruction
import Erdos249257.ResidualGaugeObstruction

/-! Paper-form restatements of two long-paper environments about the cost of
clearing a denominator and about column gauges on a monomial minor:

* "Complement divisibility after multiplication": for `x = a/b` in lowest
  terms, `c ∈ ℤ` and a positive divisor `H` of `b`, if the reduced denominator
  of `c·x` divides `H` then `b/H ∣ c`.
* "A nonzero minor survives inverse-phase column weights": for `P_{ij} =
  z_j^{e_i}` with every `z_j ≠ 0` and `e_{i₀} = 1`, the right diagonal gauge
  `W_j = z_j⁻¹` makes row `i₀` identically `1`, multiplies the determinant by
  `∏_j z_j⁻¹`, preserves nonvanishing, and preserves the modulus when every
  `|z_j| = 1`.

The content is carried by `Erdos249257.AdelicHeightObstruction` and
`Erdos249257.ResidualGaugeObstruction`. -/
namespace ErdosProblems.Erdos249.PaperCompleteR21

open Erdos249257
open Erdos249257.ResidualGaugeObstruction

/-! ### Complement divisibility after multiplication -/

/-- **Complement divisibility after multiplication.**  Write `x = a/b` in
lowest terms with `a = x.num ∈ ℤ` and `b = x.den ≥ 1`.  Let `c ∈ ℤ` and let `H`
be a positive divisor of `b`.  If the reduced denominator of `c·x` divides `H`,
then `b/H ∣ c`. -/
theorem complementDenominator_dvd_scalar
    (x : ℚ) (c : ℤ) {H : ℕ} (_hHpos : 0 < H) (hH : H ∣ x.den)
    (hscaled : ((c : ℚ) * x).den ∣ H) :
    ((x.den / H : ℕ) : ℤ) ∣ c := by
  have hnat : x.den / H ∣ c.natAbs :=
    Erdos249257.AdelicHeightObstruction.scalarLocalization_complement_dvd x c hH hscaled
  have hcast : ((x.den / H : ℕ) : ℤ) ∣ ((c.natAbs : ℕ) : ℤ) :=
    Int.natCast_dvd_natCast.mpr hnat
  exact Int.dvd_natAbs.mp hcast

/-! ### A nonzero minor survives inverse-phase column weights -/

/-- **A nonzero minor survives inverse-phase column weights.**  Let `d ≥ 1`,
let `e₀,…,e_{d-1}` be natural numbers, let `z₀,…,z_{d-1}` be nonzero complex
numbers and put `P_{ij} = z_j^{e_i}`.  Assume `e_{i₀} = 1`.  Multiplying column
`j` by `W_j = z_j⁻¹` gives

* `(P·diag W)_{i₀ j} = 1` for every `j`;
* `det (P·diag W) = det P · ∏_j z_j⁻¹`;

hence a nonzero `det P` stays nonzero while row `i₀` is constant, and if every
`‖z_j‖ = 1` the modulus of the determinant is unchanged as well. -/
theorem inversePhaseGauge_locks_row_and_preserves_minor
    {d : ℕ} (_hd : 1 ≤ d) (e : Fin d → ℕ) (z : Fin d → ℂ)
    (hz : ∀ j, z j ≠ 0) (i₀ : Fin d) (hi₀ : e i₀ = 1) :
    (∀ j, (phasePowerMatrix e z * Matrix.diagonal (fun j => (z j)⁻¹)) i₀ j = 1) ∧
      Matrix.det (phasePowerMatrix e z * Matrix.diagonal (fun j => (z j)⁻¹))
          = Matrix.det (phasePowerMatrix e z) * ∏ j, (z j)⁻¹ ∧
      (Matrix.det (phasePowerMatrix e z) ≠ 0 →
        Matrix.det (phasePowerMatrix e z * Matrix.diagonal (fun j => (z j)⁻¹)) ≠ 0) ∧
      ((∀ j, ‖z j‖ = 1) →
        ‖Matrix.det (phasePowerMatrix e z * Matrix.diagonal (fun j => (z j)⁻¹))‖
          = ‖Matrix.det (phasePowerMatrix e z)‖) := by
  have hgauge :
      phasePowerMatrix e z * Matrix.diagonal (fun j => (z j)⁻¹)
        = residualMonomialMatrix e (lockedResidual z) z :=
    (residualMonomialMatrix_eq_mul_diagonal e (lockedResidual z) z).symm
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro j
    rw [hgauge]
    exact residualMonomialMatrix_locked_row_one e z i₀ hi₀ hz j
  · rw [hgauge]
    exact det_residualMonomialMatrix e (lockedResidual z) z
  · intro hdet
    rw [hgauge]
    exact (locked_reconstruction_preserves_nonzero_minor e z i₀ hi₀ hz hdet).1
  · intro hunit
    rw [hgauge]
    exact norm_det_residualMonomialMatrix e (lockedResidual z) z
      (norm_lockedResidual z hunit)

end ErdosProblems.Erdos249.PaperCompleteR21

#print axioms ErdosProblems.Erdos249.PaperCompleteR21.complementDenominator_dvd_scalar
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.inversePhaseGauge_locks_row_and_preserves_minor
