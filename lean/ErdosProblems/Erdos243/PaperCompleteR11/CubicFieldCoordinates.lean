import Mathlib.RingTheory.PowerBasis
import ErdosProblems.Erdos243.PaperCompleteR11.CubicSquareCoordinates

/-!
# Extracting the square-root coordinates from a cubic algebra

The power-basis representation is extracted from the actual square root.
The degree bound then forces all three rational coordinate equations.
No trace, norm, coordinate equation, or coefficient relation is assumed.
-/

namespace ErdosProblems.Erdos243.PaperCompleteR11

open Polynomial
open scoped BigOperators

noncomputable section

def cubicScalePolynomial (η : ℚ) : ℚ[X] := X^3 - X + C η

theorem cubicScalePolynomial_natDegree (η : ℚ) :
    (cubicScalePolynomial η).natDegree = 3 := by
  dsimp [cubicScalePolynomial]
  compute_degree
  exact one_ne_zero

theorem cubicScalePolynomial_monic (η : ℚ) :
    (cubicScalePolynomial η).Monic := by
  change (cubicScalePolynomial η).coeff (cubicScalePolynomial η).natDegree = 1
  rw [cubicScalePolynomial_natDegree]
  norm_num [cubicScalePolynomial, Polynomial.coeff_X]

/-- Every element of an actual three-dimensional power-basis algebra has
three rational coordinates; the coefficients come from its representative. -/
theorem cubic_powerBasis_representation
    {K : Type*} [CommRing K] [Nontrivial K] [Algebra ℚ K]
    (pb : PowerBasis ℚ K) (hdim : pb.dim = 3) (β : K) :
    ∃ x y z : ℚ,
      β = algebraMap ℚ K x * pb.gen^2 + algebraMap ℚ K y * pb.gen +
        algebraMap ℚ K z := by
  obtain ⟨p, hp, hβ⟩ := pb.exists_eq_aeval β
  have hp3 : p.natDegree < 3 := by omega
  refine ⟨p.coeff 2, p.coeff 1, p.coeff 0, ?_⟩
  rw [hβ, Polynomial.aeval_eq_sum_range' hp3]
  simp [Finset.sum_range_succ, Algebra.smul_def]
  ring

/-- Coefficient extraction from the field square identity, with all
coordinates constructed and the vanishing coefficients proved. -/
theorem cubic_powerBasis_square_coordinates
    {K : Type*} [CommRing K] [Nontrivial K] [Algebra ℚ K]
    (pb : PowerBasis ℚ K) (hdim : pb.dim = 3) (η : ℚ)
    (hroot : pb.gen^3 = pb.gen - algebraMap ℚ K η)
    (β : K) (hsquare : β^2 = pb.gen^2 - 1) :
    ∃ x y z : ℚ,
      β = algebraMap ℚ K x * pb.gen^2 + algebraMap ℚ K y * pb.gen +
        algebraMap ℚ K z ∧
      x^2 + 2*x*z + y^2 - 1 = 0 ∧
      2*x*y + 2*y*z - η*x^2 = 0 ∧
      z^2 - 2*η*x*y + 1 = 0 := by
  obtain ⟨x, y, z, hβ⟩ := cubic_powerBasis_representation pb hdim β
  let q : ℚ[X] := C (x^2 + 2*x*z + y^2 - 1 : ℚ) * X^2 +
    C (2*x*y + 2*y*z - η*x^2 : ℚ) * X + C (z^2 - 2*η*x*y + 1 : ℚ)
  have hqeval : aeval pb.gen q = 0 := by
    simp only [q, map_add, map_sub, map_mul, map_pow, map_one, map_ofNat,
      Polynomial.aeval_C, Polynomial.aeval_X]
    rw [hβ] at hsquare
    linear_combination hsquare -
      ((algebraMap ℚ K x)^2 * pb.gen +
        2 * algebraMap ℚ K x * algebraMap ℚ K y) * hroot
  have hqdeg : q.natDegree ≤ 2 := by
    dsimp [q]
    compute_degree
  have hq : q = 0 := by
    by_contra hq
    have h := pb.dim_le_natDegree_of_root hq hqeval
    omega
  have h1 := congrArg (fun f : ℚ[X] => f.coeff 2) hq
  have h2 := congrArg (fun f : ℚ[X] => f.coeff 1) hq
  have h3 := congrArg (fun f : ℚ[X] => f.coeff 0) hq
  have h1' : x^2 + 2*x*z + y^2 - 1 = 0 := by
    simpa only [q, coeff_add, coeff_C_mul_X_pow, coeff_C_mul_X, coeff_C, coeff_zero, ite_true, ite_false, show (2 : ℕ) ≠ 1 by decide, show (2 : ℕ) ≠ 0 by decide, add_zero] using h1
  have h2' : 2*x*y + 2*y*z - η*x^2 = 0 := by
    simpa only [q, coeff_add, coeff_C_mul_X_pow, coeff_C_mul_X, coeff_C, coeff_zero, ite_true, ite_false, show (1 : ℕ) ≠ 2 by decide, show (1 : ℕ) ≠ 0 by decide, zero_add, add_zero] using h2
  have h3' : z^2 - 2*η*x*y + 1 = 0 := by
    simpa only [q, coeff_add, coeff_C_mul_X_pow, coeff_C_mul_X, coeff_C, coeff_zero, ite_true, ite_false, show (0 : ℕ) ≠ 2 by decide, show (0 : ℕ) ≠ 1 by decide, zero_add] using h3
  exact ⟨x, y, z, hβ, h1', h2', h3'⟩

/-- The two rational parameter relations now follow from an actual square
root in a cubic algebra, rather than from a coordinate supplier. -/
theorem cubic_powerBasis_square_parameter
    {K : Type*} [CommRing K] [Nontrivial K] [Algebra ℚ K]
    (pb : PowerBasis ℚ K) (hdim : pb.dim = 3) (η : ℚ)
    (hroot : pb.gen^3 = pb.gen - algebraMap ℚ K η)
    (hsquare : ∃ β : K, β^2 = pb.gen^2 - 1) :
    ∃ w : ℚ, w ≠ 0 ∧
      ((w^2 + 1)^2 = 8*η*w^3 ∨ (w^2 + 1)^2 = 8*η*w) := by
  obtain ⟨β, hβ⟩ := hsquare
  obtain ⟨x, y, z, _, h1, h2, h3⟩ :=
    cubic_powerBasis_square_coordinates pb hdim η hroot β hβ
  exact ⟨cubicCoordinateW x y z η,
    cubic_coordinate_parameter_ne_zero x y z η h1 h2 h3,
    cubic_coordinate_scale_relations x y z η h1 h2 h3⟩

end
#print axioms cubicScalePolynomial_natDegree
#print axioms cubicScalePolynomial_monic
#print axioms cubic_powerBasis_representation
#print axioms cubic_powerBasis_square_coordinates
#print axioms cubic_powerBasis_square_parameter

end ErdosProblems.Erdos243.PaperCompleteR11
