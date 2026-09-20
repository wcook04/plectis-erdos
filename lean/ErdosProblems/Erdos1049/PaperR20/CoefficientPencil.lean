import ErdosProblems.Erdos1049.QBinomialUnitIdentity
import Mathlib

/-!
# Literal coefficient moments and the finite coefficient pencil

These are the polynomials R_m, s_m, α_m and β_m in the coefficient-moment
section of the #1049 reasoning paper. The polynomial part defining β is
implemented by finite coefficient convolution with the divisor-count sequence.
It is not defined by a remainder identity or by a real floor operation.

The elementary normalizations and diagonal congruence below are candidate
proofs awaiting kernel validation. No finite determinant certificate,
positive-definiteness, spectral root bound or interlacing result is asserted
by this module.
-/

namespace ErdosProblems.Erdos1049.PaperR20

open Polynomial Finset
open scoped BigOperators

noncomputable section

/-- The signed Gaussian-binomial polynomial R_m in the paper. -/
def coefficientRPoly (m : ℕ) : ℤ[X] :=
  ∑ k ∈ range (m + 1),
    C ((-1 : ℤ) ^ (m + k)) * X ^ (k * (k + 1) / 2) *
      gaussBinom X m k * gaussBinom X (m + k) k

/-- The Gaussian factorial [m]_X!; the factors have lengths 1 through m. -/
def coefficientQFactorialPoly (m : ℕ) : ℤ[X] :=
  ∏ j ∈ range m, ∑ i ∈ range (j + 1), X ^ i

/-- The literal coefficient moment s_m = ([m]_X!)³ R_m. -/
def coefficientMomentPoly (m : ℕ) : ℤ[X] :=
  coefficientQFactorialPoly m ^ 3 * coefficientRPoly m

/-- The coefficient α_m = X [X(X − 1)³]^m s_m. -/
def coefficientAlphaPoly (m : ℕ) : ℤ[X] :=
  X * (X * (X - 1) ^ 3) ^ m * coefficientMomentPoly m

/-- Divisor-count coefficients τ(j), with τ(0) = 0. -/
def divisorCount (j : ℕ) : ℤ := (Nat.divisors j).card

/-- Polynomial part at infinity of P(X) ∑_{j≥1} τ(j)X^{-j}.
An input monomial at degree i contributes at precisely the degrees r < i. -/
def lambertPolynomialPart (P : ℤ[X]) : ℤ[X] :=
  ∑ i ∈ range (P.natDegree + 1),
    C (P.coeff i) * ∑ r ∈ range i, C (divisorCount (i - r)) * X ^ r

/-- The paper's exact polynomial normalization β_m = [α_m ∑τ(j)X^{-j}]_+ − 1. -/
def coefficientBetaPoly (m : ℕ) : ℤ[X] :=
  lambertPolynomialPart (coefficientAlphaPoly m) - 1

def coefficientMoment (p : ℝ) (m : ℕ) : ℝ :=
  (coefficientMomentPoly m).eval₂ (Int.castRingHom ℝ) p

def coefficientAlpha (p : ℝ) (m : ℕ) : ℝ :=
  (coefficientAlphaPoly m).eval₂ (Int.castRingHom ℝ) p

def coefficientBeta (p : ℝ) (m : ℕ) : ℝ :=
  (coefficientBetaPoly m).eval₂ (Int.castRingHom ℝ) p

/-- D_{N,h} as the determinant of the literal polynomial Hankel matrix. -/
def coefficientHankelDetPoly (N h : ℕ) : ℤ[X] :=
  Matrix.det (Matrix.of fun i j : Fin N => coefficientMomentPoly (i.val + j.val + h))

def coefficientMomentMatrix (p : ℝ) (N : ℕ) : Matrix (Fin N) (Fin N) ℝ :=
  Matrix.of fun i j => coefficientMoment p (i.val + j.val)

def coefficientAlphaMatrix (p : ℝ) (N : ℕ) : Matrix (Fin N) (Fin N) ℝ :=
  Matrix.of fun i j => coefficientAlpha p (i.val + j.val)

def coefficientBetaMatrix (p : ℝ) (N : ℕ) : Matrix (Fin N) (Fin N) ℝ :=
  Matrix.of fun i j => coefficientBeta p (i.val + j.val)

/-- The determinant polynomial det(Y A_N − B_N), with real coefficients. -/
def coefficientPencilPoly (p : ℝ) (N : ℕ) : ℝ[X] :=
  Matrix.det (Matrix.of fun i j : Fin N =>
    X * C (coefficientAlpha p (i.val + j.val)) -
      C (coefficientBeta p (i.val + j.val)))

def coefficientDiagonal (p : ℝ) (N : ℕ) : Matrix (Fin N) (Fin N) ℝ :=
  Matrix.diagonal fun i => (p * (p - 1) ^ 3) ^ i.val

@[simp] theorem coefficientRPoly_zero : coefficientRPoly 0 = 1 := by
  simp [coefficientRPoly, gaussBinom]

@[simp] theorem coefficientQFactorialPoly_zero : coefficientQFactorialPoly 0 = 1 := by
  simp [coefficientQFactorialPoly]

@[simp] theorem coefficientMomentPoly_zero : coefficientMomentPoly 0 = 1 := by
  simp [coefficientMomentPoly]

@[simp] theorem coefficientAlphaPoly_zero : coefficientAlphaPoly 0 = X := by
  simp [coefficientAlphaPoly]

@[simp] theorem lambertPolynomialPart_X : lambertPolynomialPart X = 1 := by
  norm_num [lambertPolynomialPart, Finset.sum_range_succ, divisorCount]

@[simp] theorem coefficientBetaPoly_zero : coefficientBetaPoly 0 = 0 := by
  simp [coefficientBetaPoly]

theorem coefficientAlpha_factor (p : ℝ) (m : ℕ) :
    coefficientAlpha p m =
      p * (p * (p - 1) ^ 3) ^ m * coefficientMoment p m := by
  simp [coefficientAlpha, coefficientAlphaPoly, coefficientMoment, Polynomial.eval₂_pow]

@[simp] theorem coefficientAlpha_zero (p : ℝ) : coefficientAlpha p 0 = p := by
  simp [coefficientAlpha]

@[simp] theorem coefficientBeta_zero (p : ℝ) : coefficientBeta p 0 = 0 := by
  simp [coefficientBeta]

/-- The congruence uses the same original coordinate spaces at every rank. -/
theorem coefficientAlphaMatrix_diagonal_congruence (p : ℝ) (N : ℕ) :
    coefficientAlphaMatrix p N =
      p • (coefficientDiagonal p N * coefficientMomentMatrix p N *
        coefficientDiagonal p N) := by
  ext i j
  simp only [coefficientAlphaMatrix, coefficientDiagonal, coefficientMomentMatrix,
    Matrix.smul_apply, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.of_apply,
    smul_eq_mul, coefficientAlpha_factor, pow_add]
  ring

theorem coefficientAlphaMatrix_isSymm (p : ℝ) (N : ℕ) :
    (coefficientAlphaMatrix p N).IsSymm := by
  ext i j
  simp [coefficientAlphaMatrix, Nat.add_comm]

theorem coefficientBetaMatrix_isSymm (p : ℝ) (N : ℕ) :
    (coefficientBetaMatrix p N).IsSymm := by
  ext i j
  simp [coefficientBetaMatrix, Nat.add_comm]

theorem coefficientDiagonal_entry_pos {p : ℝ} (hp : 1 < p) (i : ℕ) :
    0 < (p * (p - 1) ^ 3) ^ i := by
  have hp0 : 0 < p := lt_trans zero_lt_one hp
  exact pow_pos (mul_pos hp0 (pow_pos (sub_pos.mpr hp) 3)) i

/-- A coefficient certificate is used only after an equality with the literal
determinant polynomial has been proved. The constant coefficient makes this
bound strict even at the polynomial endpoint p = 1. -/
theorem eval₂_pos_of_nonneg_coeff (P : ℤ[X]) {x : ℝ} (hx : 0 ≤ x)
    (hcoeff : ∀ i, 0 ≤ P.coeff i) (hconstant : 0 < P.coeff 0) :
    0 < P.eval₂ (Int.castRingHom ℝ) x := by
  rw [Polynomial.eval₂_eq_sum_range]
  have h0 : (0 : ℝ) < (Int.castRingHom ℝ) (P.coeff 0) * x ^ 0 := by
    simpa using (show (0 : ℝ) < (P.coeff 0 : ℝ) by exact_mod_cast hconstant)
  apply lt_of_lt_of_le h0
  apply Finset.single_le_sum (f := fun i : ℕ => (Int.castRingHom ℝ) (P.coeff i) * x ^ i)
  · intro i hi
    apply mul_nonneg _ (pow_nonneg hx i)
    change (0 : ℝ) ≤ (P.coeff i : ℝ)
    exact_mod_cast hcoeff i
  · exact Finset.mem_range.mpr (Nat.succ_pos _)

theorem eval₂_pos_of_translated_coeff (P : ℤ[X]) {p : ℝ} (hp : 1 ≤ p)
    (hcoeff : ∀ i, 0 ≤ (P.comp (X + 1)).coeff i)
    (hconstant : 0 < (P.comp (X + 1)).coeff 0) :
    0 < P.eval₂ (Int.castRingHom ℝ) p := by
  have h := eval₂_pos_of_nonneg_coeff (P.comp (X + 1))
    (sub_nonneg.mpr hp) hcoeff hconstant
  simpa [Polynomial.eval₂_comp] using h

/-- The polynomial determinant evaluates to the literal real Hankel determinant. -/
theorem coefficientHankelDetPoly_eval (p : ℝ) (N h : ℕ) :
    (coefficientHankelDetPoly N h).eval₂ (Int.castRingHom ℝ) p =
      Matrix.det (Matrix.of fun i j : Fin N =>
        coefficientMoment p (i.val + j.val + h)) := by
  exact (Polynomial.eval₂RingHom (Int.castRingHom ℝ) p).map_det _

/-- The certificate consumer retains the exact determinant and shift.
The two coefficient hypotheses must be established by a separate kernel check. -/
theorem coefficientHankelDet_pos_of_certificate {p : ℝ} (hp : 1 ≤ p) (N h : ℕ)
    (hcoeff : ∀ i, 0 ≤ ((coefficientHankelDetPoly N h).comp (X + 1)).coeff i)
    (hconstant : 0 < ((coefficientHankelDetPoly N h).comp (X + 1)).coeff 0) :
    0 < Matrix.det (Matrix.of fun i j : Fin N =>
      coefficientMoment p (i.val + j.val + h)) := by
  rw [← coefficientHankelDetPoly_eval]
  exact eval₂_pos_of_translated_coeff _ hp hcoeff hconstant

#print axioms coefficientBetaPoly_zero
#print axioms coefficientAlphaMatrix_diagonal_congruence
#print axioms coefficientAlphaMatrix_isSymm
#print axioms coefficientBetaMatrix_isSymm
#print axioms coefficientHankelDet_pos_of_certificate

end
end ErdosProblems.Erdos1049.PaperR20
