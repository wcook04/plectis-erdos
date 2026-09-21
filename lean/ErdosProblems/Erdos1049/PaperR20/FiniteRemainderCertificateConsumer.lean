import ErdosProblems.Erdos1049.PaperR20.MomentRationalKernel
import ErdosProblems.Erdos1049.PaperR20.CoefficientPencil

/-!
# Consumer for exact finite remainder certificates

The producer supplies identities in `Polynomial (Polynomial ℤ)`: the inner
variable is the paper's integer base `p`, and the outer variable is the
rational-kernel variable.  This module evaluates those identities, derives the
pointwise rational decomposition, invokes the existing analytic summation
theorem, and identifies its finite correction with the literal `β_m`.

No certificate existence claim is made here.
-/

namespace ErdosProblems.Erdos1049.PaperR20

open Polynomial Finset
open scoped BigOperators

noncomputable section

abbrev ParameterPolynomial := ℤ[X]
abbrev BivariatePolynomial := Polynomial ParameterPolynomial

def parameterEval (p : ℝ) : ParameterPolynomial →+* ℝ :=
  eval₂RingHom (Int.castRingHom ℝ) p

def evalBivariate (P : BivariatePolynomial) (p x : ℝ) : ℝ :=
  P.eval₂ (parameterEval p) x

def clearedMomentNumeratorPoly (m e : ℕ) : BivariatePolynomial :=
  C (X ^ e * (∏ j ∈ range m, (X ^ (j + 1) - 1)) ^ 3) * X ^ (m + 1) *
    ∏ j ∈ range m, (C (X ^ (j + 1)) - X)

def clearedMomentDenominatorPoly (m : ℕ) : BivariatePolynomial :=
  ∏ j ∈ range (m + 1), (C (X ^ (m + 1 + j)) - X)

def clearedMomentDenominatorExceptPoly (m k : ℕ) : BivariatePolynomial :=
  ∏ j ∈ (range (m + 1)).erase k, (C (X ^ (m + 1 + j)) - X)

def residueCertificatePoly (m d : ℕ)
    (Cpoly : Fin (m + 1) → ParameterPolynomial) : BivariatePolynomial :=
  C (X ^ d) * ∑ k : Fin (m + 1),
    C (Cpoly k * X ^ (m + 1 + k.val)) *
      clearedMomentDenominatorExceptPoly m k.val

@[simp] theorem evalBivariate_C (P : ParameterPolynomial) (p x : ℝ) :
    evalBivariate (C P) p x = parameterEval p P := by
  simp [evalBivariate]

@[simp] theorem evalBivariate_X (p x : ℝ) :
    evalBivariate (X : BivariatePolynomial) p x = x := by
  simp [evalBivariate]

@[simp] theorem evalBivariate_add (P Q : BivariatePolynomial) (p x : ℝ) :
    evalBivariate (P + Q) p x = evalBivariate P p x + evalBivariate Q p x := by
  simp [evalBivariate]

@[simp] theorem evalBivariate_sub (P Q : BivariatePolynomial) (p x : ℝ) :
    evalBivariate (P - Q) p x = evalBivariate P p x - evalBivariate Q p x := by
  simp [evalBivariate]

@[simp] theorem evalBivariate_mul (P Q : BivariatePolynomial) (p x : ℝ) :
    evalBivariate (P * Q) p x = evalBivariate P p x * evalBivariate Q p x := by
  simp [evalBivariate]

@[simp] theorem evalBivariate_pow (P : BivariatePolynomial) (n : ℕ) (p x : ℝ) :
    evalBivariate (P ^ n) p x = evalBivariate P p x ^ n := by
  change (eval₂RingHom (parameterEval p) x) (P ^ n) =
    ((eval₂RingHom (parameterEval p) x) P) ^ n
  exact map_pow _ P n

@[simp] theorem evalBivariate_sum {ι : Type*} (s : Finset ι)
    (P : ι → BivariatePolynomial) (p x : ℝ) :
    evalBivariate (∑ i ∈ s, P i) p x = ∑ i ∈ s, evalBivariate (P i) p x := by
  change (eval₂RingHom (parameterEval p) x) (∑ i ∈ s, P i) =
    ∑ i ∈ s, (eval₂RingHom (parameterEval p) x) (P i)
  simp

@[simp] theorem evalBivariate_prod {ι : Type*} (s : Finset ι)
    (P : ι → BivariatePolynomial) (p x : ℝ) :
    evalBivariate (∏ i ∈ s, P i) p x = ∏ i ∈ s, evalBivariate (P i) p x := by
  change (eval₂RingHom (parameterEval p) x) (∏ i ∈ s, P i) =
    ∏ i ∈ s, (eval₂RingHom (parameterEval p) x) (P i)
  simp

@[simp] theorem evalBivariate_C_X (p x : ℝ) :
    evalBivariate (C (X : ParameterPolynomial)) p x = p := by
  simp [evalBivariate, parameterEval]

theorem parameterEval_ne_zero_pow {p : ℝ} (hp : p ≠ 0) (d : ℕ) :
    parameterEval p (X ^ d) ≠ 0 := by
  simp [parameterEval, hp]

set_option maxHeartbeats 1600000 in
/-- A nested-polynomial certificate is enough to derive the literal moment
identity.  Every hypothesis is finite algebraic data: polynomial equality,
exact divisibility, or the elementary exponent balance used when inverse
powers are cleared. -/
theorem actualMoment_eq_coefficientLinearForm_of_finite_certificate
    (p : ℝ) (hp : 1 < p) (m d e : ℕ)
    (Qbar : BivariatePolynomial) (Qzero : ParameterPolynomial)
    (Qcoeff : Fin m → ParameterPolynomial)
    (Cpoly : Fin (m + 1) → ParameterPolynomial)
    (Cquot : (k : Fin (m + 1)) → Fin (m + k.val) → ParameterPolynomial)
    (Qquot : Fin m → ParameterPolynomial)
    (hbalance : (∑ j ∈ range (m + 1), (m + 1 + j)) + d =
      4 * (∑ j ∈ range m, (j + 1)) + e)
    (hQsplit : Qbar = C Qzero + ∑ j : Fin m, C (Qcoeff j) * X ^ (j.val + 1))
    (hpartial : clearedMomentNumeratorPoly m e =
      Qbar * clearedMomentDenominatorPoly m +
        residueCertificatePoly m d Cpoly)
    (halpha : ∑ k : Fin (m + 1), Cpoly k = coefficientAlphaPoly m)
    (hconstant : Qzero + X ^ d * coefficientAlphaPoly m = 0)
    (hCdiv : ∀ (k : Fin (m + 1)) (n : Fin (m + k.val)),
      Cpoly k = (X ^ (n.val + 1) - 1) * Cquot k n)
    (hQdiv : ∀ j : Fin m,
      Qcoeff j = (X ^ (j.val + 1) - 1) * Qquot j)
    (hbeta : X ^ d * coefficientBetaPoly m =
      X ^ d * (∑ k : Fin (m + 1), ∑ n : Fin (m + k.val), Cquot k n) -
        ∑ j : Fin m, X ^ (j.val + 1) * Qquot j) :
    PaperR12.actualMoment p⁻¹ m =
      coefficientAlpha p m * PaperR16.lambert p⁻¹ - coefficientBeta p m := by
  let f : ParameterPolynomial →+* ℝ := parameterEval p
  let q : ℝ := p⁻¹
  let A : Fin m → ℝ := fun j => f (Qcoeff j) / p ^ d
  let Cv : Fin (m + 1) → ℝ := fun k => f (Cpoly k)
  have hp0 : 0 < p := lt_trans zero_lt_one hp
  have hpne : p ≠ 0 := ne_of_gt hp0
  have hq0 : 0 < q := inv_pos.mpr hp0
  have hq1 : q < 1 := (inv_lt_one₀ hp0).2 hp
  have hpd : p ^ d ≠ 0 := pow_ne_zero d hpne
  have heval (P : ParameterPolynomial) : f P = P.eval₂ (Int.castRingHom ℝ) p := rfl
  have hsumC : (∑ k, Cv k) = coefficientAlpha p m := by
    have h := congrArg f halpha
    simpa [Cv, coefficientAlpha, f, parameterEval] using h
  have hzero : f Qzero + p ^ d * coefficientAlpha p m = 0 := by
    have h := congrArg f hconstant
    simpa [coefficientAlpha, f, parameterEval] using h
  have hkernel : ∀ t : ℕ,
      momentRationalKernel q m (q ^ t) = finiteRationalKernel q m A Cv t := by
    intro t
    let x : ℝ := q ^ t
    have hxle : x ≤ 1 := pow_le_one₀ hq0.le hq1.le
    have hfactor (j : ℕ) (hj : j ∈ range (m + 1)) :
        0 < p ^ (m + 1 + j) - x := by
      have hpow : 1 < p ^ (m + 1 + j) := one_lt_pow₀ hp (by omega)
      linarith
    have hden : (∏ j ∈ range (m + 1), (p ^ (m + 1 + j) - x)) ≠ 0 := by
      apply Finset.prod_ne_zero_iff.mpr
      intro j hj
      exact ne_of_gt (hfactor j hj)
    have hclear := momentRationalKernel_clear p hpne m d e x hbalance hden
    have hpoly := congrArg (fun P : BivariatePolynomial => evalBivariate P p x) hpartial
    have hQ := congrArg (fun P : BivariatePolynomial => evalBivariate P p x) hQsplit
    have h_except (k : Fin (m + 1)) :
        (p ^ (m + 1 + k.val) - x) *
            (∏ j ∈ (range (m + 1)).erase k.val, (p ^ (m + 1 + j) - x)) =
          ∏ j ∈ range (m + 1), (p ^ (m + 1 + j) - x) := by
      exact Finset.mul_prod_erase (range (m + 1))
        (fun j : ℕ => (p ^ (m + 1 + j) - x : ℝ))
        (Finset.mem_range.mpr k.isLt)
    have hresidue (k : Fin (m + 1)) :
        Cv k * p ^ (m + 1 + k.val) /
              (p ^ (m + 1 + k.val) - x) =
          Cv k + Cv k * x / (p ^ (m + 1 + k.val) - x) := by
      have hn := ne_of_gt (hfactor k.val (Finset.mem_range.mpr k.isLt))
      field_simp [hn]
      ring
    have hresidue_mul (k : Fin (m + 1)) :
        Cv k * p ^ (m + 1 + k.val) *
            (∏ j ∈ (range (m + 1)).erase k.val,
              (p ^ (m + 1 + j) - x)) =
          (Cv k + Cv k * x / (p ^ (m + 1 + k.val) - x)) *
            (∏ j ∈ range (m + 1), (p ^ (m + 1 + j) - x)) := by
      rw [← h_except k, ← hresidue k]
      have hn := ne_of_gt (hfactor k.val (Finset.mem_range.mpr k.isLt))
      field_simp [hn]
    have hpoly' :
        p ^ d * momentRationalKernel q m x *
            (∏ j ∈ range (m + 1), (p ^ (m + 1 + j) - x)) =
          (f Qzero + ∑ j : Fin m, f (Qcoeff j) * x ^ (j.val + 1)) *
              (∏ j ∈ range (m + 1), (p ^ (m + 1 + j) - x)) +
            p ^ d * ∑ k : Fin (m + 1),
              Cv k * p ^ (m + 1 + k.val) *
                (∏ j ∈ (range (m + 1)).erase k.val,
                  (p ^ (m + 1 + j) - x)) := by
      have hpX : parameterEval p (X : ParameterPolynomial) = p := by
        change Polynomial.eval₂ (Int.castRingHom ℝ) p X = p
        exact Polynomial.eval₂_X (Int.castRingHom ℝ) p
      have hbone : evalBivariate 1 p x = 1 := by simp [evalBivariate]
      simp only [hbone, clearedMomentNumeratorPoly, clearedMomentDenominatorPoly,
        clearedMomentDenominatorExceptPoly, residueCertificatePoly,
        evalBivariate_add, evalBivariate_mul, evalBivariate_sub,
        evalBivariate_pow, evalBivariate_sum, evalBivariate_prod,
        evalBivariate_C, evalBivariate_X,
        map_mul, map_pow, map_prod, map_sub, map_one, hpX] at hpoly hQ
      rw [hQ] at hpoly
      rw [hclear]
      simpa only [f, Cv, mul_assoc, mul_comm, mul_left_comm] using hpoly
    have hscaled :
        p ^ d * momentRationalKernel q m x =
          (∑ j : Fin m, f (Qcoeff j) * x ^ (j.val + 1)) +
            p ^ d * ∑ k : Fin (m + 1),
              Cv k * x / (p ^ (m + 1 + k.val) - x) := by
      apply (mul_right_cancel₀ hden)
      rw [hpoly']
      simp_rw [hresidue_mul]
      simp_rw [add_mul]
      rw [Finset.sum_add_distrib]
      rw [← Finset.sum_mul, ← Finset.sum_mul]
      rw [hsumC]
      linear_combination hzero *
        (∏ j ∈ range (m + 1), (p ^ (m + 1 + j) - x))
    have htail (k : Fin (m + 1)) :
        Cv k * q ^ (m + 1 + k.val + t) /
              (1 - q ^ (m + 1 + k.val + t)) =
          Cv k * x / (p ^ (m + 1 + k.val) - x) := by
      have hn := ne_of_gt (hfactor k.val (Finset.mem_range.mpr k.isLt))
      dsimp [q, x]
      rw [pow_add, inv_pow]
      field_simp [hpne, hn]
    have hgeom (j : Fin m) :
        q ^ ((j.val + 1) * t) = x ^ (j.val + 1) := by
      simp [x, pow_mul, Nat.mul_comm]
    unfold finiteRationalKernel
    simp_rw [hgeom, htail]
    dsimp [A]
    apply (mul_left_cancel₀ hpd)
    rw [hscaled, mul_add]
    congr 1
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    field_simp [hpd]
  have hmoment := actualMoment_eq_of_rationalKernel_certificate hq0 hq1 m A Cv hkernel
  have hprefix (k : Fin (m + 1)) :
      Cv k * finiteLambertPrefix q (m + k.val) =
        ∑ n : Fin (m + k.val), f (Cquot k n) := by
    unfold finiteLambertPrefix
    rw [Finset.mul_sum, ← Fin.sum_univ_eq_sum_range]
    apply Finset.sum_congr rfl
    intro n _
    · have hn0 : p ^ (n.val + 1) - 1 ≠ 0 :=
        ne_of_gt (sub_pos.mpr (one_lt_pow₀ hp (by omega)))
      have hd : f (Cpoly k) =
          (p ^ (n.val + 1) - 1) * f (Cquot k n) := by
        simpa [f, parameterEval] using congrArg f (hCdiv k n)
      dsimp [q, Cv]
      rw [inv_pow]
      rw [hd]
      field_simp [hpne, hn0]
  have hgeomCorrection (j : Fin m) :
      A j / (1 - q ^ (j.val + 1)) =
        p ^ (j.val + 1) * f (Qquot j) / p ^ d := by
    have hn : p ^ (j.val + 1) - 1 ≠ 0 :=
      ne_of_gt (sub_pos.mpr (one_lt_pow₀ hp (by omega)))
    have hd : f (Qcoeff j) =
        (p ^ (j.val + 1) - 1) * f (Qquot j) := by
      simpa [f, parameterEval] using congrArg f (hQdiv j)
    dsimp [A, q]
    rw [inv_pow]
    rw [hd]
    field_simp [hpne, hpd, hn]
  have hbetaEval := congrArg f hbeta
  have hcorrection :
      (∑ j, A j / (1 - q ^ (j.val + 1))) -
          ∑ k, Cv k * finiteLambertPrefix q (m + k.val) =
        -coefficientBeta p m := by
    simp_rw [hgeomCorrection, hprefix]
    have hb : p ^ d * coefficientBeta p m =
        p ^ d * (∑ k : Fin (m + 1), ∑ n : Fin (m + k.val), f (Cquot k n)) -
          ∑ j : Fin m, p ^ (j.val + 1) * f (Qquot j) := by
      simp only [map_sub, map_mul, map_pow, map_sum] at hbetaEval
      simpa [coefficientBeta, f, parameterEval] using hbetaEval
    apply (mul_left_cancel₀ hpd)
    calc
      p ^ d *
          ((∑ j : Fin m, p ^ (j.val + 1) * f (Qquot j) / p ^ d) -
            ∑ k : Fin (m + 1), ∑ n : Fin (m + k.val), f (Cquot k n)) =
          (∑ j : Fin m, p ^ (j.val + 1) * f (Qquot j)) -
            p ^ d *
              (∑ k : Fin (m + 1), ∑ n : Fin (m + k.val), f (Cquot k n)) := by
        rw [← Finset.sum_div]
        field_simp [hpd]
      _ = -(p ^ d * coefficientBeta p m) := by
        rw [hb]
        ring
      _ = p ^ d * (-coefficientBeta p m) := by ring
  rw [hmoment, hsumC]
  linarith

#print axioms actualMoment_eq_coefficientLinearForm_of_finite_certificate

end
end ErdosProblems.Erdos1049.PaperR20
