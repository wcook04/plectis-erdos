import ErdosProblems.Erdos1049.PaperR20.CoefficientPencil
import ErdosProblems.Erdos1049.ActualMomentGeneratingR12
import ErdosProblems.Erdos1049.PaperR16.LambertBasic
import Mathlib.Analysis.Polynomial.Basic

/-!
# Uniqueness of the polynomial part at infinity

This file isolates the asymptotic uniqueness step in the coefficient-moment
argument.  It deliberately does not assert the still-missing Padé remainder
identity.  Once the analytic Lambert tail and the limit of the literal moment
are supplied, the polynomial called `β_m` in the paper is forced.
-/

namespace ErdosProblems.Erdos1049.PaperR20

open Filter Polynomial Topology

noncomputable section

/-- Evaluation of an integer polynomial on the real line. -/
def realPolynomialEval (P : ℤ[X]) (x : ℝ) : ℝ :=
  P.eval₂ (Int.castRingHom ℝ) x

/-- The precise analytic assertion that `lambertPolynomialPart P` is the
polynomial part at infinity of `P(p) * F(p⁻¹)`.  Naming this assertion keeps
the algebraic uniqueness theorem independent of a particular tail estimate. -/
def HasLambertPolynomialPartLimit (P : ℤ[X]) : Prop :=
  Tendsto (fun p : ℝ =>
    realPolynomialEval P p * PaperR16.lambert p⁻¹ -
      realPolynomialEval (lambertPolynomialPart P) p) atTop (𝓝 0)

/-- A real polynomial whose values tend to zero at positive infinity is the
zero polynomial.  This is the small algebraic rigidity fact used below. -/
theorem polynomial_eq_zero_of_eval_tendsto_zero (P : ℤ[X])
    (hP : Tendsto (realPolynomialEval P) atTop (𝓝 0)) : P = 0 := by
  have hmap : Tendsto (fun x : ℝ => (P.map (Int.castRingHom ℝ)).eval x)
      atTop (𝓝 0) := by
    simpa only [realPolynomialEval, Polynomial.eval_map] using hP
  have hlead : (P.map (Int.castRingHom ℝ)).leadingCoeff = 0 :=
    ((Polynomial.tendsto_nhds_iff (P.map (Int.castRingHom ℝ))).mp hmap).1
  have hz : P.map (Int.castRingHom ℝ) = 0 :=
    Polynomial.leadingCoeff_eq_zero.mp hlead
  exact (Polynomial.map_eq_zero_iff Int.cast_injective).mp hz

/-- The polynomial part is unique.  The first hypothesis is the genuine
Lambert-tail estimate; the second says that a candidate subtraction has limit
one.  No moment or Padé identity is hidden among the hypotheses. -/
theorem eq_lambertPolynomialPart_sub_one_of_tendsto
    (P B : ℤ[X])
    (hP : HasLambertPolynomialPartLimit P)
    (hB : Tendsto (fun p : ℝ =>
      realPolynomialEval P p * PaperR16.lambert p⁻¹ -
        realPolynomialEval B p) atTop (𝓝 1)) :
    B = lambertPolynomialPart P - 1 := by
  let D : ℤ[X] := B - (lambertPolynomialPart P - 1)
  have hD : Tendsto (realPolynomialEval D) atTop (𝓝 0) := by
    have hone : Tendsto (fun _ : ℝ => (1 : ℝ)) atTop (𝓝 1) :=
      tendsto_const_nhds
    have hsum := hP.add (hone.sub hB)
    simp only [sub_self, zero_add] at hsum
    convert hsum using 1
    funext p
    simp only [D, realPolynomialEval, Polynomial.eval₂_sub, Polynomial.eval₂_one]
    ring
  have : D = 0 := polynomial_eq_zero_of_eval_tendsto_zero D hD
  exact sub_eq_zero.mp this

/-- A remainder function tending to one forces its subtracting polynomial.
The equality need only hold eventually, which is convenient for formulas valid
for `p > 1`. -/
theorem eq_lambertPolynomialPart_sub_one_of_eventual_remainder
    (P B : ℤ[X]) (μ : ℝ → ℝ)
    (hP : HasLambertPolynomialPartLimit P)
    (hμ : Tendsto μ atTop (𝓝 1))
    (hremainder : ∀ᶠ p : ℝ in atTop,
      μ p = realPolynomialEval P p * PaperR16.lambert p⁻¹ -
        realPolynomialEval B p) :
    B = lambertPolynomialPart P - 1 := by
  apply eq_lambertPolynomialPart_sub_one_of_tendsto P B hP
  exact hμ.congr' hremainder

/-- Concrete endpoint for the paper's coefficient polynomials.  It records
exactly the two analytic inputs still required from the Padé calculation:
the Lambert-tail estimate and convergence of the literal moment. -/
theorem coefficientBetaPoly_unique_of_remainder
    (m : ℕ) (B : ℤ[X])
    (hLambert : HasLambertPolynomialPartLimit (coefficientAlphaPoly m))
    (hMoment : Tendsto (fun p : ℝ => PaperR12.actualMoment p⁻¹ m)
      atTop (𝓝 1))
    (hremainder : ∀ p : ℝ, 1 < p →
      PaperR12.actualMoment p⁻¹ m =
        coefficientAlpha p m * PaperR16.lambert p⁻¹ -
          realPolynomialEval B p) :
    B = coefficientBetaPoly m := by
  rw [coefficientBetaPoly]
  apply eq_lambertPolynomialPart_sub_one_of_eventual_remainder
    (coefficientAlphaPoly m) B (fun p : ℝ => PaperR12.actualMoment p⁻¹ m)
    hLambert hMoment
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with p hp
  simpa [coefficientAlpha, realPolynomialEval] using hremainder p hp

#print axioms polynomial_eq_zero_of_eval_tendsto_zero
#print axioms eq_lambertPolynomialPart_sub_one_of_tendsto
#print axioms coefficientBetaPoly_unique_of_remainder

end
end ErdosProblems.Erdos1049.PaperR20
