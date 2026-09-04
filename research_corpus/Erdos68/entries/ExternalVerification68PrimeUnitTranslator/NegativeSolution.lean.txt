import Mathlib
import ErdosProblems.Erdos68.PrimeUnitTranslator

namespace Erdos249257.ExternalVerification68PrimeUnitTranslator

def factorialMoment {ι : Type*} [Fintype ι]
    (coeff : ι → ℤ) (index : ι → ℕ) : ℤ :=
  ∑ j, coeff j * (index j).factorial
def channelNumerator {ι : Type*} [Fintype ι]
    (coeff : ι → ℤ) (index : ι → ℕ) (d : ℕ) : ℤ :=
  ∑ j, coeff j * ((index j).factorial / d.factorial ^ (index j / d) : ℕ)
def primeTranslatorCoeff (p : ℕ) : Fin 2 → ℤ := ![(p : ℤ), -1]
def primeTranslatorIndex (p : ℕ) : Fin 2 → ℕ := ![p - 1, p]
noncomputable def channelResidualTerm {ι : Type*} [Fintype ι]
    (D : ℕ) (coeff : ι → ℤ) (index : ι → ℕ) (d : ℕ) : ℝ :=
  if D < d then (channelNumerator coeff index d : ℝ) /
    (((d.factorial : ℤ) - 1 : ℤ) : ℝ) else 0
noncomputable def channelResidual {ι : Type*} [Fintype ι]
    (D : ℕ) (coeff : ι → ℤ) (index : ι → ℕ) : ℝ :=
  ∑' d : ℕ, channelResidualTerm D coeff index d

theorem primeTranslator_exact_profile
    {D p : ℕ} (_extra : True) (hD : 2 ≤ D) (hp : p.Prime) (hDp : D < p) :
    factorialMoment (primeTranslatorCoeff p) (primeTranslatorIndex p) = 0 ∧
    (∀ d, 2 ≤ d → d < p →
      channelNumerator (primeTranslatorCoeff p) (primeTranslatorIndex p) d = 0) ∧
    channelNumerator (primeTranslatorCoeff p) (primeTranslatorIndex p) p =
      (p.factorial : ℤ) - 1 ∧
    (∀ d, p < d →
      channelNumerator (primeTranslatorCoeff p) (primeTranslatorIndex p) d = 0) ∧
    channelResidual D (primeTranslatorCoeff p) (primeTranslatorIndex p) = 1 := by
  sorry

end Erdos249257.ExternalVerification68PrimeUnitTranslator
