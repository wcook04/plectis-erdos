import Mathlib

namespace Erdos249257.ExternalVerification68PrimeUnitTranslator

def factorialMoment {ι : Type*} [Fintype ι]
    (coeff : ι → ℤ) (index : ι → ℕ) : ℤ :=
  ∑ j, coeff j * (index j).factorial

def channelNumerator {ι : Type*} [Fintype ι]
    (coeff : ι → ℤ) (index : ι → ℕ) (d : ℕ) : ℤ :=
  ∑ j, coeff j * ((index j).factorial /
    d.factorial ^ (index j / d) : ℕ)

def primeTranslatorCoeff (p : ℕ) : Fin 2 → ℤ := ![(p : ℤ), -1]
def primeTranslatorIndex (p : ℕ) : Fin 2 → ℕ := ![p - 1, p]

noncomputable def channelResidualTerm {ι : Type*} [Fintype ι]
    (D : ℕ) (coeff : ι → ℤ) (index : ι → ℕ) (d : ℕ) : ℝ :=
  if D < d then
    (channelNumerator coeff index d : ℝ) /
      (((d.factorial : ℤ) - 1 : ℤ) : ℝ)
  else 0

noncomputable def channelResidual {ι : Type*} [Fintype ι]
    (D : ℕ) (coeff : ι → ℤ) (index : ι → ℕ) : ℝ :=
  ∑' d : ℕ, channelResidualTerm D coeff index d

def appendPrimeTranslatorCoeff {ι : Type*}
    (coeff : ι → ℤ) (p : ℕ) (z : ℤ) : Sum ι (Fin 2) → ℤ :=
  Sum.elim coeff (fun j => z * primeTranslatorCoeff p j)

def appendPrimeTranslatorIndex {ι : Type*}
    (index : ι → ℕ) (p : ℕ) : Sum ι (Fin 2) → ℕ :=
  Sum.elim index (primeTranslatorIndex p)

def augmentedChannelMomentMatrix {n : ℕ}
    (index : Fin (n + 1) → ℕ) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ :=
  fun r j =>
    Fin.cases ((index j).factorial : ℤ)
      (fun d : Fin n =>
        ((index j).factorial /
          (d.val + 2).factorial ^ (index j / (d.val + 2)) : ℕ)) r

def cramerChannelKernelCoeff {n : ℕ}
    (index : Fin (n + 1) → ℕ) : Fin (n + 1) → ℤ :=
  (augmentedChannelMomentMatrix index).cramer (Pi.single 0 1)

def factorialGridScale (D : ℕ) : ℕ := D.factorial ^ 2

def factorialGridIndex (n t : ℕ) (j : Fin (n + 2)) : ℕ :=
  (t + j.val) * factorialGridScale (n + 2)

theorem primeTranslator_exact_profile
    {D p : ℕ} (hD : 2 ≤ D) (hp : p.Prime) (hDp : D < p) :
    factorialMoment (primeTranslatorCoeff p) (primeTranslatorIndex p) = 0 ∧
    (∀ d, 2 ≤ d → d < p →
      channelNumerator (primeTranslatorCoeff p) (primeTranslatorIndex p) d = 0) ∧
    channelNumerator (primeTranslatorCoeff p) (primeTranslatorIndex p) p =
      (p.factorial : ℤ) - 1 ∧
    (∀ d, p < d →
      channelNumerator (primeTranslatorCoeff p) (primeTranslatorIndex p) d = 0) ∧
    channelResidual D (primeTranslatorCoeff p) (primeTranslatorIndex p) = 1 := by
  sorry

theorem channelResidual_appendPrimeTranslator
    {ι : Type*} [Fintype ι]
    (coeff : ι → ℤ) (index : ι → ℕ) {D p : ℕ} (z : ℤ)
    (hD : 2 ≤ D) (hp : p.Prime) (hDp : D < p) :
    channelResidual D (appendPrimeTranslatorCoeff coeff p z)
        (appendPrimeTranslatorIndex index p) =
      channelResidual D coeff index + (z : ℝ) := by
  sorry

theorem exists_remote_factorialGrid_primeTranslator_reduction
    (n B : ℕ) :
    ∃ p : ℕ, ∃ z : ℤ,
      p.Prime ∧
      (∀ j : Sum (Fin (n + 2)) (Fin 2),
        B < appendPrimeTranslatorIndex
          (factorialGridIndex n (B + 1)) p j) ∧
      (∀ d ∈ Finset.Icc 2 (n + 2),
        channelNumerator
          (appendPrimeTranslatorCoeff
            (cramerChannelKernelCoeff
              (factorialGridIndex n (B + 1))) p z)
          (appendPrimeTranslatorIndex
            (factorialGridIndex n (B + 1)) p) d = 0) ∧
      factorialMoment
          (appendPrimeTranslatorCoeff
            (cramerChannelKernelCoeff
              (factorialGridIndex n (B + 1))) p z)
          (appendPrimeTranslatorIndex
            (factorialGridIndex n (B + 1)) p) ≠ 0 ∧
      |channelResidual (n + 2)
          (appendPrimeTranslatorCoeff
            (cramerChannelKernelCoeff
              (factorialGridIndex n (B + 1))) p z)
          (appendPrimeTranslatorIndex
            (factorialGridIndex n (B + 1)) p)| ≤ (1 : ℝ) / 2 := by
  sorry

end Erdos249257.ExternalVerification68PrimeUnitTranslator
