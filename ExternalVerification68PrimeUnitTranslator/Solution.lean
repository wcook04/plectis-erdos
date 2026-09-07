/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib
import ErdosProblems.Erdos68.PrimeUnitTranslator

/-!
# Source transport for the Erdős #68 prime-unit translator

The declarations below restate the Mathlib-only challenge vocabulary and
transport the exact source theorems without strengthening their hypotheses.
-/

namespace Erdos249257.ExternalVerification68PrimeUnitTranslator

/-- The factorial moment of an integer coefficient vector. -/
def factorialMoment {ι : Type*} [Fintype ι]
    (coeff : ι → ℤ) (index : ι → ℕ) : ℤ :=
  ∑ j, coeff j * (index j).factorial

/-- The integer numerator of the `d`-th divisor channel. -/
def channelNumerator {ι : Type*} [Fintype ι]
    (coeff : ι → ℤ) (index : ι → ℕ) (d : ℕ) : ℤ :=
  ∑ j, coeff j * ((index j).factorial /
    d.factorial ^ (index j / d) : ℕ)

/-- Coefficients `(p, -1)` of the prime-pair translator. -/
def primeTranslatorCoeff (p : ℕ) : Fin 2 → ℤ := ![(p : ℤ), -1]

/-- Support indices `(p - 1, p)` of the prime-pair translator. -/
def primeTranslatorIndex (p : ℕ) : Fin 2 → ℕ := ![p - 1, p]

/-- The real contribution of one channel to the tail beyond `D`. -/
noncomputable def channelResidualTerm {ι : Type*} [Fintype ι]
    (D : ℕ) (coeff : ι → ℤ) (index : ι → ℕ) (d : ℕ) : ℝ :=
  if D < d then
    (channelNumerator coeff index d : ℝ) /
      (((d.factorial : ℤ) - 1 : ℤ) : ℝ)
  else 0

/-- The full normalized residual beyond the cutoff `D`. -/
noncomputable def channelResidual {ι : Type*} [Fintype ι]
    (D : ℕ) (coeff : ι → ℤ) (index : ι → ℕ) : ℝ :=
  ∑' d : ℕ, channelResidualTerm D coeff index d

/-- Coefficients for a support enlarged by a scaled prime translator. -/
def appendPrimeTranslatorCoeff {ι : Type*}
    (coeff : ι → ℤ) (p : ℕ) (z : ℤ) : Sum ι (Fin 2) → ℤ :=
  Sum.elim coeff (fun j => z * primeTranslatorCoeff p j)

/-- Indices for a support enlarged by the prime translator. -/
def appendPrimeTranslatorIndex {ι : Type*}
    (index : ι → ℕ) (p : ℕ) : Sum ι (Fin 2) → ℕ :=
  Sum.elim index (primeTranslatorIndex p)

/-- The moment row together with the consecutive channel rows. -/
def augmentedChannelMomentMatrix {n : ℕ}
    (index : Fin (n + 1) → ℕ) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ :=
  fun r j =>
    Fin.cases ((index j).factorial : ℤ)
      (fun d : Fin n =>
        ((index j).factorial /
          (d.val + 2).factorial ^ (index j / (d.val + 2)) : ℕ)) r

/-- Cramer's-rule coefficient vector for unit factorial moment and zero
consecutive channels. -/
def cramerChannelKernelCoeff {n : ℕ}
    (index : Fin (n + 1) → ℕ) : Fin (n + 1) → ℤ :=
  (augmentedChannelMomentMatrix index).cramer (Pi.single 0 1)

/-- The common scale of the factorial grid at cutoff `D`. -/
def factorialGridScale (D : ℕ) : ℕ := D.factorial ^ 2

/-- The factorial grid of `n + 2` indices starting at `t`. -/
def factorialGridIndex (n t : ℕ) (j : Fin (n + 2)) : ℕ :=
  (t + j.val) * factorialGridScale (n + 2)

/-- The prime-pair translator has zero factorial moment. -/
theorem primeTranslator_moment_zero
    {p : ℕ} (hp : 0 < p) :
    factorialMoment (primeTranslatorCoeff p) (primeTranslatorIndex p) = 0 := by
  simpa [factorialMoment, primeTranslatorCoeff, primeTranslatorIndex,
    Erdos68.factorialMoment, Erdos68.primeTranslatorCoeff,
    Erdos68.primeTranslatorIndex] using Erdos68.primeTranslator_moment_zero hp

/-- Every channel strictly below `p` annihilates the prime translator. -/
theorem primeTranslator_channel_zero_of_lt_p
    {p d : ℕ} (hp : p.Prime) (hd2 : 2 ≤ d) (hdp : d < p) :
    channelNumerator (primeTranslatorCoeff p) (primeTranslatorIndex p) d = 0 := by
  simpa [channelNumerator, primeTranslatorCoeff, primeTranslatorIndex,
    Erdos68.channelNumerator, Erdos68.primeTranslatorCoeff,
    Erdos68.primeTranslatorIndex] using
    Erdos68.primeTranslator_channel_zero_of_lt_p hp hd2 hdp

/-- At the prime itself the sole surviving channel numerator is exactly its
normalizing modulus `p! - 1`. -/
theorem primeTranslator_channel_at_prime
    {p : ℕ} (hp : p.Prime) :
    channelNumerator (primeTranslatorCoeff p) (primeTranslatorIndex p) p =
      (p.factorial : ℤ) - 1 := by
  simpa [channelNumerator, primeTranslatorCoeff, primeTranslatorIndex,
    Erdos68.channelNumerator, Erdos68.primeTranslatorCoeff,
    Erdos68.primeTranslatorIndex] using
    Erdos68.primeTranslator_channel_at_prime hp

/-- Every channel strictly beyond `p` annihilates the prime translator. -/
theorem primeTranslator_channel_zero_of_p_lt
    {p d : ℕ} (hp : 0 < p) (hpd : p < d) :
    channelNumerator (primeTranslatorCoeff p) (primeTranslatorIndex p) d = 0 := by
  simpa [channelNumerator, primeTranslatorCoeff, primeTranslatorIndex,
    Erdos68.channelNumerator, Erdos68.primeTranslatorCoeff,
    Erdos68.primeTranslatorIndex] using
    Erdos68.primeTranslator_channel_zero_of_p_lt hp hpd

/-- The prime-pair translator is an exact unit direction for the full
infinite channel residual. -/
theorem primeTranslator_channelResidual_eq_one
    {D p : ℕ} (hD : 2 ≤ D) (hp : p.Prime) (hDp : D < p) :
    channelResidual D (primeTranslatorCoeff p) (primeTranslatorIndex p) = 1 := by
  simpa [channelResidual, channelResidualTerm, channelNumerator,
    primeTranslatorCoeff, primeTranslatorIndex,
    Erdos68.channelResidual, Erdos68.channelResidualTerm,
    Erdos68.channelNumerator, Erdos68.primeTranslatorCoeff,
    Erdos68.primeTranslatorIndex] using
    Erdos68.primeTranslator_channelResidual_eq_one hD hp hDp

/-- Appending a scaled prime translator shifts the full residual by that
integer and changes nothing else in the original support. -/
theorem channelResidual_appendPrimeTranslator
    {ι : Type*} [Fintype ι]
    (coeff : ι → ℤ) (index : ι → ℕ) {D p : ℕ} (z : ℤ)
    (hD : 2 ≤ D) (hp : p.Prime) (hDp : D < p) :
    channelResidual D (appendPrimeTranslatorCoeff coeff p z)
        (appendPrimeTranslatorIndex index p) =
      channelResidual D coeff index + (z : ℝ) := by
  simpa [channelResidual, channelResidualTerm, channelNumerator,
    appendPrimeTranslatorCoeff, appendPrimeTranslatorIndex,
    primeTranslatorCoeff, primeTranslatorIndex,
    Erdos68.channelResidual, Erdos68.channelResidualTerm,
    Erdos68.channelNumerator, Erdos68.appendPrimeTranslatorCoeff,
    Erdos68.appendPrimeTranslatorIndex, Erdos68.primeTranslatorCoeff,
    Erdos68.primeTranslatorIndex] using
    Erdos68.channelResidual_appendPrimeTranslator coeff index z hD hp hDp

/-- For every cutoff and support threshold, a factorial-grid block and a
prime translator pair can be chosen entirely above the threshold, with the
stated zero-channel, nonzero-moment, and residual bounds. -/
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
  simpa [factorialMoment, channelNumerator, primeTranslatorCoeff,
    primeTranslatorIndex, channelResidual, channelResidualTerm,
    appendPrimeTranslatorCoeff, appendPrimeTranslatorIndex,
    augmentedChannelMomentMatrix, cramerChannelKernelCoeff,
    factorialGridScale, factorialGridIndex,
    Erdos68.factorialMoment, Erdos68.channelNumerator,
    Erdos68.primeTranslatorCoeff, Erdos68.primeTranslatorIndex,
    Erdos68.channelResidual, Erdos68.channelResidualTerm,
    Erdos68.appendPrimeTranslatorCoeff, Erdos68.appendPrimeTranslatorIndex,
    Erdos68.augmentedChannelMomentMatrix, Erdos68.cramerChannelKernelCoeff,
    Erdos68.factorialGridScale, Erdos68.factorialGridIndex] using
    Erdos68.exists_remote_factorialGrid_primeTranslator_reduction n B

end Erdos249257.ExternalVerification68PrimeUnitTranslator
