/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Erdos249257.BooleanMobiusCarry

namespace Erdos249257.ExternalVerification257BooleanMobiusCarry

open ArithmeticFunction Filter Set
open scoped ArithmeticFunction.Moebius

noncomputable section

noncomputable def supportCoeff (A : Set ℕ) (n : ℕ) : ℕ :=
  letI := Classical.decPred fun d : ℕ => d ∈ A
  (n.divisors.filter fun d => d ∈ A).card

noncomputable def erdosSupportSeries (b : ℕ) (A : Set ℕ) : ℝ :=
  ∑' a : ℕ, Set.indicator A (fun a => (1 : ℝ) / ((b : ℝ) ^ a - 1)) a

def IsTemperedBinaryOrbit (c : ℕ → ℕ) (v : ℕ) (u : ℕ → ℤ) : Prop :=
  (∀ N : ℕ,
      u (N + 1) = 2 * u N - ((v * c (N + 1) : ℕ) : ℤ)) ∧
    Tendsto (fun N : ℕ ↦ (u N : ℝ) / (2 : ℝ) ^ N) atTop (nhds 0)

noncomputable def supportCoeffAF (A : Set ℕ) : ArithmeticFunction ℤ :=
  ⟨fun n ↦ (supportCoeff A n : ℤ), by simp [supportCoeff]⟩

noncomputable def booleanMobiusSupport (f : ArithmeticFunction ℤ) : Set ℕ :=
  {n : ℕ | 0 < n ∧ (ArithmeticFunction.moebius * f) n = 1}

def carryQuotient (q : ℕ) (U : ℕ → ℤ) (n : ℕ) : ℤ :=
  if n = 0 then 0 else (2 * U (n - 1) - U n) / (q : ℤ)

def carryQuotientAF (q : ℕ) (U : ℕ → ℤ) : ArithmeticFunction ℤ :=
  ⟨carryQuotient q U, by simp [carryQuotient]⟩

structure BooleanMobiusCarryCertificate
    (p : ℤ) (q : ℕ) (U : ℕ → ℤ) : Prop where
  initial : U 0 = p
  positive : ∀ N : ℕ, 0 < U N
  sqrtBound : ∀ N : ℕ, (U N : ℝ) ≤
    (q : ℝ) * (2 * Real.sqrt (N : ℝ) + 4)
  divisible : ∀ N : ℕ, (q : ℤ) ∣ 2 * U N - U (N + 1)
  mobiusBoolean : ∀ n : ℕ, 0 < n →
    (ArithmeticFunction.moebius * carryQuotientAF q U) n = 0 ∨
      (ArithmeticFunction.moebius * carryQuotientAF q U) n = 1

private def toSourceCertificate
    {p : ℤ} {q : ℕ} {U : ℕ → ℤ}
    (cert : BooleanMobiusCarryCertificate p q U) :
    Erdos249257.BooleanMobiusCarryCertificate p q U where
  initial := cert.initial
  positive := cert.positive
  sqrtBound := cert.sqrtBound
  divisible := cert.divisible
  mobiusBoolean := by
    intro n hn
    simpa [carryQuotientAF, carryQuotient,
      Erdos249257.carryQuotientAF,
      Erdos249257.carryQuotient] using cert.mobiusBoolean n hn

private def ofSourceCertificate
    {p : ℤ} {q : ℕ} {U : ℕ → ℤ}
    (cert : Erdos249257.BooleanMobiusCarryCertificate p q U) :
    BooleanMobiusCarryCertificate p q U where
  initial := cert.initial
  positive := cert.positive
  sqrtBound := cert.sqrtBound
  divisible := cert.divisible
  mobiusBoolean := by
    intro n hn
    simpa [carryQuotientAF, carryQuotient,
      Erdos249257.carryQuotientAF,
      Erdos249257.carryQuotient] using cert.mobiusBoolean n hn

theorem exists_booleanMobiusCarry_of_support_fraction
    (A : Set ℕ) (hzero : 0 ∉ A)
    (hpos : ∃ a : ℕ, 0 < a ∧ a ∈ A)
    (p : ℤ) (q : ℕ) (hq : 0 < q)
    (hvalue : erdosSupportSeries 2 A = (p : ℝ) / (q : ℝ)) :
    ∃ U : ℕ → ℤ, BooleanMobiusCarryCertificate p q U ∧
      {n : ℕ |
        (ArithmeticFunction.moebius * carryQuotientAF q U) n = 1} = A := by
  have hvalue' : Erdos249257.erdosSupportSeries 2 A =
      (p : ℝ) / (q : ℝ) := by
    simpa [erdosSupportSeries,
      Erdos249257.erdosSupportSeries] using hvalue
  obtain ⟨U, cert, hreconstruct⟩ :=
    Erdos249257.exists_booleanMobiusCarry_of_support_fraction
      A hzero hpos p q hq hvalue'
  refine ⟨U, ofSourceCertificate cert, ?_⟩
  simpa [carryQuotientAF, carryQuotient,
    Erdos249257.carryQuotientAF,
    Erdos249257.carryQuotient] using hreconstruct

theorem support_fraction_of_booleanMobiusCarry
    (p : ℤ) (q : ℕ) (hq : 0 < q) (U : ℕ → ℤ)
    (cert : BooleanMobiusCarryCertificate p q U) :
    let A := booleanMobiusSupport (carryQuotientAF q U)
    0 ∉ A ∧ erdosSupportSeries 2 A = (p : ℝ) / (q : ℝ) := by
  simpa [booleanMobiusSupport, carryQuotientAF, carryQuotient,
    erdosSupportSeries, Erdos249257.booleanMobiusSupport,
    Erdos249257.carryQuotientAF,
    Erdos249257.carryQuotient,
    Erdos249257.erdosSupportSeries] using
      Erdos249257.support_fraction_of_booleanMobiusCarry
        p q hq U (toSourceCertificate cert)

theorem BooleanMobiusCarryCertificate.reconstructsSupport
    {p : ℤ} {q : ℕ} {U : ℕ → ℤ} (hq : 0 < q)
    (cert : BooleanMobiusCarryCertificate p q U) :
    let A := booleanMobiusSupport (carryQuotientAF q U)
    0 ∉ A ∧
      carryQuotientAF q U = supportCoeffAF A ∧
      IsTemperedBinaryOrbit (supportCoeff A) q U ∧
      {n : ℕ |
        (ArithmeticFunction.moebius * carryQuotientAF q U) n = 1} = A ∧
      erdosSupportSeries 2 A = (p : ℝ) / (q : ℝ) := by
  simpa [booleanMobiusSupport, carryQuotientAF, carryQuotient,
    supportCoeffAF, supportCoeff, IsTemperedBinaryOrbit,
    erdosSupportSeries, Erdos249257.booleanMobiusSupport,
    Erdos249257.carryQuotientAF,
    Erdos249257.carryQuotient,
    Erdos249257.supportCoeffAF,
    Erdos249257.supportCoeff,
    Erdos249257.IsTemperedBinaryOrbit,
    Erdos249257.erdosSupportSeries] using
      Erdos249257.BooleanMobiusCarryCertificate.reconstructsSupport
        hq (toSourceCertificate cert)

theorem exists_normalized_support_fraction_iff_exists_booleanMobiusCarry
    (p : ℤ) (q : ℕ) (hq : 0 < q) :
    (∃ A : Set ℕ, 0 ∉ A ∧ (∃ a : ℕ, 0 < a ∧ a ∈ A) ∧
        erdosSupportSeries 2 A = (p : ℝ) / (q : ℝ)) ↔
      ∃ U : ℕ → ℤ, BooleanMobiusCarryCertificate p q U := by
  constructor
  · intro h
    have hsource : ∃ A : Set ℕ, 0 ∉ A ∧
        (∃ a : ℕ, 0 < a ∧ a ∈ A) ∧
        Erdos249257.erdosSupportSeries 2 A =
          (p : ℝ) / (q : ℝ) := by
      simpa [erdosSupportSeries,
        Erdos249257.erdosSupportSeries] using h
    obtain ⟨U, cert⟩ :=
      (Erdos249257.exists_normalized_support_fraction_iff_exists_booleanMobiusCarry
        p q hq).mp hsource
    exact ⟨U, ofSourceCertificate cert⟩
  · rintro ⟨U, cert⟩
    have hsource :=
      (Erdos249257.exists_normalized_support_fraction_iff_exists_booleanMobiusCarry
        p q hq).mpr ⟨U, toSourceCertificate cert⟩
    simpa [erdosSupportSeries,
      Erdos249257.erdosSupportSeries] using hsource

end

end Erdos249257.ExternalVerification257BooleanMobiusCarry
