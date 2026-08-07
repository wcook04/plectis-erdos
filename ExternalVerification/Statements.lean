/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Prime.Nth
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.NumberTheory.Real.Irrational

/-!
# External-verification statement vocabulary

This module contains only the definitions needed to state the nineteen-interface
external-verification packet.  It imports Mathlib, not the proof-bearing
`Erdos249257` modules.  `ExternalVerification.Challenge` and
`ExternalVerification.Solution` therefore share byte-identical statement
constants while the challenge import closure remains independent of the
submitted proofs.
-/

namespace Erdos249257.ExternalVerification

open scoped ENNReal
open Module MeasureTheory

/-! ## One statement-isolated interface for every indexed problem -/

noncomputable def factorialGapTailTerm (D d : ℕ) : ℝ :=
  if D < d then
    (1 : ℝ) / ((((d.factorial : ℤ) - 1 : ℤ)) : ℝ)
  else 0

noncomputable def factorialGapTail (D : ℕ) : ℝ :=
  ∑' d : ℕ, factorialGapTailTerm D d

noncomputable def factorialGapSeries : ℝ := factorialGapTail 1

def strictFacTopRat (x : ℚ) (n : ℕ) : ℤ :=
  ⌊(n.factorial : ℚ) * x⌋ + 1

def factorialGapPrefix (n : ℕ) : ℚ :=
  ∑ k ∈ Finset.Icc 2 n, 1 / ((k.factorial : ℚ) - 1)

noncomputable def strictFacTop (x : ℝ) (n : ℕ) : ℤ :=
  ⌊(n.factorial : ℝ) * x⌋ + 1

noncomputable def factorialGapPredecessorGap (m : ℕ) : ℝ :=
  (strictFacTop ((factorialGapPrefix (m - 1) : ℚ) : ℝ) (m - 1) : ℝ) -
    ((m - 1).factorial : ℝ) *
      ((factorialGapPrefix (m - 1) : ℚ) : ℝ)

noncomputable def factorialGapStepCarry (m : ℕ) : ℤ :=
  -⌊1 + 1 / ((m.factorial : ℝ) - 1) -
      (m : ℝ) * factorialGapPredecessorGap m⌋

def centeredState (a D C : ℤ) : ℤ :=
  D - (a - 1) * C

noncomputable def prime0 (n : ℕ) : ℕ :=
  Nat.nth Nat.Prime n

noncomputable def primeGap0 (n : ℕ) : ℕ :=
  prime0 (n + 1) - prime0 n

noncomputable def primeDyadicTerm (n : ℕ) : ℝ :=
  (prime0 n : ℝ) / 2 ^ (n + 1)

noncomputable def primeGapDyadicTerm (n : ℕ) : ℝ :=
  (primeGap0 n : ℝ) / 2 ^ (n + 1)

def smooth3Val (p q r i j k : ℕ) : ℕ :=
  p ^ i * q ^ j * r ^ k

def threePrimeHeight (p q r x : ℕ) : ℕ :=
  p ^ Nat.log p x * q ^ Nat.log q x * r ^ Nat.log r x

def threePrimeKernelQ (p q r i j k : ℕ) : ℚ :=
  (threePrimeHeight p q r (smooth3Val p q r i j k) : ℚ)⁻¹

def smoothPrefixExponents (p q r x : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  ((Finset.range (Nat.log p x + 1)).product
      ((Finset.range (Nat.log q x + 1)).product
        (Finset.range (Nat.log r x + 1)))).filter
    fun e => smooth3Val p q r e.1 e.2.1 e.2.2 ≤ x

def smoothPrefixLcm (p q r x : ℕ) : ℕ :=
  (smoothPrefixExponents p q r x).lcm
    fun e => smooth3Val p q r e.1 e.2.1 e.2.2

abbrev TotientOddCoreIndex := Fin 2 ⊕ Σ j : ℕ, Fin (2 ^ j)

def SamePositiveRay (a b : ℂ) : Prop :=
  ∃ r : ℝ, 0 < r ∧ b = (r : ℂ) * a

def CoordinatewiseCorridor
    (a b N K Q digit : ℕ) : Prop :=
  0 < a ∧ 0 < Q ∧ 0 < digit ∧ digit ≤ N + K ∧
    a ^ K ∣ Q * digit ∧
    Q * b ^ (N + K + 1) < a ^ (K + 1)

/-- The `(j,r)` dyadic-kernel channel of Euler's totient, restated for the
external verification boundary. -/
def totientKernelSeq (j r : ℕ) : ℕ → ℚ := fun n =>
  Nat.totient (2 ^ j * n + r)

/-- Every dyadic totient channel at levels `0,...,e`. -/
abbrev TotientKernelThroughLevelIndex (e : ℕ) :=
  Σ j : Fin (e + 1), Fin (2 ^ j.val)

/-- The complete finite dyadic kernel through level `e`. -/
def totientKernelThroughLevelFamily (e : ℕ) :
    TotientKernelThroughLevelIndex e → ℕ → ℚ
  | ⟨j, r⟩ => totientKernelSeq j.val r.val

/-- The full dyadic-kernel index. -/
abbrev TotientDyadicKernelIndex := Σ j : ℕ, Fin (2 ^ j)

/-- Every canonical dyadic section of Euler's totient. -/
def fullTotientKernelFamily : TotientDyadicKernelIndex → ℕ → ℚ
  | ⟨j, r⟩ => totientKernelSeq j r.val

/-- The positive-index real Mersenne weight. -/
noncomputable def mersenneWeight (n : ℕ) : ℝ :=
  1 / ((2 : ℝ) ^ n - 1)

/-- The value coded by a set of positive exponents. -/
noncomputable def positiveMersenneSupportValue (A : Set ℕ) : ℝ :=
  ∑' k : ℕ, Set.indicator A mersenneWeight (k + 1)

/-- The normalized Mersenne achievement set. -/
def mersenneAchievementSet : Set ℝ :=
  {x : ℝ | ∃ A : Set ℕ, 0 ∉ A ∧ x = positiveMersenneSupportValue A}

noncomputable def mersenneDigitTerm (k : ℕ) (b : ℕ → Fin 2) : ℝ :=
  ((b k : ℕ) : ℝ) * mersenneWeight (k + 1)

noncomputable def positiveMersenneDigitValue (b : ℕ → Fin 2) : ℝ :=
  ∑' k : ℕ, mersenneDigitTerm k b

def SupportedMersenneDigits (J : Set ℕ) :=
  {b : ℕ → Fin 2 // ∀ k, k ∉ J → b k = 0}

noncomputable def supportedMersenneDigitValue
    (J : Set ℕ) (b : SupportedMersenneDigits J) : ℝ :=
  positiveMersenneDigitValue b.1

def supportedMersenneAchievementSet (J : Set ℕ) : Set ℝ :=
  Set.range (supportedMersenneDigitValue J)

def finiteErdosSum (F : Finset ℕ) (b : ℕ) : ℚ :=
  ∑ n ∈ F, 1 / ((b : ℚ) ^ n - 1)

def rationalBasePrefixQ
    (r s : ℚ) (coeff : ℕ → ℚ) (N : ℕ) : ℚ :=
  ∑ m ∈ Finset.range N,
    coeff (m + 1) * s ^ (m + 1) / r ^ (m + 1)

def rationalBaseClearedTailQ
    (r s B F : ℚ) (coeff : ℕ → ℚ) (N : ℕ) : ℚ :=
  B * r ^ N * (F - rationalBasePrefixQ r s coeff N)

/-- One trusted challenge witness carries the nineteen exact interfaces selected
for the eight-problem external-verification portfolio.  The named theorems in
`Challenge` and `Solution` project these fields, so Comparator still compares
each statement separately while the trusted challenge contains one hole. -/
structure PortfolioClaims (ι : Type*) [Fintype ι] : Prop where
  problem68 :
    Irrational factorialGapSeries ↔
      ∀ B : ℕ, ∃ m : ℕ,
        B < m ∧ ¬(m : ℤ) ∣ strictFacTopRat (factorialGapPrefix m) m
  problem68Carry :
    Irrational factorialGapSeries ↔
      ∀ B : ℕ, ∃ m : ℕ,
        B < m ∧ factorialGapStepCarry m ≠ 1
  problem243 :
    ∀ (a C D magnitude : ℕ → ℕ) (B : ℕ),
      0 < B →
      (∀ n, 1 < a n) →
      (∀ n, 0 < C n) →
      (∀ n, C (n + 1) + D n = a n * C n) →
      (∀ n, D (n + 1) = a n * D n) →
      (∀ n, C (n + 1) ≤ C n + B) →
      (∀ n, 0 < magnitude n) →
      (∀ K, ∃ N, ∀ n, N ≤ n → K * magnitude n < C n) →
      (∀ n, ∃ t e, n ≤ t ∧ 0 < e ∧ e ≤ B ∧
        D t + e = (a t - 1) * C t) →
      False
  problem243Periodic :
    ∀ (a D C e : ℕ → ℕ) (N h M : ℕ),
      0 < h → 0 < M →
      (∀ n, 2 ≤ a n) →
      (∀ n, 0 < e (N + n)) →
      (∀ n, e (N + n) < a (N + n)) →
      (∀ n, D (n + 1) = a n * D n) →
      (∀ n, C (n + 1) = C n + e n) →
      (∀ n, D n + e n = (a n - 1) * C n) →
      (∀ n, e (N + n + h) = e (N + n)) →
      (∀ n, C (N + n + h) = C (N + n) + M) →
      False
  problem249Finite :
    ∀ e : ℕ, 1 ≤ e →
      finrank ℚ
        (Submodule.span ℚ (Set.range (totientKernelThroughLevelFamily e))) =
          2 ^ e + 1
  problem249Infinite :
    ¬ FiniteDimensional ℚ
      (Submodule.span ℚ (Set.range fullTotientKernelFamily))
  problem249Basis :
    Nonempty
      (Basis TotientOddCoreIndex ℚ
        (Submodule.span ℚ (Set.range fullTotientKernelFamily)))
  problem251 : ∀ M : ℕ, ∃ n, M < primeGap0 n
  problem251Equivalence :
    Summable primeDyadicTerm →
      (Irrational (∑' n : ℕ, primeDyadicTerm n) ↔
        Irrational (∑' n : ℕ, primeGapDyadicTerm n))
  problem257Measure : volume mersenneAchievementSet = 1
  problem257FullSupport :
    ∀ b : ℕ, 2 ≤ b →
      Irrational (∑' k : ℕ, (1 : ℝ) / ((b : ℝ) ^ (k + 1) - 1))
  problem257FinitePeriod :
    ∀ (F : Finset ℕ) (b : ℕ)
      (hF : F.Nonempty) (h0 : 0 ∉ F) (hb : 2 ≤ b)
      (hcop : Nat.Coprime b (finiteErdosSum F b).den),
      orderOf (ZMod.unitOfCoprime b hcop) = F.lcm id
  problem257Dichotomy :
    ∀ J : Set ℕ,
      (∃ F : Finset ℕ,
        J = (↑F : Set ℕ)ᶜ ∧
          volume (supportedMersenneAchievementSet J) =
            ((2 : ℝ≥0∞) ^ F.card)⁻¹) ∨
      (Jᶜ.Infinite ∧ volume (supportedMersenneAchievementSet J) = 0)
  problem269 :
    threePrimeKernelQ 2 3 5 0 0 0 *
          threePrimeKernelQ 2 3 5 1 1 0 -
        threePrimeKernelQ 2 3 5 1 0 0 *
          threePrimeKernelQ 2 3 5 0 1 0 =
      -(1 / 15 : ℚ)
  problem269Lcm :
    ∀ {p q r x : ℕ}, p.Prime → q.Prime → r.Prime →
      p ≠ q → p ≠ r → q ≠ r → x ≠ 0 →
      smoothPrefixLcm p q r x = threePrimeHeight p q r x
  problem1041 :
    ∀ (c : ι → ℂ),
      Function.Injective c →
      ∀ { ε : ℝ }, 0 < ε →
        ∃ shift : ℂ, ‖shift‖ < ε ∧
          (∀ i, c i + shift ≠ 0) ∧
          ∀ i j, i ≠ j →
            ¬ SamePositiveRay (c i + shift) (c j + shift)
  problem1041Roots :
    ∀ (f : Polynomial ℂ), f.Monic → 0 < f.natDegree → f.Splits →
      ∀ { ρ ε : ℝ }, 0 ≤ ρ →
      (∀ b ∈ f.roots, ‖b‖ ≤ ρ) →
      0 < ε →
      ((f.natDegree + 1) * ε) ^ (f.natDegree : ℝ)⁻¹ + ρ < 1 →
      ∀ { shift : ℂ }, ‖shift‖ < ε →
      ∀ a : ℂ, (f + Polynomial.C shift).eval a = 0 → ‖a‖ < 1
  problem1049 :
    ∀ {N K Q digit : ℕ}, 1 ≤ N → 1 ≤ K →
      ¬ CoordinatewiseCorridor 3 2 N K Q digit
  problem1049Recurrence :
    ∀ {r s B F : ℚ} {coeff : ℕ → ℚ}, r ≠ 0 → ∀ N : ℕ,
      rationalBaseClearedTailQ r s B F coeff (N + 1) =
        r * rationalBaseClearedTailQ r s B F coeff N -
          B * coeff (N + 1) * s ^ (N + 1)

end Erdos249257.ExternalVerification
