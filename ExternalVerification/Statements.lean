/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Prime.Nth
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic

/-!
# External-verification statement vocabulary

This module contains only the definitions needed to state the configured
external-verification packet.  It imports Mathlib, not the proof-bearing
`Erdos249257` modules.  `ExternalVerification.Challenge` and
`ExternalVerification.Solution` therefore share byte-identical statement
constants while the challenge import closure remains independent of the
submitted proofs.
-/

namespace Erdos249257.ExternalVerification

open scoped ENNReal
open Filter Module MeasureTheory

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

/-! ## Centered-state recovery and Sylvester rigidity -/

/-- The Sylvester successor used by the centered-state defect equation. -/
def sylvesterNext (a : ℤ) : ℤ :=
  a ^ 2 - a + 1

/-- Product-cleared denominator update for the reciprocal-tail state. -/
def nextDenState (a D : ℤ) : ℤ :=
  a * D

/-- Product-cleared reciprocal-tail update for the reciprocal-tail state. -/
def nextTailState (a D C : ℤ) : ℤ :=
  a * C - D

/-! ## Summable negative-mass recovery -/

/-- The normalized negative mass of an integral centered tail step. -/
noncomputable def negativeRelativeMass
    (C : ℕ → ℕ) (E : ℕ → ℤ) (n : ℕ) : ℝ :=
  (Int.natAbs (min (E n) 0) : ℝ) / C n

noncomputable def prime0 (n : ℕ) : ℕ :=
  Nat.nth Nat.Prime n

noncomputable def primeGap0 (n : ℕ) : ℕ :=
  prime0 (n + 1) - prime0 n

noncomputable def primeDyadicTerm (n : ℕ) : ℝ :=
  (prime0 n : ℝ) / 2 ^ (n + 1)

noncomputable def primeGapDyadicTerm (n : ℕ) : ℝ :=
  (primeGap0 n : ℝ) / 2 ^ (n + 1)

/-! ## Coefficient-only natural-friction interface -/

/-- The coefficient emitted by an unrestricted rational-valued carry. -/
def carryCoeff (K : ℕ → ℚ) (n : ℕ) : ℚ :=
  2 * K n - K (n + 1)

/-- The finite dyadic partial sum emitted by `carryCoeff`. -/
def carryPartialSum (K : ℕ → ℚ) (n : ℕ) : ℚ :=
  ∑ i ∈ Finset.range n, carryCoeff K i / 2 ^ (i + 1)

/-- A coherent no-go interface for the tempting claim that rational dyadic
coefficient sums force periodic coefficients.  It records the exact finite
endpoint identity for the linear carry, the linear carry's nonperiodicity,
and the matching nonperiodicity of the actual consecutive-prime gaps.  It
does not assert the infinite limit of the countermodel. -/
def CoefficientOnlyNoGo : Prop :=
  (∀ n : ℕ,
    carryPartialSum (fun j => (j : ℚ)) n = -((n : ℚ) / 2 ^ n)) ∧
  (∀ {h : ℕ}, 0 < h →
    ¬ ∃ N₀, ∀ N, N₀ ≤ N →
      carryCoeff (fun j => (j : ℚ)) (N + h) =
        carryCoeff (fun j => (j : ℚ)) N) ∧
  (∀ {h : ℕ}, 0 < h →
    ¬ ∃ N₀, ∀ N, N₀ ≤ N →
      primeGap0 (N + h + 1) = primeGap0 (N + 1))

/-! ## Abstract dyadic-tail classification vocabulary -/

def DyadicTailRecurrence (g : ℕ → ℤ) (T : ℕ → ℚ) : Prop :=
  ∀ N, T (N + 1) = 2 * T N - g (N + 1)

def tailShift (T : ℕ → ℚ) (h N : ℕ) : ℚ :=
  T (N + h) - T N

def RatIntegral (x : ℚ) : Prop :=
  ∃ z : ℤ, x = z

def RealDyadicTailRecurrence (g : ℕ → ℤ) (T : ℕ → ℝ) : Prop :=
  ∀ N, T (N + 1) = 2 * T N - g (N + 1)

def realTailShift (T : ℕ → ℝ) (h N : ℕ) : ℝ :=
  T (N + h) - T N

def RealIntegral (x : ℝ) : Prop :=
  ∃ z : ℤ, x = z

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

def smoothExponentBox (hp hq hr : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  (Finset.range (hp + 1)).product
    ((Finset.range (hq + 1)).product (Finset.range (hr + 1)))

def smoothPointHeight (p q r : ℕ) (e : ℕ × ℕ × ℕ) : ℕ :=
  threePrimeHeight p q r (smooth3Val p q r e.1 e.2.1 e.2.2)

def smoothHeightFiber
    (p q r hp hq hr H : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  (smoothExponentBox hp hq hr).filter fun e => smoothPointHeight p q r e = H

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

/-! ## All-base totient-kernel index reduction -/

/-- The `(j,r)` base-`k` kernel channel of Euler's totient. -/
def allBaseTotientKernelSeq (k j r : ℕ) : ℕ → ℚ := fun n =>
  Nat.totient (k ^ j * n + r)

/-- Every dyadic totient channel at levels `0,...,e`. -/
abbrev TotientKernelThroughLevelIndex (e : ℕ) :=
  Σ j : Fin (e + 1), Fin (2 ^ j.val)

/-- The complete finite dyadic kernel through level `e`. -/
def totientKernelThroughLevelFamily (e : ℕ) :
    TotientKernelThroughLevelIndex e → ℕ → ℚ
  | ⟨j, r⟩ => totientKernelSeq j.val r.val

/-- The two distinguished zero-residue channels in the all-base reduction. -/
inductive TotientKernelHeadIndex
  | F00
  | F10
  deriving DecidableEq

instance : Fintype TotientKernelHeadIndex where
  elems := {.F00, .F10}
  complete := by
    intro i
    cases i <;> simp

/-- Coordinates for nonzero canonical sections through levels `1,...,e`. -/
abbrev TotientKernelSectionIndex (k e : ℕ) :=
  Σ j : Fin e, Fin (k ^ j.val) × Fin (k - 1)

/-- The complete finite-level all-base index. -/
abbrev TotientKernelIndex (k e : ℕ) :=
  TotientKernelHeadIndex ⊕ TotientKernelSectionIndex k e

/-- The positive level represented by a canonical section coordinate. -/
def totientKernelSectionLevel {k e : ℕ}
    (i : TotientKernelSectionIndex k e) : ℕ :=
  i.1.val + 1

/-- The residue represented by a quotient/nonzero-digit coordinate. -/
def totientKernelSectionResidue {k e : ℕ}
    (i : TotientKernelSectionIndex k e) : ℕ :=
  k * i.2.1.val + (i.2.2.val + 1)

/-- The filtration-compatible all-base family of canonical channels. -/
def canonicalAllBaseTotientKernelFamily (k e : ℕ) :
    TotientKernelIndex k e → ℕ → ℚ
  | Sum.inl .F00 => allBaseTotientKernelSeq k 0 0
  | Sum.inl .F10 => allBaseTotientKernelSeq k 1 0
  | Sum.inr i => allBaseTotientKernelSeq k
      (totientKernelSectionLevel i) (totientKernelSectionResidue i)

/-- Every base-`k` totient channel through level `e`. -/
abbrev AllBaseTotientKernelThroughLevelIndex (k e : ℕ) :=
  Σ j : Fin (e + 1), Fin (k ^ j.val)

/-- The complete finite all-base kernel through level `e`. -/
def allBaseTotientKernelThroughLevelFamily (k e : ℕ) :
    AllBaseTotientKernelThroughLevelIndex k e → ℕ → ℚ
  | ⟨j, r⟩ => allBaseTotientKernelSeq k j.val r.val

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

/-! ## Boolean–Möbius exact-row dynamics -/

/- These statement-side definitions preserve the exact rational greedy-skip
   socket used by the proof-bearing Boolean–Möbius row constructor. -/
def mersenneWeightRat (n : ℕ) : ℚ :=
  1 / ((2 : ℚ) ^ n - 1)

def greedyMersenneRemainderRat (x : ℚ) : ℕ → ℚ
  | 0 => x
  | n + 1 =>
      if mersenneWeightRat (n + 1) ≤ greedyMersenneRemainderRat x n then
        greedyMersenneRemainderRat x n - mersenneWeightRat (n + 1)
      else
        greedyMersenneRemainderRat x n

/- Positive skips are required cofinally; finite exact rows alone do not
   supply this hypothesis. -/
def CofinalPositiveHalfGreedySkips : Prop :=
  ∀ N : ℕ, ∃ c : ℕ,
    max N 4 ≤ c ∧
      0 < greedyMersenneRemainderRat (1 / 2 : ℚ) (c - 1) ∧
      greedyMersenneRemainderRat (1 / 2 : ℚ) (c - 1) <
        mersenneWeightRat c

/-! ## Fixed-precision valuation--unit no-go vocabulary -/

structure VUSymbol where
  valuation : ℕ
  unit : ℤ

def VUCompatible (u : ℕ) (σ : VUSymbol) (c : ℤ) : Prop :=
  Odd σ.unit ∧ ∃ z : ℤ,
    c = (2 : ℤ) ^ σ.valuation * (σ.unit + (2 : ℤ) ^ u * z)

def vuModulus (u : ℕ) (σ : VUSymbol) : ℤ :=
  (2 : ℤ) ^ (σ.valuation + u)

def vuRadius (u : ℕ) (σ : VUSymbol) : ℤ :=
  (2 : ℤ) ^ (σ.valuation + u - 1)

def vuBaseDigit (σ : VUSymbol) : ℤ :=
  (2 : ℤ) ^ σ.valuation * σ.unit

def vuCentredStep (u : ℕ) (σ : VUSymbol) (e : ℤ) : ℤ :=
  let R := vuRadius u σ
  let M := vuModulus u σ
  (2 * e + vuBaseDigit σ + R) % M - R

inductive VUOrbit (u : ℕ) : ℤ → List VUSymbol → List ℤ → Prop
  | nil (e : ℤ) : VUOrbit u e [] []
  | cons (e c e' : ℤ) (σ : VUSymbol) (symbols : List VUSymbol)
      (states : List ℤ) (hcompat : VUCompatible u σ c)
      (hstep : e' = 2 * e + c) (htail : VUOrbit u e' symbols states) :
      VUOrbit u e (σ :: symbols) (e' :: states)

/-! The exact Boolean seam used by the half-membership classification.  These
statement-side definitions intentionally mirror the finite integer-greedy
construction without importing its proof-bearing source module. -/

def seamTruncatedMersenneWeight (s d : ℕ) : ℕ :=
  4 ^ s / (2 ^ d - 1)

def seamSubsetTarget (s : ℕ) : ℕ :=
  2 ^ (2 * s - 1) - 2 ^ s

def seamWeightsFrom (s d : ℕ) : List ℕ :=
  if h : d < s then
    seamTruncatedMersenneWeight s d :: seamWeightsFrom s (d + 1)
  else
    []
termination_by s - d
decreasing_by omega

def seamWeights (s : ℕ) : List ℕ :=
  seamWeightsFrom s 2

theorem seamWeightsFrom_length_eq (s d : ℕ) :
    (seamWeightsFrom s d).length = s - d := by
  by_cases hds : d < s
  · rw [seamWeightsFrom, dif_pos hds, List.length_cons,
      seamWeightsFrom_length_eq s (d + 1)]
    omega
  · rw [seamWeightsFrom, dif_neg hds]
    simp
    omega
termination_by s - d
decreasing_by omega

@[simp] theorem seamWeights_length_eq (s : ℕ) :
    (seamWeights s).length = s - 2 := by
  exact seamWeightsFrom_length_eq s 2

def seamWeightedBoolSum : List ℕ → List Bool → ℕ
  | w :: ws, true :: bs => w + seamWeightedBoolSum ws bs
  | _ :: ws, false :: bs => seamWeightedBoolSum ws bs
  | _, _ => 0

def seamIntegerGreedyBits : List ℕ → ℕ → List Bool
  | [], _ => []
  | w :: ws, C =>
      if w ≤ C then
        true :: seamIntegerGreedyBits ws (C - w)
      else
        false :: seamIntegerGreedyBits ws C

theorem seamIntegerGreedyBits_length (weights : List ℕ) (C : ℕ) :
    (seamIntegerGreedyBits weights C).length = weights.length := by
  induction weights generalizing C with
  | nil => simp [seamIntegerGreedyBits]
  | cons w ws ih =>
      simp only [seamIntegerGreedyBits]
      split <;> simp [ih]

abbrev SeamRowWord (s : ℕ) := Fin (s - 2) → Bool

namespace SeamRowWord

def ofList {s : ℕ} (bits : List Bool) (hlen : bits.length = s - 2) :
    SeamRowWord s :=
  fun i => bits.get (Fin.cast hlen.symm i)

def terminal {s : ℕ} (hs : 3 ≤ s) (b : SeamRowWord (s + 1)) : Bool :=
  b ⟨s - 2, by omega⟩

end SeamRowWord

def seamGreedyWord (s : ℕ) : SeamRowWord s :=
  SeamRowWord.ofList
    (seamIntegerGreedyBits (seamWeights s) (seamSubsetTarget s))
    (by rw [seamIntegerGreedyBits_length, seamWeights_length_eq])

def SeamGreedyUnboundedTerminalFalse : Prop :=
  ∀ N : ℕ, ∃ p : ℕ, ∃ hp5 : 5 ≤ p,
    N ≤ p ∧
      SeamRowWord.terminal (by omega)
        (seamGreedyWord (p + 1)) = false

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

/-! ## Rational-support shifted odd-tail state -/

noncomputable def supportCoeff (A : Set ℕ) (n : ℕ) : ℕ :=
  letI := Classical.decPred fun d : ℕ => d ∈ A
  (n.divisors.filter fun d => d ∈ A).card

noncomputable def erdosSupportSeries (b : ℕ) (A : Set ℕ) : ℝ :=
  ∑' a : ℕ, Set.indicator A (fun a => (1 : ℝ) / ((b : ℝ) ^ a - 1)) a

noncomputable def binaryCoeffTail (c : ℕ → ℕ) (N : ℕ) : ℝ :=
  ∑' j : ℕ, (c (N + j + 1) : ℝ) / (2 : ℝ) ^ (j + 1)

/-! ## Totient carry anti-compression -/

/- The coefficient series and tempered orbit are restated here so the
   Challenge remains independent of the proof-bearing Erdos249257 modules. -/
noncomputable def binaryCoeffSeries (c : ℕ → ℕ) : ℝ :=
  ∑' n : ℕ, (c (n + 1) : ℝ) / (2 : ℝ) ^ (n + 1)

/-! The exact integral recurrence and subexponential boundary for a binary
carry orbit. -/
def IsTemperedBinaryOrbit (c : ℕ → ℕ) (v : ℕ) (u : ℕ → ℤ) : Prop :=
  (∀ N : ℕ,
      u (N + 1) = 2 * u N - ((v * c (N + 1) : ℕ) : ℤ)) ∧
    Tendsto (fun N : ℕ ↦ (u N : ℝ) / (2 : ℝ) ^ N) atTop (nhds 0)

abbrev TotientCarryIndex (e : ℕ) :=
  Σ j : Fin e, Fin (2 ^ (j.val + 1))

def carryKernelSeq (u : ℕ → ℤ) (j r : ℕ) : ℕ → ℚ := fun n =>
  u (2 ^ j * n + r)

def canonicalCarryKernelFamily (u : ℕ → ℤ) (e : ℕ) :
    TotientCarryIndex e → ℕ → ℚ
  | ⟨j, r⟩ => carryKernelSeq u (j.val + 1) r.val

def CarrySectionsEventuallyPeriodicMod
    (v h N₀ : ℕ) (u : ℕ → ℤ) : Prop :=
  ∀ j r n : ℕ, N₀ ≤ n →
    u (2 ^ j * n + r) ≡ u (2 ^ j * (n + h) + r) [ZMOD (v : ℤ)]

/-! ## Weighted-phase carry observer -/

/- These statement-side names avoid the #257 carry-quotient vocabulary while
   preserving the exact integer residue/coboundary interface from #269. -/
def weightedCarryResidue (B c : ℤ) : ℤ := c % B

def weightedCarryQuotient (B c : ℤ) : ℤ := c / B

def weightedResidueDigit (B base residue nextResidue : ℤ) : ℤ :=
  (base * residue - nextResidue) / B

/-! ## Boolean–Möbius carry certificate -/

/-- The integer carry quotient extracted from a scaled binary orbit. -/
def carryQuotient (q : ℕ) (U : ℕ → ℤ) (n : ℕ) : ℤ :=
  if n = 0 then 0 else (2 * U (n - 1) - U n) / (q : ℤ)

/-- The carry quotient packaged as an integer-valued arithmetic function. -/
def carryQuotientAF (q : ℕ) (U : ℕ → ℤ) : ArithmeticFunction ℤ :=
  ⟨carryQuotient q U, by simp [carryQuotient]⟩

/-- A quotient-only rational-support certificate: positive and
square-root-bounded, with divisible carry differences and Boolean Möbius
transform.  The support is reconstructed from that transform in the source
theorem; it is not supplied as an extra hypothesis here. -/
structure BooleanMobiusCarryCertificate (p : ℤ) (q : ℕ) (U : ℕ → ℤ) : Prop where
  initial : U 0 = p
  positive : ∀ N : ℕ, 0 < U N
  sqrtBound : ∀ N : ℕ, (U N : ℝ) ≤
    (q : ℝ) * (2 * Real.sqrt (N : ℝ) + 4)
  divisible : ∀ N : ℕ, (q : ℤ) ∣ 2 * U N - U (N + 1)
  mobiusBoolean : ∀ n : ℕ, 0 < n →
    (ArithmeticFunction.moebius * carryQuotientAF q U) n = 0 ∨
      (ArithmeticFunction.moebius * carryQuotientAF q U) n = 1

/-! ## Orthogonal-petal sunflower conditional interface -/

/-- Statement-side copy of the finite-core orthogonal-petal bouquet data.

This mirrors the proof-bearing source structure without importing it into the
trusted Challenge.  `Solution` supplies the explicit field-by-field transport
to the source structure before invoking the landed conditional theorem.
-/
structure OrthogonalPetalBouquet (A : Set ℕ) where
  Q : ℕ
  Q_pos : 0 < Q
  exceptional : Finset ℕ
  core : ℕ → ℕ
  petal : ℕ → ℕ
  exceptional_pos : ∀ d ∈ exceptional, 0 < d
  exceptional_dvd_Q : ∀ d ∈ exceptional, d ∣ Q
  core_pos : ∀ i, 0 < core i
  core_dvd_Q : ∀ i, core i ∣ Q
  petal_one_lt : ∀ i, 1 < petal i
  petal_coprime_Q : ∀ i, Nat.Coprime (petal i) Q
  petal_pairwise : ∀ i j, i ≠ j → Nat.Coprime (petal i) (petal j)
  support_eq :
    A = (↑exceptional : Set ℕ) ∪ Set.range (fun i => core i * petal i)
  summable_inv_petal : Summable (fun i => (1 : ℝ) / (petal i : ℝ))

/-- The exact analytic selector left open by the sunflower route. -/
def SunflowerForcedSlotTailSelection (A : Set ℕ) : Prop :=
  ∀ K : ℕ, 0 < K → ∃ N : ℕ,
    (2 ^ K ∣ ∑ r ∈ Finset.Icc 1 K,
      supportCoeff A (N + r) * 2 ^ (K - r)) ∧
    binaryCoeffTail (supportCoeff A) (N + K) ≤ 16

noncomputable def compositeDilationDefect (A : Set ℕ) (a x : ℕ) : ℕ :=
  by
    classical
    exact ((a * x).divisors.filter fun d =>
      d ∈ A ∧ ¬ d ∣ x ∧ d ≠ a).card

def IntBand (p D q : ℤ) : Prop :=
  q * (2 * q + 1) * p < 2 * D * (3 * q + 1) ∧
    2 * D * (3 * q + 2) < 2 * p * q * (q + 1)

def finiteErdosSum (F : Finset ℕ) (b : ℕ) : ℚ :=
  ∑ n ∈ F, 1 / ((b : ℚ) ^ n - 1)

def rationalBasePrefixQ
    (r s : ℚ) (coeff : ℕ → ℚ) (N : ℕ) : ℚ :=
  ∑ m ∈ Finset.range N,
    coeff (m + 1) * s ^ (m + 1) / r ^ (m + 1)

def rationalBaseClearedTailQ
    (r s B F : ℚ) (coeff : ℕ → ℚ) (N : ℕ) : ℚ :=
  B * r ^ N * (F - rationalBasePrefixQ r s coeff N)

/-! ## Rectangular Hermite--Padé threshold comparison -/

/-- Quadratic Archimedean decay expression in the explicit rectangular
Hermite--Padé exponent model. -/
noncomputable def hpDecay (rho sigma : ℝ) : ℝ :=
  (1 + rho ^ 2) / 2 + sigma

/-- Homogeneous polynomial-width expression in the explicit rectangular
Hermite--Padé exponent model. -/
noncomputable def hpHeight (rho sigma : ℝ) : ℝ :=
  (1 + rho) ^ 2 / 2 + sigma * (1 + rho)

/-- Cyclotomic denominator-saving expression in the explicit exponent model. -/
noncomputable def hpCyclotomicSaving (sigma : ℝ) : ℝ :=
  3 * sigma ^ 2 / Real.pi ^ 2

/-- Rational-base height threshold associated with the explicit rectangular
two-function exponent model. -/
noncomputable def hpThreshold (rho sigma : ℝ) : ℝ :=
  (hpDecay rho sigma - hpCyclotomicSaving sigma) /
    (hpHeight rho sigma + hpDecay rho sigma)

/-- Denominator-cleared difference from the classical one-function threshold.

This is the load-bearing polynomial gap whose sign and unique zero transport
to the threshold comparison.  The interface deliberately records only this
explicit model, not a universal Hermite--Padé theorem. -/
noncomputable def hpClearedGap (rho sigma : ℝ) : ℝ :=
  (Real.pi ^ 2 + 2) * hpDecay rho sigma - 6 * sigma ^ 2 -
    (Real.pi ^ 2 - 2) * hpHeight rho sigma

/-! ## Stern--Brocot run stability -/

/-- The direction-free continuant state at alternating run boundaries. -/
def runBoundaryPair : List ℕ → ℕ × ℕ
  | [] => (1, 1)
  | n :: ns =>
      let p := runBoundaryPair ns
      (n * p.1 + p.2, p.1)

/-- The arithmetic height of an alternating Stern--Brocot run word. -/
def runHeight (ns : List ℕ) : ℕ :=
  (runBoundaryPair ns).1 + (runBoundaryPair ns).2

/-- Replace every nonnegative defect by the positive run length `1 + e`. -/
def defectRunLengths (e : List ℕ) : List ℕ :=
  e.map Nat.succ

/-- The closed cylinder mass at a positive Stern--Brocot node. -/
noncomputable def cylinderMass (a b : ℕ+) : ℝ :=
  1 / (((2 : ℝ) ^ (a : ℕ) - 1) * ((2 : ℝ) ^ (b : ℕ) - 1))

/-! ## LCM factor-ideal shift-algebra no-go -/

def periodLcm : ℕ → ℕ
  | 0 => 1
  | t + 1 => Nat.lcm (periodLcm t) (t + 1)

/-- The binary cyclotomic layer whose clean prime factors provide exact
period-ray anchors. -/
noncomputable def binaryCyclotomicLayer (n : ℕ) : ℕ :=
  ((Polynomial.cyclotomic n ℤ).eval (2 : ℤ)).natAbs

/-- The totient tail whose actual-LCM differences form the diagonal orbit. -/
noncomputable def totientTail (N : ℕ) : ℝ :=
  ∑' j : ℕ, (Nat.totient (N + 1 + j) : ℝ) / 2 ^ (j + 1)

/-! ## Period-killer window and carry vocabulary -/

def deltaTotient (h n : ℕ) : ℤ :=
  (Nat.totient (n + h) : ℤ) - (Nat.totient n : ℤ)

def windowDiscrepancy (h N L : ℕ) : ℤ :=
  ∑ j ∈ Finset.range L,
    ((Nat.totient (N + h + 1 + j) : ℤ) -
      (Nat.totient (N + 1 + j) : ℤ)) * 2 ^ (L - 1 - j)

def certifiedKill (h N L : ℕ) : Prop :=
  (N + h + L + 2 : ℤ) < windowDiscrepancy h N L % 2 ^ L ∧
    windowDiscrepancy h N L % 2 ^ L < 2 ^ L - (N + h + L + 2)

noncomputable def windowFirstCos (h N L : ℕ) : ℝ :=
  Real.cos
    (2 * Real.pi *
      (((windowDiscrepancy h N L % (2 ^ L : ℤ) : ℤ) : ℝ) /
        ((2 ^ L : ℤ) : ℝ)))

noncomputable def windowFirstAngle (h N L : ℕ) : ℝ :=
  2 * Real.pi *
    (((windowDiscrepancy h N L % (2 ^ L : ℤ) : ℤ) : ℝ) /
      ((2 ^ L : ℤ) : ℝ))

noncomputable def windowFirstExp (h N L : ℕ) : ℂ :=
  Complex.exp ((windowFirstAngle h N L : ℂ) * Complex.I)

/-! ## Infinite tail-orbit phase-density and prime-index escape -/

/-- First additive character of the infinite totient tail difference. -/
noncomputable def tailOrbitFirstExp (h N : ℕ) : ℂ :=
  Complex.exp
    (((2 * Real.pi * (totientTail (N + h) - totientTail N) : ℝ) : ℂ) *
      Complex.I)

/-- On arbitrarily late dyadic blocks, the mean real part of the infinite
tail-orbit phase is at most `89/100`.  This is an explicit producer premise.
-/
noncomputable def TotientTailOrbitBlockGap : Prop :=
  ∀ h : ℕ, 0 < h →
    ∀ X₀ : ℕ, ∃ X : ℕ,
      max X₀ 1 ≤ X ∧
      (∑ N ∈ Finset.Ico X (2 * X), (tailOrbitFirstExp h N).re)
        ≤ (89 / 100 : ℝ) * X

/-- On arbitrarily late dyadic blocks, at least an `11/100` proportion of
tail-orbit phases have nonpositive real part. -/
noncomputable def TotientTailOrbitNonpositiveBlockDensity : Prop :=
  ∀ h : ℕ, 0 < h →
    ∀ X₀ : ℕ, ∃ X : ℕ,
      max X₀ 1 ≤ X ∧
      (11 / 100 : ℝ) * X ≤
        ((Finset.Ico X (2 * X)).filter
          fun N => (tailOrbitFirstExp h N).re ≤ 0).card

/-- Cofinal prime indices at which the infinite-orbit real part is strictly
below `9/10`; this is the selected endpoint-facing producer interface. -/
def DTWNaturalPrimeTailOrbitStrictGap : Prop :=
  ∀ h : ℕ, 0 < h →
    ∀ N₀ : ℕ, ∃ p : ℕ,
      max (N₀ + h + 1) (h + 5) ≤ p ∧
      p.Prime ∧
      (tailOrbitFirstExp h (p - h - 1)).re < (9 / 10 : ℝ)

def endpointSurvivor (h N L : ℕ) (z : ℤ) : Prop :=
  |z| ≤ (N + h + L + 2 : ℤ) ∧
    z % 2 ^ L = windowDiscrepancy h N L % 2 ^ L

def carryOrbit (h N : ℕ) (d : ℤ) : ℕ → ℤ
  | 0 => d
  | i + 1 => 2 * carryOrbit h N d i - deltaTotient h (N + i + 1)

/-- The actual power-two LCM height used by the diagonal orbit. -/
def actualLcmHeight (a : ℕ) : ℕ :=
  periodLcm (2 ^ a)

/-- The actual LCM-diagonal tail orbit at exponent `a`. -/
noncomputable def actualLcmTailOrbit (a : ℕ) : ℝ :=
  totientTail (2 * actualLcmHeight a) - totientTail (actualLcmHeight a)

/-! ## Quantitative actual-LCM orbit separation -/

def diagonalWindowIncrement (t s : ℕ) : ℤ :=
  (Nat.totient (2 * periodLcm t + s) : ℤ) -
    (Nat.totient (periodLcm t + s) : ℤ)

def diagonalAdjacentSuffixRawBlock (t J m : ℕ) : ℤ :=
  (∑ r ∈ Finset.range m,
      diagonalWindowIncrement t (J + 1 + r) * 2 ^ (m - 1 - r)) +
    diagonalWindowIncrement t (J + m + 1)

def canonicalAdjacentSuffixDepth (t : ℕ) : ℕ :=
  Nat.log2 (periodLcm t) + 10

def oddGuardedCanonicalAdjacentSuffixDepth (t : ℕ) : ℕ :=
  let m := canonicalAdjacentSuffixDepth t
  if Even m then m + 1 else m

noncomputable def actualLcmRawApprox (a q : ℕ) : ℝ :=
  (diagonalAdjacentSuffixRawBlock (2 ^ a) 0 (2 * q + 1) : ℝ) /
    (2 : ℝ) ^ (2 * q + 1)

noncomputable def actualLcmRawErrorRadius (a q : ℕ) : ℝ :=
  ((2 * actualLcmHeight a + 2 * q + 3 : ℕ) : ℝ) /
    (2 : ℝ) ^ (2 * q + 1)

/-- Cofinal quantitative anti-concentration of the actual LCM tail orbit at
the canonical odd ranks.  The supply is the explicit open arithmetic input;
the downstream irrationality implication is theorem transport, not a claim
that this supply has been constructed. -/
def PowerTwoActualLcmOrbitSeparationSupply : Prop :=
  ∀ a₀ : ℕ, ∃ a q : ℕ, max 2 a₀ ≤ a ∧
    oddGuardedCanonicalAdjacentSuffixDepth (2 ^ a) = 2 * q + 1 ∧
    ∀ z : ℤ,
      (1 : ℝ) / 32 + actualLcmRawErrorRadius a q ≤
        |actualLcmTailOrbit a - (z : ℝ)|

/-- Cofinal non-integrality of the actual power-two LCM-diagonal orbit. -/
def PowerTwoActualLcmOrbitNonintegralitySupply : Prop :=
  ∀ a₀ : ℕ, ∃ a, a₀ ≤ a ∧
    actualLcmTailOrbit a ∉ Set.range ((↑) : ℤ → ℝ)

/-! ## Finite actual foreign-residue projection -/

def mersenne (n : ℕ) : ℕ := 2 ^ n - 1

def squarefreeKernel (n : ℕ) : ℕ := ∏ p ∈ n.primeFactors, p

def mobiusNumerator (r : ℕ) : ℤ :=
  ∑ s ∈ r.primeFactors.powerset,
    (-1 : ℤ) ^ s.card *
      ((r / s.prod id : ℕ) : ℤ) *
        (((mersenne r) / (mersenne (s.prod id)) : ℕ) : ℤ)

def baseMobiusShadow (r : ℕ) : ℚ :=
  Rat.divInt (mobiusNumerator r) (mersenne r : ℤ)

def numericMobiusShadow (H : ℕ) : ℚ :=
  baseMobiusShadow (squarefreeKernel H) / (squarefreeKernel H : ℚ)

def diagonalCoefficient (H : ℕ) : ℕ := 2 ^ H * (2 ^ H - 1)

noncomputable def scaleExplicitShadowRat (H : ℕ) : ℚ :=
  (H : ℚ) * numericMobiusShadow H

noncomputable def scaleExplicitShadow (H : ℕ) : ℝ :=
  (scaleExplicitShadowRat H : ℝ)

noncomputable def scaleDiagonalTailDifference (H : ℕ) : ℝ :=
  totientTail (2 * H) - totientTail H

noncomputable def scaleForeignDefect (H : ℕ) : ℝ :=
  scaleDiagonalTailDifference H - scaleExplicitShadow H

def ScaleFullTargetHit (H : ℕ) : Prop :=
  ∃ z : ℤ, ((scaleExplicitShadowRat H).den : ℝ) * scaleForeignDefect H =
    (-(scaleExplicitShadowRat H).num : ℝ) +
      ((scaleExplicitShadowRat H).den : ℝ) * (z : ℝ)

def residueOffset (d N : ℕ) : ℕ := d - N % d

noncomputable def foreignResidueKernel (d N : ℕ) : ℝ :=
  ((ArithmeticFunction.moebius d : ℤ) : ℝ) *
    (2 : ℝ) ^ (d - residueOffset d N) *
      (((N + residueOffset d N : ℕ) : ℝ) /
          ((d : ℝ) * ((2 : ℝ) ^ d - 1)) +
        1 / (((2 : ℝ) ^ d - 1) ^ 2))

noncomputable def stableResidueFactor (d : ℕ) : ℝ :=
  1 / ((2 : ℝ) ^ d - 1) + 1 / (((2 : ℝ) ^ d - 1) ^ 2)

noncomputable def residueIncrement (d H : ℕ) : ℝ :=
  foreignResidueKernel d (2 * H) - foreignResidueKernel d H

noncomputable def foreignTailWindow (H D L : ℕ) : ℝ :=
  ∑ d ∈ Finset.Icc (D + 1) L, residueIncrement d H

noncomputable def foreignComplementBound (H D : ℕ) : ℝ :=
  (diagonalCoefficient H : ℝ) *
    (2 / (2 : ℝ) ^ D + 4 / (3 * (4 : ℝ) ^ D))

noncomputable def projectedForeignDefect (H D : ℕ) : ℝ :=
  ∑ d ∈ Finset.Icc 1 D, if d ∣ H then 0 else residueIncrement d H

noncomputable def projectedDivisorChannels (H D : ℕ) : ℝ :=
  ∑ d ∈ Finset.Icc 1 D, if d ∣ H then residueIncrement d H else 0

noncomputable def finiteResidueDiagonal (H D : ℕ) : ℝ :=
  ∑ d ∈ Finset.Icc 1 D, residueIncrement d H

def ControlledForeignProjection (H D : ℕ) : Prop :=
  |scaleForeignDefect H - projectedForeignDefect H D| ≤
    foreignComplementBound H D

def ProjectedFullTargetSeparation (H D : ℕ) : Prop :=
  ∀ z : ℤ, foreignComplementBound H D <
    |scaleExplicitShadow H + projectedForeignDefect H D - (z : ℝ)|

/-! ## First-harmonic pivot supplier fibres -/

/-- Offset of the first-harmonic pivot argument `N + (L-s+1)`. -/
def pivotOffset (L s : ℕ) : ℕ := L - s + 1

/-- The integer argument at which the largest-prime pivot is selected. -/
def pivotArgument (N L s : ℕ) : ℕ := N + pivotOffset L s

/-- Canonical largest-prime choice from the finite prime-factor set. -/
noncomputable def pivotPrime (N L s : ℕ) : ℕ :=
  (pivotArgument N L s).primeFactors.toList.foldl Nat.max 1

/-- Cofactor associated to the canonical largest-prime choice. -/
noncomputable def pivotCofactor (N L s : ℕ) : ℕ :=
  pivotArgument N L s / pivotPrime N L s

/-- Exact clean-supplier predicate used by the pivot fibre. -/
noncomputable def pivotSupplier (X L s N : ℕ) : Prop :=
  let p := pivotPrime N L s
  let m := pivotCofactor N L s
  p.Prime ∧ m * p = pivotArgument N L s ∧ 0 < m ∧
    m ≤ Nat.sqrt X / 2 ∧ 2 * Nat.sqrt X < p

noncomputable instance (X L s N : ℕ) : Decidable (pivotSupplier X L s N) := by
  unfold pivotSupplier
  infer_instance

noncomputable def pivotSupplierBases (X L s : ℕ) : Finset ℕ :=
  (Finset.Ico X (2 * X)).filter (pivotSupplier X L s)

noncomputable def pivotFiber (X L s m : ℕ) : Finset ℕ :=
  (pivotSupplierBases X L s).filter fun N => pivotCofactor N L s = m

/-- The shifted prime interval parametrising one supplier fibre. -/
def pivotSupplierPrimes (X L s m : ℕ) : Finset ℕ :=
  (Finset.range (2 * X + pivotOffset L s + 1)).filter fun p =>
    p.Prime ∧ X + pivotOffset L s ≤ m * p ∧
      m * p < 2 * X + pivotOffset L s

/-- Convert a supplier prime to its canonical window base. -/
def pivotBaseOfPrime (L s m p : ℕ) : ℕ := m * p - pivotOffset L s

noncomputable def pivotPrimeAngle (h L s m p : ℕ) : ℝ :=
  2 * Real.pi *
    (((2 : ℝ) ^ h - 1) * (Nat.totient m : ℝ) * ((p : ℝ) - 1) /
      (2 * (2 : ℝ) ^ (L - s)))

noncomputable def pivotPrimePhase (h L s m p : ℕ) : ℂ :=
  Complex.exp ((pivotPrimeAngle h L s m p : ℂ) * Complex.I)

noncomputable def pivotResidualWeight (h N L s m p : ℕ) : ℂ :=
  windowFirstExp h N L / pivotPrimePhase h L s m p

def pivotGoodCofactor (L s N : ℕ) (η : ℝ) : Prop :=
  η * pivotCofactor N L s ≤ Nat.totient (pivotCofactor N L s)

noncomputable instance (L s N : ℕ) (η : ℝ) :
    Decidable (pivotGoodCofactor L s N η) := by
  classical exact inferInstance

noncomputable def pivotGoodBases (X L s : ℕ) (η : ℝ) : Finset ℕ :=
  (pivotSupplierBases X L s).filter fun N => pivotGoodCofactor L s N η

noncomputable def pivotBadBases (X L s : ℕ) (η : ℝ) : Finset ℕ :=
  (pivotSupplierBases X L s).filter fun N => ¬pivotGoodCofactor L s N η

noncomputable def pivotNonSupplierBases (X L s : ℕ) : Finset ℕ :=
  (Finset.Ico X (2 * X)).filter fun N => ¬pivotSupplier X L s N

noncomputable def pivotPhaseAt (h N L s : ℕ) : ℂ :=
  pivotPrimePhase h L s (pivotCofactor N L s) (pivotPrime N L s)

noncomputable def pivotResidualAt (h N L s : ℕ) : ℂ :=
  windowFirstExp h N L / pivotPhaseAt h N L s

noncomputable def pivotFiberMean (h X L s m : ℕ) : ℂ :=
  ((pivotFiber X L s m).card : ℂ)⁻¹ *
    ∑ N ∈ pivotFiber X L s m, pivotPhaseAt h N L s

noncomputable def pivotCenteredCorrelation
    (h X L s : ℕ) (η : ℝ) : ℂ :=
  ∑ N ∈ pivotGoodBases X L s η,
    pivotResidualAt h N L s *
      (pivotPhaseAt h N L s - pivotFiberMean h X L s (pivotCofactor N L s))

noncomputable def pivotFiberMeanContribution
    (h X L s : ℕ) (η : ℝ) : ℂ :=
  ∑ N ∈ pivotGoodBases X L s η,
    pivotResidualAt h N L s *
      pivotFiberMean h X L s (pivotCofactor N L s)

noncomputable def pivotBadContribution
    (h X L s : ℕ) (η : ℝ) : ℂ :=
  ∑ N ∈ pivotBadBases X L s η, windowFirstExp h N L

noncomputable def pivotNonSupplierContribution (h X L s : ℕ) : ℂ :=
  ∑ N ∈ pivotNonSupplierBases X L s, windowFirstExp h N L

def PivotBudgetAt (h X L s : ℕ) (η : ℝ) : Prop :=
  (pivotCenteredCorrelation h X L s η).re ≤ (14 / 25 : ℝ) * X ∧
  ‖pivotFiberMeanContribution h X L s η‖ ≤ (1 / 100 : ℝ) * X ∧
  ‖pivotBadContribution h X L s η‖ ≤ (1 / 100 : ℝ) * X ∧
  ‖pivotNonSupplierContribution h X L s‖ ≤ (8 / 25 : ℝ) * X

def DTWPivotResidualDecorrelation : Prop :=
  ∀ h : ℕ, 0 < h → ∃ s : ℕ, 0 < s ∧ ∃ η : ℝ, 0 < η ∧ η < 1 ∧
    ∀ X₀ : ℕ, ∃ X L : ℕ,
      max X₀ 1 ≤ X ∧
      h ≤ L - s ∧
      16 * (2 * X + h + L + 2) ≤ 2 ^ L ∧
      PivotBudgetAt h X L s η

/-- The zero-based dyadic coboundary `(2 - E)c`. -/
def dyadicCoboundary (c : ℕ → ℤ) (n : ℕ) : ℤ :=
  2 * c n - c (n + 1)

/-- The depth-`L` cleared binary prefix, accumulated from left to right. -/
def dyadicClearedPrefix (a : ℕ → ℤ) (n : ℕ) : ℕ → ℤ
  | 0 => 0
  | L + 1 => 2 * dyadicClearedPrefix a n L + a (n + L)

/-- Evaluation of a finite integer shift polynomial on a sequence. -/
def shiftLinearCombination : List (ℕ × ℤ) → (ℕ → ℤ) → (ℕ → ℤ)
  | [], _ => fun _ => 0
  | (h, q) :: terms, f => fun n =>
      q * f (n + h) + shiftLinearCombination terms f n

/-- The `ℓ1` weight of a finite shift polynomial. -/
def shiftLinearWeight : List (ℕ × ℤ) → ℤ
  | [] => 0
  | (_, q) :: terms => |q| + shiftLinearWeight terms

/-! ## Conditional local-window carry escape -/

def leastPositiveResidue (C : ℕ) (x : ℤ) : ℕ :=
  if x % (C : ℤ) = 0 then C else Int.natAbs (x % (C : ℤ))

def windowBase (b : ℕ → ℤ) (lo : ℕ) : ℕ → ℤ
  | 0 => 1
  | len + 1 => b (lo + len) * windowBase b lo len

def windowForcing (b e : ℕ → ℤ) (lo : ℕ) : ℕ → ℤ
  | 0 => 0
  | len + 1 => b (lo + len) * windowForcing b e lo len + e (lo + len)

def CofinalLocalWindowEscape
    (b m : ℕ → ℕ) (shortBound : ℕ → ℕ → ℕ) : Prop :=
  ∀ B : ℕ, 0 < B → Nat.Coprime B 30 →
    ∀ lo₀ : ℕ, ∃ lo len : ℕ,
      lo₀ ≤ lo ∧ 0 < len ∧
      0 < Int.natAbs (windowBase (fun n => b n) lo len) ∧
      shortBound B (lo + len) <
        leastPositiveResidue
          (Int.natAbs (windowBase (fun n => b n) lo len))
          (-((B : ℤ) *
            windowForcing (fun n => b n) (fun n => m n) lo len))

/-- One trusted challenge witness carries the twenty-five exact interfaces selected
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
  problem243BoundedRiseTailAvoidance :
    ∀ (u m : ℕ → ℕ) (N B : ℕ),
      0 < B →
      (∀ n, N ≤ n → 1 < m n) →
      (∀ {i j : ℕ}, N ≤ i → N ≤ j → i ≠ j →
        Nat.Coprime (m i) (m j)) →
      (∀ {i t : ℕ}, N ≤ i → i < t →
        Nat.Coprime (m i) (u t)) →
      (∀ n, N ≤ n → u (n + 1) ≤ u n + B) →
      Filter.Tendsto u Filter.atTop Filter.atTop →
      False
  problem243SylvesterNextEventualOfCenteredZero :
    ∀ (a D C : ℕ → ℤ),
      (∀ n, D (n + 1) = nextDenState (a n) (D n)) →
      (∀ n, C (n + 1) = nextTailState (a n) (D n) (C n)) →
      (∃ N, ∀ n, N ≤ n → centeredState (a n) (D n) (C n) = 0) →
      (∃ N, ∀ n, N ≤ n → C (n + 1) ≠ 0) →
      ∃ N, ∀ n, N ≤ n → a (n + 1) = sylvesterNext (a n)
  problem243CenteredStateEventuallyZero :
    ∀ (C E : ℕ → ℕ),
      (∀ n, C (n + 1) + E n = C n) →
      ∃ N, ∀ n, N ≤ n → E n = 0
  problem243BoundedNegativePartEventuallyZero :
    ∀ (a C D : ℕ → ℕ) (E : ℕ → ℤ) (B : ℕ),
      (∀ n, 1 < a n) →
      (∀ n, 0 < C n) →
      (∀ n, C (n + 1) + D n = a n * C n) →
      (∀ n, D (n + 1) = a n * D n) →
      (∀ n, E n = centeredState (a n : ℤ) (D n : ℤ) (C n : ℤ)) →
      (∀ n, Int.natAbs (E n) < C n) →
      (∀ n, -(B : ℤ) ≤ E n) →
      (∀ K, ∃ N, ∀ n, N ≤ n →
        K * Int.natAbs (E n) < C n) →
      ∃ N, ∀ n, N ≤ n → E n = 0
  problem243SummableNegativeMass :
    ∀ (a D : ℕ → ℤ) (C : ℕ → ℕ),
      (∀ n, D (n + 1) = nextDenState (a n) (D n)) →
      (∀ n, C (n + 1) = nextTailState (a n) (D n) (C n)) →
      (∀ n, 0 < C n) →
      (∀ n, (C (n + 1) : ℤ) =
        (C n : ℤ) - centeredState (a n) (D n) (C n)) →
      (∀ K, ∃ N, ∀ n, N ≤ n →
        K * Int.natAbs (centeredState (a n) (D n) (C n)) < C n) →
      (Summable
        (negativeRelativeMass C
          (fun n ↦ centeredState (a n) (D n) (C n)))) →
      ∃ N, ∀ n, N ≤ n →
        a (n + 1) = sylvesterNext (a n)
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
  problem249AllBaseRank :
    ∀ (k e : ℕ), 2 ≤ k → 1 ≤ e →
      LinearIndependent ℚ (canonicalAllBaseTotientKernelFamily k e) →
      finrank ℚ
        (Submodule.span ℚ
          (Set.range (allBaseTotientKernelThroughLevelFamily k e))) =
        k ^ e + 1
  problem249CarryAntiCompression :
    (¬ Irrational (binaryCoeffSeries Nat.totient)) →
      ∃ v : ℕ, 0 < v ∧ ∃ u : ℕ → ℤ,
        IsTemperedBinaryOrbit Nat.totient v u ∧
          (∀ e : ℕ,
            2 ^ e - 1 ≤
              Module.finrank ℚ
                (Submodule.span ℚ
                  (Set.range (canonicalCarryKernelFamily u e)))) ∧
          ∃ h : ℕ, 0 < h ∧ ∃ N₀ : ℕ,
            CarrySectionsEventuallyPeriodicMod v h N₀ u
  problem249FixedPrecisionTropicalNoGo :
    ∀ (u : ℕ) (hu : 0 < u)
      (symbols : List VUSymbol) (hodd : ∀ σ ∈ symbols, Odd σ.unit) (e : ℤ),
      ∃ states : List ℤ,
        VUOrbit u e symbols states ∧
        List.Forall₂ (fun σ e' => |e'| ≤ vuRadius u σ) symbols states
  problem249CleanBinaryCyclotomicAnchor :
    ∀ (h N₀ : ℕ), 0 < h →
      ∃ q p : ℕ,
        q.Prime ∧
        p.Prime ∧
        Nat.Coprime p (h * q) ∧
        p ∣ binaryCyclotomicLayer (h * q) ∧
        h * q ∣ p - 1 ∧
        N₀ ≤ p - 1
  problem269WeightedCarry :
    ∀ (B : ℤ) (hB : 0 < B)
      (base carry digit : ℕ → ℤ),
      (∀ n, carry (n + 1) = base n * carry n - B * digit n) →
      let residue := fun n => weightedCarryResidue B (carry n)
      let quotient := fun n => weightedCarryQuotient B (carry n)
      ∀ n,
        digit n =
          weightedResidueDigit B (base n)
              (residue n) (residue (n + 1)) +
            base n * quotient n - quotient (n + 1)
  problem269ConditionalCarryEscape :
    ∀ (b m : ℕ → ℕ) (shortBound : ℕ → ℕ → ℕ),
      CofinalLocalWindowEscape b m shortBound →
      (B : ℕ) → 0 < B → Nat.Coprime B 30 →
      (d : ℕ → ℤ) →
      (∀ n, d (n + 1) = (b n : ℤ) * d n - (B : ℤ) * (m n : ℤ)) →
      (∀ n, 0 < d n) →
      (∀ n, Int.natAbs (d n) ≤ shortBound B n) →
      False
  problem249VisibleCoprimeMass :
    (∑' p : ℕ × ℕ, if 0 < p.1 ∧ 0 < p.2 ∧ Nat.Coprime p.1 p.2
        then 1 / ((2 : ℝ) ^ (p.1 + p.2) - 1) else 0) = 1
  problem249SquaredGcdMoment :
    (∑' d : ℕ+, (Nat.totient (d : ℕ) : ℝ) / ((2 : ℝ) ^ (d : ℕ) - 1) ^ 2
      = ∑' n : ℕ+,
          ((∑ e ∈ (n : ℕ).divisors, (Nat.totient e : ℝ) * (((n : ℕ) / e : ℕ) : ℝ))
            - ((n : ℕ) : ℝ)) * ((1 : ℝ) / 2) ^ (n : ℕ))
  problem249SternBrocotRunStability :
    ∀ e : List ℕ,
      Nat.fib (e.length + 3) + Nat.fib (e.length + 1) * e.sum ≤
        runHeight (defectRunLengths e)
  problem249CylinderMassSplit :
    ∀ a b : ℕ+,
      cylinderMass a b =
        1 / ((2 : ℝ) ^ ((a : ℕ) + (b : ℕ)) - 1)
          + cylinderMass (a + b) b + cylinderMass a (a + b)
  problem249LcmFactorIdealShiftAlgebra :
    ∀ (t : ℕ), 3 ≤ t →
      ∃ c a : ℕ → ℤ,
        (∃ k, c k ≠ 0) ∧
        (∀ i, a i = dyadicCoboundary c i) ∧
        ∀ terms : List (ℕ × ℤ),
          ∃ d b : ℕ → ℤ,
            (∀ i, d i = shiftLinearCombination terms c i) ∧
            (∀ i, b i = shiftLinearCombination terms a i) ∧
            (∀ i, b i = dyadicCoboundary d i) ∧
            (∀ n L, dyadicClearedPrefix b n L =
              (2 : ℤ) ^ L * d n - d (n + L)) ∧
            (∀ i, (Nat.totient (periodLcm t) : ℤ) ∣ b i) ∧
            (∀ j, j ∣ periodLcm t → ∀ i, (Nat.totient j : ℤ) ∣ b i) ∧
            (∀ i, |d i| ≤ shiftLinearWeight terms *
              |(Nat.totient (periodLcm t) : ℤ)|) ∧
            ∀ i, |b i| ≤ shiftLinearWeight terms *
              (2 * |(Nat.totient (periodLcm t) : ℤ)|)
  problem249ActualLcmOrbit :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) ↔
      PowerTwoActualLcmOrbitNonintegralitySupply
  problem249ActualLcmOrbit_of_supply :
    PowerTwoActualLcmOrbitNonintegralitySupply →
      Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n)
  problem249ActualLcmOrbitSeparation :
    PowerTwoActualLcmOrbitSeparationSupply →
      Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n)
  problem249FirstHarmonicPivotFiber :
    ∀ {X L s m : ℕ}, 0 < m → m ≤ Nat.sqrt X / 2 →
      (pivotSupplierPrimes X L s m).image (pivotBaseOfPrime L s m) =
        pivotFiber X L s m
  problem249FirstHarmonicPivotIsolationCounterexample :
    pivotOffset 20 1 = 20 ∧
      18 ∈ pivotFiber 16 20 1 2 ∧
      pivotPrime 18 20 1 = 19 ∧
      19 ∣ pivotArgument 18 20 1 ∧
      19 ∣ 18 + 1
  problem249FirstHarmonicPivotDecomposition :
    ∀ (h X L s : ℕ) (η : ℝ),
      (∑ N ∈ Finset.Ico X (2 * X), windowFirstExp h N L) =
        pivotCenteredCorrelation h X L s η +
        pivotFiberMeanContribution h X L s η +
        pivotBadContribution h X L s η +
        pivotNonSupplierContribution h X L s
  problem249FirstHarmonicPivotBudget :
    ∀ {h X L s : ℕ} {η : ℝ}, PivotBudgetAt h X L s η →
      (∑ N ∈ Finset.Ico X (2 * X), windowFirstCos h N L) ≤
        (9 / 10 : ℝ) * X
  problem249FirstHarmonicPivotResidualDecorrelation :
    DTWPivotResidualDecorrelation →
      Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n)
  problem249ActualLcmPositiveCorridor :
    ∀ {a J : ℕ}, 8 ≤ a → J + (a + 6) < 2 * 2 ^ a →
      0 <
        totientTail (2 * periodLcm (2 ^ a) + J) -
          totientTail (periodLcm (2 ^ a) + J)
  problem249ActualLcmTrueEndpointSurvivor :
    ∀ {a J K : ℕ}, 8 ≤ a → J + K + (a + 6) < 2 * 2 ^ a →
      ∀ {d : ℤ},
        (d : ℝ) =
          totientTail (2 * periodLcm (2 ^ a) + J) -
            totientTail (periodLcm (2 ^ a) + J) →
        -carryOrbit (periodLcm (2 ^ a)) (periodLcm (2 ^ a) + J) d K < 0 ∧
        endpointSurvivor (periodLcm (2 ^ a))
          (periodLcm (2 ^ a) + J) K
          (-carryOrbit (periodLcm (2 ^ a))
            (periodLcm (2 ^ a) + J) d K)
  problem249ActualLcmTopEdgeResidue :
    ∀ {a J K : ℕ}, 8 ≤ a → J + K + (a + 6) < 2 * 2 ^ a →
      ∀ {d : ℤ},
        (d : ℝ) =
          totientTail (2 * periodLcm (2 ^ a) + J) -
            totientTail (periodLcm (2 ^ a) + J) →
        ((2 * periodLcm (2 ^ a) + J + K + 2 : ℕ) : ℤ) <
            (2 : ℤ) ^ K →
        let H := periodLcm (2 ^ a)
        let e := carryOrbit H (H + J) d K
        let P := (2 : ℤ) ^ K
        let B := ((2 * H + J + K + 2 : ℕ) : ℤ)
        windowDiscrepancy H (H + J) K % P = P - e ∧
          P - B < windowDiscrepancy H (H + J) K % P ∧
          windowDiscrepancy H (H + J) K % P < P
  problem249ActualForeignResidueProjection :
    (∀ {H D L : ℕ}, 2 * H ≤ D →
      |foreignTailWindow H D L| ≤ foreignComplementBound H D) ∧
    (∀ H D : ℕ,
      finiteResidueDiagonal H D =
        projectedForeignDefect H D + projectedDivisorChannels H D) ∧
    (∀ {H D : ℕ}, ControlledForeignProjection H D →
      ProjectedFullTargetSeparation H D → ¬ScaleFullTargetHit H)
  problem251 : ∀ M : ℕ, ∃ n, M < primeGap0 n
  problem251CoefficientOnlyNoGo : CoefficientOnlyNoGo
  problem251CofinalSmallMismatch :
    ∀ {T : ℕ → ℚ} (h : ℕ),
      DyadicTailRecurrence (fun n => (primeGap0 n : ℤ)) T →
      (∀ N₀, ∃ N, N₀ ≤ N ∧
        ((-1 < tailShift T h N ∧ tailShift T h N < 1) ∧
         (-1 < tailShift T h (N + 1) ∧ tailShift T h (N + 1) < 1)) ∧
        primeGap0 (N + h + 1) ≠ primeGap0 (N + 1)) →
      ¬ ∃ N₀, ∀ N, N₀ ≤ N → RatIntegral (tailShift T h N)
  problem251Equivalence :
    Summable primeDyadicTerm →
      (Irrational (∑' n : ℕ, primeDyadicTerm n) ↔
        Irrational (∑' n : ℕ, primeGapDyadicTerm n))
  problem251TailShiftDenominator :
    ∀ {g : ℕ → ℤ} {T : ℕ → ℚ},
      DyadicTailRecurrence g T → ∀ N h,
        RatIntegral (tailShift T h N) ↔ (T N).den ∣ 2 ^ h - 1
  problem251TailShiftCongruence :
    ∀ {g : ℕ → ℤ} {T : ℕ → ℚ},
      DyadicTailRecurrence g T → ∀ N h,
        RatIntegral (tailShift T h N) ↔
          2 ^ h ≡ 1 [MOD (T N).den]
  problem251TailShiftEventualIntegrality :
    ∀ {g : ℕ → ℤ} {T : ℕ → ℝ},
      RealDyadicTailRecurrence g T →
        (¬ Irrational (T 0) ↔
          ∃ h N : ℕ, 0 < h ∧
            ∀ k, RealIntegral (realTailShift T h (N + k)))
  problem251TailShiftIrrationalityNormalForm :
    ∀ {g : ℕ → ℤ} {T : ℕ → ℝ},
      RealDyadicTailRecurrence g T →
        (Irrational (T 0) ↔
          ∀ h : ℕ, 0 < h → ∀ N : ℕ,
            ¬ RealIntegral (realTailShift T h N))
  problem257Measure : volume mersenneAchievementSet = 1
  problem257FullSupport :
    ∀ b : ℕ, 2 ≤ b →
      Irrational (∑' k : ℕ, (1 : ℝ) / ((b : ℝ) ^ (k + 1) - 1))
  problem257PairwiseCoprime :
    ∀ (b : ℕ) (A : Set ℕ),
      2 ≤ b →
      A.Infinite →
      A.Pairwise Nat.Coprime →
      Summable (Set.indicator A fun a : ℕ => (1 : ℝ) / a) →
      Irrational (erdosSupportSeries b A)
  problem257RatWeightEventuallyPeriodic :
    ∀ (b m N₀ : ℕ) (γ : ℕ → ℚ),
      2 ≤ b →
      0 < m →
      (∀ n : ℕ, 0 ≤ γ n) →
      (∀ n : ℕ, N₀ ≤ n → γ (n + m) = γ n) →
      (∃ a : ℕ, N₀ ≤ a ∧ 0 < a ∧ 0 < γ a) →
      Irrational (∑' a : ℕ, ((γ a : ℝ)) / ((b : ℝ) ^ a - 1))
  problem257OrthogonalPetalSunflower :
    ∀ {A : Set ℕ},
      OrthogonalPetalBouquet A →
      SunflowerForcedSlotTailSelection A →
      Irrational (erdosSupportSeries 2 A)
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
  problem257ShiftedOddTailNatStates :
    ∀ (A : Set ℕ),
      (∃ a : ℕ, 0 < a ∧ a ∈ A) →
      ∀ (p : ℤ) (c v : ℕ),
        0 < v →
        erdosSupportSeries 2 A =
          (p : ℝ) / ((2 ^ c * v : ℕ) : ℝ) →
        ∃ u : ℕ → ℕ,
          (∀ n : ℕ, (u n : ℝ) =
            (v : ℝ) * binaryCoeffTail (supportCoeff A) (c + n)) ∧
          (∀ n : ℕ, 0 < u n) ∧
          (∀ n : ℕ, u (n + 1) +
            v * supportCoeff A (c + n + 1) = 2 * u n) ∧
          (∀ n : ℕ, u n ≡ p.toNat * 2 ^ n [MOD v])
  problem257BooleanMobiusCarry :
    ∀ (p : ℤ) (q : ℕ),
      0 < q →
      ((∃ A : Set ℕ, 0 ∉ A ∧ (∃ a : ℕ, 0 < a ∧ a ∈ A) ∧
          erdosSupportSeries 2 A = (p : ℝ) / (q : ℝ)) ↔
        ∃ U : ℕ → ℤ, BooleanMobiusCarryCertificate p q U)
  problem257BooleanMobiusExactRowDynamics :
    CofinalPositiveHalfGreedySkips →
      (1 / 2 : ℝ) ∈ mersenneAchievementSet
  problem257HalfMembershipSeamClassification :
    (1 / 2 : ℝ) ∈ mersenneAchievementSet ↔
      SeamGreedyUnboundedTerminalFalse
  problem257CompositeDilationDefect :
    ∀ (A : Set ℕ) {a x : ℕ},
      a ∈ A →
      0 < a →
      0 < x →
      supportCoeff A (a * x) =
        supportCoeff A x + (if a ∣ x then 0 else 1) +
          compositeDilationDefect A a x
  problem257HalfTwoAdicBand :
    ∀ {p D q : ℤ},
      0 < p →
      0 < D →
      0 < q →
      Odd p →
      Odd D →
      Odd q →
      IntBand p D q →
      7 ≤ p
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
  problem269HeightGrouping :
    ∀ (p q r hp hq hr : ℕ),
      (∑ e ∈ smoothExponentBox hp hq hr,
        threePrimeKernelQ p q r e.1 e.2.1 e.2.2) =
        ∑ H ∈ (smoothExponentBox hp hq hr).image (smoothPointHeight p q r),
          (smoothHeightFiber p q r hp hq hr H).card • ((H : ℚ)⁻¹)
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
  problem1049RectangularHpGapNonpos :
    ∀ (rho sigma : ℝ), 0 ≤ rho → 1 + rho ≤ sigma →
      hpClearedGap rho sigma ≤ 0
  problem1049RectangularHpGapEqZeroIff :
    ∀ (rho sigma : ℝ), 0 ≤ rho → 1 + rho ≤ sigma →
      (hpClearedGap rho sigma = 0 ↔ rho = 0 ∧ sigma = 1)
  problem1049RectangularHpThresholdLeClassical :
    ∀ (rho sigma : ℝ), 0 ≤ rho → 1 + rho ≤ sigma →
      hpThreshold rho sigma ≤ 1 / 2 - 1 / Real.pi ^ 2
  problem1049RectangularHpThresholdEqClassicalIff :
    ∀ (rho sigma : ℝ), 0 ≤ rho → 1 + rho ≤ sigma →
      (hpThreshold rho sigma = 1 / 2 - 1 / Real.pi ^ 2 ↔
        rho = 0 ∧ sigma = 1)
  problem249TailOrbitBlockGapOfNonpositiveDensity :
    TotientTailOrbitNonpositiveBlockDensity →
      TotientTailOrbitBlockGap
  problem249IrrationalOfTailOrbitBlockGap :
    TotientTailOrbitBlockGap →
      Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n)
  problem249IrrationalOfNaturalPrimeTailOrbitStrictGap :
    DTWNaturalPrimeTailOrbitStrictGap →
      Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n)

end Erdos249257.ExternalVerification
