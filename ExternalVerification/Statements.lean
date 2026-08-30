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
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.NumberTheory.Real.Irrational

/-!
# External-verification statement vocabulary

This module contains only the definitions needed to state the twenty-nine-interface
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
  problem251 : ∀ M : ℕ, ∃ n, M < primeGap0 n
  problem251Equivalence :
    Summable primeDyadicTerm →
      (Irrational (∑' n : ℕ, primeDyadicTerm n) ↔
        Irrational (∑' n : ℕ, primeGapDyadicTerm n))
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
