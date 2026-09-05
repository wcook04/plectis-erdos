/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib
import ErdosProblems.Erdos269.KernelCarryRank
import ErdosProblems.Erdos269.ThreePrimeRunningLcm

namespace Erdos249257.ExternalVerification269ThreePrimeStructure

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

def SameThreePrimeLogCell (p q r x y : ℕ) : Prop :=
  Nat.log p x = Nat.log p y ∧
    Nat.log q x = Nat.log q y ∧
      Nat.log r x = Nat.log r y

def positivePrimePowers (p count : ℕ) : Finset ℕ :=
  (Finset.range count).image fun e => p ^ (e + 1)

def threePrimePositiveJumpSet (p q r count : ℕ) : Finset ℕ :=
  (positivePrimePowers p count ∪ positivePrimePowers q count) ∪
    positivePrimePowers r count

def smoothExponentBox (hp hq hr : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  (Finset.range (hp + 1)).product
    ((Finset.range (hq + 1)).product (Finset.range (hr + 1)))

def smoothPointHeight (p q r : ℕ) (e : ℕ × ℕ × ℕ) : ℕ :=
  threePrimeHeight p q r (smooth3Val p q r e.1 e.2.1 e.2.2)

def smoothHeightFiber
    (p q r hp hq hr H : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  (smoothExponentBox hp hq hr).filter fun e => smoothPointHeight p q r e = H

def smoothExponentShell
    (p q r lo hi hp hq hr : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  ((Finset.range (hp + 1)).product
      ((Finset.range (hq + 1)).product (Finset.range (hr + 1)))).filter
    fun e => lo ≤ smooth3Val p q r e.1 e.2.1 e.2.2 ∧
      smooth3Val p q r e.1 e.2.1 e.2.2 < hi

theorem smoothPrefixLcm_eq_threePrimeHeight
    {p q r x : ℕ} (hp : p.Prime) (hq : q.Prime) (hr : r.Prime)
    (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r) (hx : x ≠ 0) :
    smoothPrefixLcm p q r x = threePrimeHeight p q r x := by
  simpa [smoothPrefixLcm, smoothPrefixExponents, smooth3Val,
    threePrimeHeight, ErdosProblems.Erdos269.smoothPrefixLcm,
    ErdosProblems.Erdos269.smoothPrefixExponents,
    ErdosProblems.Erdos269.smooth3Val,
    ErdosProblems.Erdos269.threePrimeHeight] using
    ErdosProblems.Erdos269.smoothPrefixLcm_eq_threePrimeHeight
      hp hq hr hpq hpr hqr hx

theorem threePrimeKernelQ_eq_of_sameLogCell
    {p q r i j k i' j' k' : ℕ}
    (hcell : SameThreePrimeLogCell p q r
      (smooth3Val p q r i j k) (smooth3Val p q r i' j' k')) :
    threePrimeKernelQ p q r i j k =
      threePrimeKernelQ p q r i' j' k' := by
  have hcell' : ErdosProblems.Erdos269.SameThreePrimeLogCell p q r
      (ErdosProblems.Erdos269.smooth3Val p q r i j k)
      (ErdosProblems.Erdos269.smooth3Val p q r i' j' k') := by
    simpa [SameThreePrimeLogCell, smooth3Val,
      ErdosProblems.Erdos269.SameThreePrimeLogCell,
      ErdosProblems.Erdos269.smooth3Val] using hcell
  simpa [SameThreePrimeLogCell, smooth3Val, threePrimeHeight,
    threePrimeKernelQ, ErdosProblems.Erdos269.SameThreePrimeLogCell,
    ErdosProblems.Erdos269.smooth3Val,
    ErdosProblems.Erdos269.threePrimeHeight,
    ErdosProblems.Erdos269.threePrimeKernelQ] using
    ErdosProblems.Erdos269.threePrimeKernelQ_eq_of_sameLogCell hcell'

theorem threePrimePositiveJumpSet_card
    {p q r count : ℕ} (hp : p.Prime) (hq : q.Prime) (hr : r.Prime)
    (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r) :
    (threePrimePositiveJumpSet p q r count).card = 3 * count := by
  simpa [threePrimePositiveJumpSet, positivePrimePowers,
    ErdosProblems.Erdos269.threePrimePositiveJumpSet,
    ErdosProblems.Erdos269.positivePrimePowers] using
    ErdosProblems.Erdos269.threePrimePositiveJumpSet_card
      hp hq hr hpq hpr hqr

theorem finiteSmoothKernelSum_groupedByHeight
    (p q r hp hq hr : ℕ) :
    (∑ e ∈ smoothExponentBox hp hq hr,
      threePrimeKernelQ p q r e.1 e.2.1 e.2.2) =
      ∑ H ∈ (smoothExponentBox hp hq hr).image (smoothPointHeight p q r),
        (smoothHeightFiber p q r hp hq hr H).card • ((H : ℚ)⁻¹) := by
  simpa [smoothExponentBox, smoothPointHeight, smoothHeightFiber,
    smooth3Val, threePrimeHeight, threePrimeKernelQ,
    ErdosProblems.Erdos269.smoothExponentBox,
    ErdosProblems.Erdos269.smoothPointHeight,
    ErdosProblems.Erdos269.smoothHeightFiber,
    ErdosProblems.Erdos269.smooth3Val,
    ErdosProblems.Erdos269.threePrimeHeight,
    ErdosProblems.Erdos269.threePrimeKernelQ] using
    ErdosProblems.Erdos269.finiteSmoothKernelSum_groupedByHeight
      p q r hp hq hr

theorem smoothExponentShell_card_quadratic
    {p q r lo hi hp hq hr j : ℕ}
    (hrPos : 0 < r) (hwidth : hi ≤ r * lo)
    (hpq : hp ≤ hq) (hqr : hq ≤ hr)
    (hsum : hp + hq + hr = j) :
    9 * (smoothExponentShell p q r lo hi hp hq hr).card ≤
      (j + 3) ^ 2 := by
  simpa [smoothExponentShell, smooth3Val,
    ErdosProblems.Erdos269.smoothExponentShell,
    ErdosProblems.Erdos269.smooth3Val] using
    ErdosProblems.Erdos269.smoothExponentShell_card_quadratic
      hrPos hwidth hpq hqr hsum

theorem kernel_235_minor_eq_neg_one_fifteen :
    threePrimeKernelQ 2 3 5 0 0 0 *
          threePrimeKernelQ 2 3 5 1 1 0 -
        threePrimeKernelQ 2 3 5 1 0 0 *
          threePrimeKernelQ 2 3 5 0 1 0 =
      -(1 / 15 : ℚ) := by
  simpa [threePrimeKernelQ, threePrimeHeight, smooth3Val,
    ErdosProblems.Erdos269.threePrimeKernelQ,
    ErdosProblems.Erdos269.threePrimeHeight,
    ErdosProblems.Erdos269.smooth3Val] using
    ErdosProblems.Erdos269.kernel_235_minor_eq_neg_one_fifteen

theorem threePrimeKernel_infiniteRank_and_noFiniteSeparation
    {p q r : ℕ} (hp : p.Prime) (hq : q.Prime) (hr : r.Prime)
    (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r) :
    (∀ n : ℕ,
      ∃ I J : Fin n → ℕ,
        Function.Injective I ∧ Function.Injective J ∧
          ∀ k : ℕ,
            (Matrix.det fun a b : Fin n =>
              threePrimeKernelQ p q r (I a) (J b) k) ≠ 0) ∧
      (∀ d : ℕ,
        ¬ ∃ (f : Fin d → ℕ → ℚ) (G : Fin d → ℕ → ℕ → ℚ),
            ∀ i j k,
              threePrimeKernelQ p q r i j k =
                ∑ l : Fin d, f l i * G l j k) := by
  constructor
  · intro n
    simpa [threePrimeKernelQ, threePrimeHeight, smooth3Val,
      ErdosProblems.Erdos269.threePrimeKernelQ,
      ErdosProblems.Erdos269.threePrimeHeight,
      ErdosProblems.Erdos269.smooth3Val] using
      ErdosProblems.Erdos269.exists_uniform_nonsingular_threePrimeKernel_minor_of_prime
        hp hq hr hpr hqr n
  · intro d
    simpa [threePrimeKernelQ, threePrimeHeight, smooth3Val,
      ErdosProblems.Erdos269.threePrimeKernelQ,
      ErdosProblems.Erdos269.threePrimeHeight,
      ErdosProblems.Erdos269.smooth3Val] using
      ErdosProblems.Erdos269.not_finite_separable_threePrimeKernel
        hp hq hr hpr hqr d

end Erdos249257.ExternalVerification269ThreePrimeStructure
