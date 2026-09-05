/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib

/-!
# Trusted challenge for the three-prime structure in Erdős #269

The package exposes the exact running-LCM coordinate for every finite prefix
of a three-prime smooth semigroup and the full rank phase transition: for every
order there is a nonsingular kernel minor, uniformly in the remaining layer,
and consequently no finite separable representation exists.  The explicit
`{2,3,5}` determinant `-1/15` is retained as the smallest concrete witness.

Neither theorem proves irrationality or transcendence of the three-prime
series in Erdős #269.
-/

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

/-- The literal LCM of the smooth prefix is exactly the product of the three
maximal pure prime powers. -/
theorem smoothPrefixLcm_eq_threePrimeHeight
    {p q r x : ℕ} (hp : p.Prime) (hq : q.Prime) (hr : r.Prime)
    (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r) (hx : x ≠ 0) :
    smoothPrefixLcm p q r x = threePrimeHeight p q r x := by
  sorry

/-- The rational three-prime kernel is exactly constant on every logarithmic
cell of the smooth lattice. -/
theorem threePrimeKernelQ_eq_of_sameLogCell
    {p q r i j k i' j' k' : ℕ}
    (hcell : SameThreePrimeLogCell p q r
      (smooth3Val p q r i j k) (smooth3Val p q r i' j' k')) :
    threePrimeKernelQ p q r i j k =
      threePrimeKernelQ p q r i' j' k' := by
  sorry

/-- The first `count` positive jump values in each of three pairwise-distinct
prime channels form an exact `3 * count`-element set. -/
theorem threePrimePositiveJumpSet_card
    {p q r count : ℕ} (hp : p.Prime) (hq : q.Prime) (hr : r.Prime)
    (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r) :
    (threePrimePositiveJumpSet p q r count).card = 3 * count := by
  sorry

/-- Every finite three-prime kernel box groups exactly by its genuine
running-LCM height, with the fibre cardinalities as coefficients. -/
theorem finiteSmoothKernelSum_groupedByHeight
    (p q r hp hq hr : ℕ) :
    (∑ e ∈ smoothExponentBox hp hq hr,
      threePrimeKernelQ p q r e.1 e.2.1 e.2.2) =
      ∑ H ∈ (smoothExponentBox hp hq hr).image (smoothPointHeight p q r),
        (smoothHeightFiber p q r hp hq hr H).card • ((H : ℚ)⁻¹) := by
  sorry

/-- A multiplicative-width shell has the exact denominator-free quadratic
multiplicity bound used by the scaled-tail analysis. -/
theorem smoothExponentShell_card_quadratic
    {p q r lo hi hp hq hr j : ℕ}
    (hrPos : 0 < r) (hwidth : hi ≤ r * lo)
    (hpq : hp ≤ hq) (hqr : hq ≤ hr)
    (hsum : hp + hq + hr = j) :
    9 * (smoothExponentShell p q r lo hi hp hq hr).card ≤
      (j + 3) ^ 2 := by
  sorry

/-- The smallest `{2,3,5}` kernel rectangle has determinant `-1/15`, hence
rank two over the rationals. -/
theorem kernel_235_minor_eq_neg_one_fifteen :
    threePrimeKernelQ 2 3 5 0 0 0 *
          threePrimeKernelQ 2 3 5 1 1 0 -
        threePrimeKernelQ 2 3 5 1 0 0 *
          threePrimeKernelQ 2 3 5 0 1 0 =
      -(1 / 15 : ℚ) := by
  sorry

/-- Three distinct prime generators force nonsingular minors of every order,
simultaneously in every third-coordinate layer, and hence rule out every
finite decomposition `∑ l, f l i * G l j k`. -/
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
  sorry

end Erdos249257.ExternalVerification269ThreePrimeStructure
