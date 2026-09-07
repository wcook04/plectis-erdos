/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib

/-!
# Trusted challenge for the Erdős #68 moving-factor scale split

This source-independent package exposes three distinct endpoints of one
private-factor mechanism.  First, one prefix-private prime in a tailored
factorial block is enough for a two-coordinate scale certificate implying
irrationality.  Second, arbitrary factors of one moving private modulus give
a strictly more flexible normalized-collision certificate.  Third, every
fixed pair of denominator owners is eventually absorbed by the growing
factorial base.

The two irrationality theorems are conditional: no theorem here supplies the
required cofinal scale or projection-disagreement certificates.  Thus the
package does not solve Erdős #68.
-/

namespace Erdos249257.ExternalVerification68MovingFactorScaleSplit

open scoped BigOperators

noncomputable section

/-- The literal factorial-gap series from Erdős #68. -/
noncomputable def factorialGapSeries : ℝ :=
  ∑' d : ℕ, if 1 < d then
    (1 : ℝ) / ((((d.factorial : ℤ) - 1 : ℤ) : ℝ))
  else 0

/-- The canonical large prefix-private primes of `m! - 1`. -/
def factorialGapLargePrefixPrivatePrimes (m : ℕ) : Finset ℕ :=
  (m.factorial - 1).primeFactors.filter fun q =>
    m + 1 < q ∧
      ∀ k ∈ Finset.Ico 2 m,
        Nat.Coprime q (k.factorial - 1)

def factorialBlockIndices (p : ℕ) : Finset ℕ :=
  Finset.Icc 2 (2 * p - 1)

def factorialGapDenominator (n : ℕ) : ℕ :=
  n.factorial - 1

def factorialBlockBase (p : ℕ) : ℕ :=
  (p - 1).factorial

def pairwiseCollisionCore
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (d : ι → ℕ) : ℕ :=
  s.lcm fun i =>
    (s.erase i).lcm fun j => Nat.gcd (d i) (d j)

def collisionCore
    {ι : Type*} [DecidableEq ι]
    (base : ℕ) (s : Finset ι) (d : ι → ℕ) : ℕ :=
  Nat.lcm base (pairwiseCollisionCore s d)

def endpointDenominatorLcm
    {ι : Type*} [DecidableEq ι]
    (base : ℕ) (s : Finset ι) (d : ι → ℕ) : ℕ :=
  Nat.lcm base (s.lcm d)

def endpointTailNumerator
    {ι : Type*} [DecidableEq ι]
    (base : ℕ) (s : Finset ι) (d : ι → ℕ) : ℕ :=
  s.sum fun i => endpointDenominatorLcm base s d / d i

def privateQuotient
    {ι : Type*} [DecidableEq ι]
    (base : ℕ) (s : Finset ι) (d : ι → ℕ) (i : ι) : ℕ :=
  d i / Nat.gcd (d i) (collisionCore base s d)

def privateModulus
    {ι : Type*} [DecidableEq ι]
    (base : ℕ) (s : Finset ι) (d : ι → ℕ) : ℕ :=
  s.prod (privateQuotient base s d)

def projectedResidue (T Q : ℕ) : ℕ :=
  T % Q

def complementaryProjectedResidue (T Q : ℕ) : ℕ :=
  projectedResidue (Q - projectedResidue T Q) Q

def leaveOneOutModulus (R r : ℕ) : ℕ :=
  R / r

def factorialBlockEndpointLcm (p : ℕ) : ℕ :=
  endpointDenominatorLcm
    (factorialBlockBase p)
    (factorialBlockIndices p)
    factorialGapDenominator

def factorialBlockCollisionCore (p : ℕ) : ℕ :=
  collisionCore
    (factorialBlockBase p)
    (factorialBlockIndices p)
    factorialGapDenominator

def factorialBlockNormalizedCollisionCore (p : ℕ) : ℕ :=
  factorialBlockCollisionCore p / factorialBlockBase p

def factorialBlockUpperDescFactorial (p : ℕ) : ℕ :=
  (2 * p - 1).descFactorial p

def factorialBlockPrivateModulus (p : ℕ) : ℕ :=
  privateModulus
    (factorialBlockBase p)
    (factorialBlockIndices p)
    factorialGapDenominator

def factorialBlockTailNumerator (p : ℕ) : ℕ :=
  endpointTailNumerator
    (factorialBlockBase p)
    (factorialBlockIndices p)
    factorialGapDenominator

def factorialBlockPrivateQuotient (p n : ℕ) : ℕ :=
  privateQuotient
    (factorialBlockBase p)
    (factorialBlockIndices p)
    factorialGapDenominator n

def factorialBlockFactorProjectionModulus (p a : ℕ) : ℕ :=
  leaveOneOutModulus (factorialBlockPrivateModulus p) a

def factorialBlockScale (p : ℕ) : ℕ :=
  2 * p ^ 2 * (2 * p - 1).factorial

def factorialBlockBudget (p : ℕ) : ℕ :=
  2 * p + 1

/-- One moving prefix-private prime, together with the exact global and local
scale bounds, is enough to prove irrationality. -/
theorem movingPrivateFactorScaleSplit_implies_irrational
    (hcert :
      ∀ B : ℕ, ∃ m q : ℕ,
        4 ≤ m ∧
        B < m / 2 + 1 ∧
        q ∈ factorialGapLargePrefixPrivatePrimes m ∧
        factorialBlockBudget (m / 2 + 1) *
              factorialBlockEndpointLcm (m / 2 + 1) <
          factorialBlockScale (m / 2 + 1) *
            complementaryProjectedResidue
              (factorialBlockTailNumerator (m / 2 + 1))
              (factorialBlockPrivateModulus (m / 2 + 1)) ∧
        factorialBlockBudget (m / 2 + 1) *
              factorialBlockCollisionCore (m / 2 + 1) * q <
          factorialBlockScale (m / 2 + 1)) :
    Irrational factorialGapSeries := by
  sorry

/-- Arbitrary factors of one moving private modulus give a normalized
collision certificate implying irrationality.  The factors need not arise
from two distinct denominator owners. -/
theorem splitFactorNormalizedCollision_implies_irrational
    (hcert :
      ∀ B : ℕ, ∃ p a b : ℕ,
        p.Prime ∧
        B < p ∧
        a ∣ factorialBlockPrivateModulus p ∧
        b ∣ factorialBlockPrivateModulus p ∧
        1 < factorialBlockPrivateModulus p ∧
        complementaryProjectedResidue
            (factorialBlockTailNumerator p)
            (factorialBlockFactorProjectionModulus p a) ≠
          complementaryProjectedResidue
            (factorialBlockTailNumerator p)
            (factorialBlockFactorProjectionModulus p b) ∧
        factorialBlockBudget p *
              factorialBlockNormalizedCollisionCore p * max a b <
          2 * p ^ 2 * factorialBlockUpperDescFactorial p) :
    Irrational factorialGapSeries := by
  sorry

/-- Every fixed pair of factorial-gap owners is eventually absorbed: after
the block parameter passes both source denominators, both private quotients
are exactly one. -/
theorem fixedOwnerPair_eventually_absorbed
    {p i j : ℕ}
    (hi : 2 ≤ i)
    (hj : 2 ≤ j)
    (hlt :
      max (factorialGapDenominator i)
          (factorialGapDenominator j) < p) :
    factorialBlockPrivateQuotient p i = 1 ∧
      factorialBlockPrivateQuotient p j = 1 := by
  sorry

end

end Erdos249257.ExternalVerification68MovingFactorScaleSplit
