/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib

/-!
# Trusted challenge for the carry mechanism in Erdős #269

This supporting package exposes the full checked conditional carry-extinction
family: the exact weighted block defect, global perturbation extinction from
two channel anchors, exponential lift-error growth, and the sharp four-state
first-block obstruction.  It also retains the exact residue-digit/coboundary
decomposition and the local-window consumer.

The required lift, block-nullity, anchors, and local-window escape proposition
are hypotheses, not proved producers.  This package does not prove
irrationality in Erdős #269.
-/

namespace Erdos249257.ExternalVerification269CarryMechanism

open scoped BigOperators

def carryLiftPerturbation
    (base digit z : ℕ → ℤ) (n : ℕ) : ℤ :=
  base n * z n - z (n + 1) - digit n

def carryLiftError
    (D : ℤ) (z carry : ℕ → ℤ) (n : ℕ) : ℤ :=
  D * z n - carry n

def channelPrefix {G : Type*} [AddCommGroup G]
    (ε : ℕ → G) (N : ℕ) : G :=
  ∑ n ∈ Finset.range N, ε n

def ChannelBlockNull {ι G : Type*} [AddCommGroup G]
    (jumpBase : ℕ → ι) (ε : ℕ → G) : Prop :=
  ∀ a b, jumpBase a = jumpBase b →
    channelPrefix ε a = channelPrefix ε b

inductive Prime235
  | two
  | three
  | five
  deriving DecidableEq

/-- A single error bound below `2^N` contradicts any nonzero integral lift
whose perturbation is block-null and vanishes at genuine `2 → 3` and `2 → 5`
anchors. -/
theorem no_carryLift_of_errorBound_below_twoPow
    (D : ℤ)
    (base digit z carry : ℕ → ℤ)
    (jumpBase : ℕ → Prime235)
    (hcarry :
      ∀ n, carry (n + 1) =
        base n * carry n - D * digit n)
    (hchannel : Function.Surjective jumpBase)
    (hnull :
      ChannelBlockNull jumpBase
        (carryLiftPerturbation base digit z))
    {n23 n25 : ℕ}
    (h23start : jumpBase n23 = .two)
    (h23end : jumpBase (n23 + 1) = .three)
    (h25start : jumpBase n25 = .two)
    (h25end : jumpBase (n25 + 1) = .five)
    (hanchor23 :
      carryLiftPerturbation base digit z n23 = 0)
    (hanchor25 :
      carryLiftPerturbation base digit z n25 = 0)
    (herror0 : carryLiftError D z carry 0 ≠ 0)
    (bound : ℕ → ℕ)
    (hbounded :
      ∀ n, Int.natAbs (carryLiftError D z carry n) ≤ bound n)
    (hbaseTwo : ∀ n, (2 : ℤ) ≤ base n)
    (N : ℕ) (hbelow : bound N < 2 ^ N) :
    False := by
  sorry

/-- Four unit-accurate integral approximants cannot simultaneously satisfy
the two anchor equations and a null first complete `2`-block. -/
theorem no_unitAccurateLift_with_twoAnchors_and_firstTwoBlockNull
    (T0 T1 T2 T3 : ℝ)
    (z0 z1 z2 z3 : ℤ)
    (hT0 : 0 < T0 ∧ T0 < 1)
    (hT1 : 0 < T1 ∧ T1 < 1)
    (hT2 : 0 < T2 ∧ T2 < 1)
    (hT3 : 0 < T3 ∧ T3 < 1)
    (hacc0 : |(z0 : ℝ) - T0| < 1)
    (hacc1 : |(z1 : ℝ) - T1| < 1)
    (hacc2 : |(z2 : ℝ) - T2| < 1)
    (hacc3 : |(z3 : ℝ) - T3| < 1)
    (hanchor23 : 2 * z0 - z1 - 1 = 0)
    (hanchor25 : 2 * z2 - z3 - 1 = 0)
    (hfirstBlock :
      (2 * z0 - z1 - 1) +
        (3 * z1 - z2 - 1) = 0) :
    False := by
  sorry

/-- Block-nullity plus genuine zero `2 → 3` and `2 → 5` anchors extinguishes
the entire perturbation. -/
theorem perturbation_eq_zero_of_blockNull_twoAnchors
    {jumpBase : ℕ → Prime235}
    {ε : ℕ → ℤ}
    (hbase : Function.Surjective jumpBase)
    (hnull : ChannelBlockNull jumpBase ε)
    {n23 n25 : ℕ}
    (h23start : jumpBase n23 = .two)
    (h23end : jumpBase (n23 + 1) = .three)
    (h25start : jumpBase n25 = .two)
    (h25end : jumpBase (n25 + 1) = .five)
    (hanchor23 : ε n23 = 0)
    (hanchor25 : ε n25 = 0) :
    ∀ n, ε n = 0 := by
  sorry

/-- Exact weighted block-defect identity for an integral carry lift. -/
theorem carryLift_blockDefect
    (D : ℤ)
    (base digit z carry : ℕ → ℤ)
    (hcarry :
      ∀ n, carry (n + 1) =
        base n * carry n - D * digit n)
    (a b : ℕ) (hab : a ≤ b) :
    D * (∑ n ∈ Finset.Ico a b,
      carryLiftPerturbation base digit z n) =
      carryLiftError D z carry a -
        carryLiftError D z carry b +
      ∑ n ∈ Finset.Ico a b,
        (base n - 1) * carryLiftError D z carry n := by
  sorry

def carryResidue (B c : ℤ) : ℤ := c % B

def carryQuotient (B c : ℤ) : ℤ := c / B

def residueDigit (B base residue nextResidue : ℤ) : ℤ :=
  (base * residue - nextResidue) / B

/-- Every exact carry recurrence splits into a finite residue digit and an
uncontrolled integral coboundary. -/
theorem carry_eq_residueDigit_add_coboundary
    (B : ℤ) (hB : 0 < B)
    (base carry digit : ℕ → ℤ)
    (hrec : ∀ n,
      carry (n + 1) = base n * carry n - B * digit n) :
    let residue := fun n => carryResidue B (carry n)
    let quotient := fun n => carryQuotient B (carry n)
    ∀ n,
      digit n =
        residueDigit B (base n)
          (residue n) (residue (n + 1)) +
        base n * quotient n - quotient (n + 1) := by
  sorry

def leastPositiveResidue (C : ℕ) (x : ℤ) : ℕ :=
  if x % (C : ℤ) = 0 then C else Int.natAbs (x % (C : ℤ))

def windowBase (b : ℕ → ℤ) (lo : ℕ) : ℕ → ℤ
  | 0 => 1
  | len + 1 => b (lo + len) * windowBase b lo len

def windowForcing (b e : ℕ → ℤ) (lo : ℕ) : ℕ → ℤ
  | 0 => 0
  | len + 1 => b (lo + len) * windowForcing b e lo len + e (lo + len)

/-- The exact denominator-dependent producer consumed by the local-window
contradiction.  It is deliberately named as a proposition, not asserted. -/
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

/-- Cofinal local-window escape rules out a positive reduced carry obeying the
matching recurrence and short bound. -/
theorem no_positive_reducedCarry_of_cofinalLocalWindowEscape
    (b m : ℕ → ℕ) (shortBound : ℕ → ℕ → ℕ)
    (hescape : CofinalLocalWindowEscape b m shortBound)
    (B : ℕ) (hBpos : 0 < B) (hBcoprime : Nat.Coprime B 30)
    (d : ℕ → ℤ)
    (hrec : ∀ n,
      d (n + 1) = (b n : ℤ) * d n - (B : ℤ) * (m n : ℤ))
    (hpos : ∀ n, 0 < d n)
    (hbound : ∀ n, Int.natAbs (d n) ≤ shortBound B n) :
    False := by
  sorry

end Erdos249257.ExternalVerification269CarryMechanism
