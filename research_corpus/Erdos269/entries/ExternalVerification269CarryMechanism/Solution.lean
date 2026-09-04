/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib
import ErdosProblems.Erdos269.CarryLiftExtinction
import ErdosProblems.Erdos269.RestrictedFloorSum
import ErdosProblems.Erdos269.WeightedPhaseCarry

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

abbrev Prime235 := ErdosProblems.Erdos269.Prime235

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
  have hnull' :
      ErdosProblems.Erdos269.ChannelBlockNull jumpBase
        (ErdosProblems.Erdos269.carryLiftPerturbation base digit z) := by
    simpa [ChannelBlockNull, channelPrefix, carryLiftPerturbation,
      ErdosProblems.Erdos269.ChannelBlockNull,
      ErdosProblems.Erdos269.channelPrefix,
      ErdosProblems.Erdos269.carryLiftPerturbation] using hnull
  simpa [carryLiftPerturbation, carryLiftError,
    ErdosProblems.Erdos269.carryLiftPerturbation,
    ErdosProblems.Erdos269.carryLiftError] using
    ErdosProblems.Erdos269.no_carryLift_of_errorBound_below_twoPow
      D base digit z carry jumpBase hcarry hchannel hnull'
      h23start h23end h25start h25end
      hanchor23 hanchor25 herror0 bound hbounded hbaseTwo N hbelow

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
  exact
    ErdosProblems.Erdos269.no_unitAccurateLift_with_twoAnchors_and_firstTwoBlockNull
      T0 T1 T2 T3 z0 z1 z2 z3 hT0 hT1 hT2 hT3
      hacc0 hacc1 hacc2 hacc3 hanchor23 hanchor25 hfirstBlock

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
  have hnull' :
      ErdosProblems.Erdos269.ChannelBlockNull jumpBase ε := by
    simpa [ChannelBlockNull, channelPrefix,
      ErdosProblems.Erdos269.ChannelBlockNull,
      ErdosProblems.Erdos269.channelPrefix] using hnull
  exact
    ErdosProblems.Erdos269.perturbation_eq_zero_of_blockNull_twoAnchors
      hbase hnull' h23start h23end h25start h25end hanchor23 hanchor25

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
  simpa [carryLiftPerturbation, carryLiftError,
    ErdosProblems.Erdos269.carryLiftPerturbation,
    ErdosProblems.Erdos269.carryLiftError] using
    ErdosProblems.Erdos269.carryLift_blockDefect
      D base digit z carry hcarry a b hab

def carryResidue (B c : ℤ) : ℤ := c % B
def carryQuotient (B c : ℤ) : ℤ := c / B
def residueDigit (B base residue nextResidue : ℤ) : ℤ :=
  (base * residue - nextResidue) / B

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
  simpa [carryResidue, carryQuotient, residueDigit,
    ErdosProblems.Erdos269.carryResidue,
    ErdosProblems.Erdos269.carryQuotient,
    ErdosProblems.Erdos269.residueDigit] using
    ErdosProblems.Erdos269.carry_eq_residueDigit_add_coboundary
      B hB base carry digit hrec

abbrev leastPositiveResidue :=
  ErdosProblems.Erdos269.leastPositiveResidue

abbrev windowBase := ErdosProblems.Erdos269.windowBase

abbrev windowForcing := ErdosProblems.Erdos269.windowForcing

abbrev CofinalLocalWindowEscape :=
  ErdosProblems.Erdos269.CofinalLocalWindowEscape

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
  exact
    ErdosProblems.Erdos269.no_positive_reducedCarry_of_cofinalLocalWindowEscape
      b m shortBound hescape B hBpos hBcoprime d hrec hpos hbound

end Erdos249257.ExternalVerification269CarryMechanism
