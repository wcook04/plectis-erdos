import Erdos249257.TerminalOnlyScaledVanishing
import Erdos249257.DyadicPrefixCompression
import Mathlib.NumberTheory.Real.Irrational

/-!
# Erdős #257: the rational-half counterexample frontier

This module records two distinct boundary results.  First, a
`HalfTerminalOnlyScaledVanishingSequence` would produce an infinite support
whose reciprocal-Mersenne subseries is exactly `1/2`, and would therefore
refute the universal irrationality assertion.  No such sequence is
constructed here; finite suffix-cylinder computations do not supply the
required cofinal hypothesis.

Second, no finite Boolean support using ranks at least two can sum to
`1/21`.  This does not construct a representation of `1/21` or prove its
membership in the achievement set.  Neither result settles Erdős #257.
-/

namespace ErdosProblems.Erdos257

open Erdos249257
open Erdos249257.HalfCarryReachability

/-- The universal irrationality assertion in Erdős #257. -/
def UniversalMersenneSubseriesIrrationality : Prop :=
  ∀ A : Set ℕ, A.Infinite → Irrational (erdosSupportSeries 2 A)

/-- Any terminal scaled-vanishing sequence supplies an infinite rational
counterexample of exact value `1/2`. -/
theorem exists_rational_half_counterexample_of_terminalScaledVanishing
    (S : HalfTerminalOnlyScaledVanishingSequence) :
    ∃ A : Set ℕ, A.Infinite ∧
      erdosSupportSeries 2 A = (1 : ℝ) / 2 :=
  exists_infinite_support_half_of_terminalScaledVanishing S

/-- The same conditional hypothesis negates the universal irrationality
claim. -/
theorem not_universal_of_terminalScaledVanishing
    (S : HalfTerminalOnlyScaledVanishingSequence) :
    ¬ UniversalMersenneSubseriesIrrationality := by
  obtain ⟨A, hA, hhalf⟩ :=
    exists_rational_half_counterexample_of_terminalScaledVanishing S
  intro huniversal
  have hirr := huniversal A hA
  rw [hhalf] at hirr
  have hcast : (1 / 2 : ℝ) = ((1 / 2 : ℚ) : ℝ) := by norm_num
  rw [hcast] at hirr
  exact (Rat.not_irrational (1 / 2 : ℚ)) hirr

/-! ## The rational target `1/21` cannot terminate -/

/-- No finite Boolean support on the genuine reciprocal-Mersenne ranks can
sum to `1/21`.  The reduced-denominator order theorem forces the support lcm
to be six, hence every selected rank is one of `2`, `3`, or `6`; the eight
remaining finite possibilities are then exact arithmetic.

Consequently, if a representation of `1/21` is first reduced to Boolean
support using only ranks at least two, this theorem rules out finite support.
The existence of such a representation is not proved here. -/
theorem finiteErdosSum_ne_one_div_twenty_one
    (F : Finset ℕ) (hF : ∀ n ∈ F, 2 ≤ n) :
    finiteErdosSum F 2 ≠ (1 : ℚ) / 21 := by
  intro heq
  have h0 : 0 ∉ F := by
    intro hzero
    have := hF 0 hzero
    omega
  have hne : F.Nonempty := by
    by_contra hempty
    rw [Finset.not_nonempty_iff_eq_empty.mp hempty] at heq
    norm_num [finiteErdosSum] at heq
  have horder :=
    oddDoublingOrder_finiteErdosSum_den_eq_lcm F hne h0
  have hden : (finiteErdosSum F 2).den = 21 := by
    rw [heq]
    norm_num
  have horder' :
      oddDoublingOrder 21 (by decide : Odd 21) = F.lcm id := by
    simpa only [hden] using horder
  have horder21 : oddDoublingOrder 21 (by decide : Odd 21) = 6 :=
    two_three_dyadicPrefix_fixture.2.2.1
  rw [horder21] at horder'
  have hlcm : F.lcm id = 6 := horder'.symm
  have hlcm' : F.lcm (fun m : ℕ ↦ m) = 6 := by
    simpa only [id_eq] using hlcm
  have hranks : ∀ n ∈ F, n = 2 ∨ n = 3 ∨ n = 6 := by
    intro n hn
    have hndvd : n ∣ 6 := by
      rw [← hlcm']
      exact Finset.dvd_lcm (f := fun m : ℕ ↦ m) hn
    have hnle : n ≤ 6 := Nat.le_of_dvd (by omega) hndvd
    obtain ⟨k, hk⟩ := hndvd
    have hn2 := hF n hn
    interval_cases n <;> omega
  have hF_eq :
      F = ({2, 3, 6} : Finset ℕ).filter (fun n ↦ n ∈ F) := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_insert,
      Finset.mem_singleton]
    constructor
    · intro hn
      exact ⟨hranks n hn, hn⟩
    · exact fun hn ↦ hn.2
  by_cases h2 : 2 ∈ F <;>
    by_cases h3 : 3 ∈ F <;>
      by_cases h6 : 6 ∈ F <;> {
        rw [hF_eq] at heq
        simp only [finiteErdosSum, Finset.sum_filter] at heq
        norm_num [finiteErdosSum, h2, h3, h6] at heq
      }

end ErdosProblems.Erdos257
