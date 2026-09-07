import ErdosProblems.Erdos257.FourNinthsCoinCancellation
import Erdos257PeriodNoncollapse.BooleanMobiusGreedyReduction
import Erdos257PeriodNoncollapse.BooleanMobiusExactTransition

/-!
# The executable 4/9 diagonal is an exact Mersenne quotient defect

The paired diagonal recurrence was originally derived from quotient-greedy rows, but its
finite state and its quotient meaning had become separate formal surfaces.  This module
reconnects them.  At depth `d`, the selected bits are evaluated at the even endpoint `2d`.
Every old quotient scales by four plus exactly the paired divisor load, while a newly
selected boundary rank contributes the literal coin `2^(d+1)+1`.

The resulting signed quotient defect has exactly the same initial state and recurrence as
the executable remainder `rho`.  Thus the two are equal at every depth.  This is an exact
coordinate identity; it does not assert nonnegativity of the defect.
-/

namespace ErdosProblems.Erdos257

namespace FourNinthsQuotientDefect

open Erdos257PeriodNoncollapse
open Erdos257PeriodNoncollapse.BooleanMobiusGreedyReduction
open scoped BigOperators

noncomputable local instance (d : ℕ) : Decidable (FourNinthsDiagonalTakesAt d) :=
  Classical.propDecidable _

/-- The integral target at the even endpoint attached to diagonal depth `d`. -/
def fourNinthsQuotientTarget (d : ℕ) : ℕ :=
  4 ^ (d + 1) / 9

/-- The target remainder modulo nine follows the period-three orbit `4,7,1`. -/
theorem four_pow_succ_mod_nine (d : ℕ) :
    4 ^ (d + 1) % 9 =
      if d % 3 = 0 then 4 else if d % 3 = 1 then 7 else 1 := by
  induction d with
  | zero => norm_num
  | succ d ih =>
      rw [pow_succ, Nat.mul_mod, ih]
      have hmod : d % 3 < 3 := Nat.mod_lt d (by omega)
      interval_cases h : d % 3 <;>
        simp [h, Nat.add_mod] <;> norm_num

/-- The base-four rounding digit of the target is the executable paired pulse. -/
theorem fourNinths_target_roundingDigit (d : ℕ) :
    4 * (4 ^ (d + 1) % 9) / 9 = fourNinthsPairPulse (d + 1) := by
  rw [four_pow_succ_mod_nine]
  have hmod : d % 3 < 3 := Nat.mod_lt d (by omega)
  interval_cases h : d % 3 <;>
    simp [h, Nat.add_mod, fourNinthsPairPulse] <;> norm_num

/-- Exact fourfold recurrence of the integral `4/9` target. -/
theorem fourNinthsQuotientTarget_succ (d : ℕ) :
    fourNinthsQuotientTarget (d + 1) =
      4 * fourNinthsQuotientTarget d + fourNinthsPairPulse (d + 1) := by
  have hpow : 4 ^ (d + 1 + 1) = 4 * 4 ^ (d + 1) := by
    rw [pow_succ]
    ring
  have hdecomp := Nat.mod_add_div (4 ^ (d + 1)) 9
  have hscaled :
      4 * 4 ^ (d + 1) =
        4 * (4 ^ (d + 1) % 9) + 9 * (4 * (4 ^ (d + 1) / 9)) := by
    omega
  unfold fourNinthsQuotientTarget
  rw [hpow, hscaled,
    Nat.add_mul_div_left (4 * (4 ^ (d + 1) % 9))
      (4 * (4 ^ (d + 1) / 9)) (by omega),
    fourNinths_target_roundingDigit]
  omega

/-- The quotient mass of the actual selected diagonal bits at endpoint `2d`. -/
def fourNinthsDiagonalPrefixQuotient (d : ℕ) : ℕ :=
  ∑ a ∈ Finset.range (d + 1),
    fourNinthsStateBit (fourNinthsDiagonalState d) a *
      localMersenneQuotient (2 * d) a

/-- The finite support selected by the executable diagonal through depth `d`. -/
def fourNinthsDiagonalSupport (d : ℕ) : Finset ℕ :=
  (Finset.range (d + 1)).filter fun a ↦
    fourNinthsStateBit (fourNinthsDiagonalState d) a = 1

theorem fourNinthsStateBit_le_one (s : FourNinthsDiagonalState) (a : ℕ) :
    fourNinthsStateBit s a ≤ 1 := by
  unfold fourNinthsStateBit
  split <;> omega

/-- Every selected diagonal rank is a genuine Mersenne rank between two and `d`. -/
theorem fourNinthsDiagonalSupport_rank_bounds
    {d a : ℕ} (ha : a ∈ fourNinthsDiagonalSupport d) :
    2 ≤ a ∧ a ≤ d := by
  rw [fourNinthsDiagonalSupport, Finset.mem_filter] at ha
  rcases ha with ⟨harange, hab⟩
  have had : a ≤ d := by simpa [Finset.mem_range] using harange
  constructor
  · by_contra ha2
    have ha01 : a = 0 ∨ a = 1 := by omega
    rcases ha01 with rfl | rfl
    · simpa [fourNinthsDiagonalState_bit_zero] using hab
    · simpa [fourNinthsDiagonalState_bit_one] using hab
  · exact had

/-- The bit-weighted quotient coordinate is the ordinary finite-support quotient sum. -/
theorem localPrefixQuotient_fourNinthsDiagonalSupport (d : ℕ) :
    localPrefixQuotient (fourNinthsDiagonalSupport d) (2 * d) =
      fourNinthsDiagonalPrefixQuotient d := by
  unfold localPrefixQuotient fourNinthsDiagonalSupport
    fourNinthsDiagonalPrefixQuotient
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro a ha
  by_cases hbit : fourNinthsStateBit (fourNinthsDiagonalState d) a = 1
  · simp [hbit]
  · have hle := fourNinthsStateBit_le_one (fourNinthsDiagonalState d) a
    have hzero : fourNinthsStateBit (fourNinthsDiagonalState d) a = 0 := by omega
    simp [hbit, hzero]

/-- Existing support bits are unchanged by one executable diagonal step. -/
theorem fourNinthsDiagonalState_bit_succ_eq_of_le
    {d a : ℕ} (ha : a ≤ d) :
    fourNinthsStateBit (fourNinthsDiagonalState (d + 1)) a =
      fourNinthsStateBit (fourNinthsDiagonalState d) a := by
  by_cases ha0 : a = 0
  · subst a
    rw [fourNinthsDiagonalState_bit_zero, fourNinthsDiagonalState_bit_zero]
  · have ha1 : 1 ≤ a := Nat.one_le_iff_ne_zero.mpr ha0
    rw [fourNinthsDiagonalState]
    exact fourNinthsDiagonalStep_preserves_existing_bit
      (fourNinthsDiagonalState d) ha1 (by
        rw [fourNinthsDiagonalState_bits_length]
        exact ha)

/-- The newest support bit is precisely the executable take decision. -/
theorem fourNinthsDiagonalState_new_bit (d : ℕ) :
    fourNinthsStateBit (fourNinthsDiagonalState (d + 1)) (d + 1) =
      if FourNinthsDiagonalTakesAt d then 1 else 0 := by
  classical
  by_cases htake : FourNinthsDiagonalTakesAt d
  · have hstrict :
        (2 : ℤ) ^ (d + 1) <
          4 * (fourNinthsDiagonalState d).rho +
            (fourNinthsPairPulse (d + 1) : ℤ) -
            (fourNinthsDiagonalLoad (fourNinthsDiagonalState d) (d + 1) : ℤ) := by
      unfold FourNinthsDiagonalTakesAt at htake
      push_cast at htake
      omega
    rw [fourNinthsDiagonalState]
    simp [fourNinthsDiagonalStep, fourNinthsStateBit,
      fourNinthsDiagonalState_bits_length, htake, hstrict]
  · have hstrict : ¬
        ((2 : ℤ) ^ (d + 1) <
          4 * (fourNinthsDiagonalState d).rho +
            (fourNinthsPairPulse (d + 1) : ℤ) -
            (fourNinthsDiagonalLoad (fourNinthsDiagonalState d) (d + 1) : ℤ)) := by
      intro h
      apply htake
      unfold FourNinthsDiagonalTakesAt
      push_cast
      omega
    rw [fourNinthsDiagonalState]
    simp [fourNinthsDiagonalStep, fourNinthsStateBit,
      fourNinthsDiagonalState_bits_length, htake, hstrict]

/-- The two-step quotient pulse, kept local to avoid importing the unrelated
denominator-21 greedy theorem forest. -/
def fourNinthsMersenneTwoStepPulse (M a : ℕ) : ℕ :=
  2 * (if a ∣ M + 1 then 1 else 0) +
    (if a ∣ M + 2 then 1 else 0)

/-- The local two-step quotient pulse is exactly the paired diagonal rank load. -/
theorem fourNinthsMersenneTwoStepPulse_eq_rankLoad (d a : ℕ) :
    fourNinthsMersenneTwoStepPulse (2 * d) a =
      fourNinthsRankLoad a (d + 1) := by
  unfold fourNinthsMersenneTwoStepPulse fourNinthsRankLoad
  rw [show 2 * d + 1 = 2 * (d + 1) - 1 by omega,
    show 2 * d + 2 = 2 * (d + 1) by omega]
  split_ifs <;> omega

/-- Minimal two-step quotient transition, kept here to avoid importing the unrelated
denominator-21 greedy theorem forest. -/
theorem localMersenneQuotient_add_two_fourNinths
    {M a : ℕ} (ha : 2 ≤ a) :
    localMersenneQuotient (M + 2) a =
      4 * localMersenneQuotient M a + fourNinthsMersenneTwoStepPulse M a := by
  rw [show M + 2 = (M + 1) + 1 by omega,
    localMersenneQuotient_endpoint_succ ha,
    localMersenneQuotient_endpoint_succ ha]
  unfold fourNinthsMersenneTwoStepPulse
  split_ifs <;> omega

/-- The old support's quotient mass scales by four and emits exactly the paired load. -/
theorem fourNinthsDiagonalPrefixQuotient_oldPart_succ (d : ℕ) :
    (∑ a ∈ Finset.range (d + 1),
        fourNinthsStateBit (fourNinthsDiagonalState (d + 1)) a *
          localMersenneQuotient (2 * (d + 1)) a) =
      4 * fourNinthsDiagonalPrefixQuotient d +
        fourNinthsDiagonalLoad (fourNinthsDiagonalState d) (d + 1) := by
  rw [fourNinthsDiagonalLoad_eq_abstract]
  unfold fourNinthsDiagonalPrefixQuotient fourNinthsAbstractDiagonalLoad
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a ha
  have had : a ≤ d := by simpa [Finset.mem_range] using ha
  rw [fourNinthsDiagonalState_bit_succ_eq_of_le had]
  by_cases ha2 : 2 ≤ a
  · rw [show 2 * (d + 1) = 2 * d + 2 by omega,
      localMersenneQuotient_add_two_fourNinths ha2,
      fourNinthsMersenneTwoStepPulse_eq_rankLoad]
    ring
  · have ha01 : a = 0 ∨ a = 1 := by omega
    rcases ha01 with rfl | rfl
    · simp [fourNinthsDiagonalState_bit_zero]
    · simp [fourNinthsDiagonalState_bit_one]

/-- The boundary quotient coin is added exactly when the executable diagonal takes it. -/
theorem fourNinthsDiagonalPrefixQuotient_newPart_succ (d : ℕ) :
    fourNinthsStateBit (fourNinthsDiagonalState (d + 1)) (d + 1) *
        localMersenneQuotient (2 * (d + 1)) (d + 1) =
      if FourNinthsDiagonalTakesAt d then 2 ^ (d + 1) + 1 else 0 := by
  by_cases hd : d = 0
  · subst d
    have hnot : ¬ FourNinthsDiagonalTakesAt 0 := by
      norm_num [FourNinthsDiagonalTakesAt, fourNinthsDiagonalState,
        fourNinthsPairPulse, fourNinthsDiagonalLoad]
    rw [fourNinthsDiagonalState_new_bit]
    simp [hnot]
  · have hrank : 2 ≤ d + 1 := by omega
    rw [fourNinthsDiagonalState_new_bit,
      BooleanMobiusGreedyReduction.localMersenneQuotient_two_mul_self hrank]
    split_ifs <;> simp

/-- Exact affine recurrence of the quotient mass carried by the actual bit word. -/
theorem fourNinthsDiagonalPrefixQuotient_succ (d : ℕ) :
    fourNinthsDiagonalPrefixQuotient (d + 1) =
      4 * fourNinthsDiagonalPrefixQuotient d +
        fourNinthsDiagonalLoad (fourNinthsDiagonalState d) (d + 1) +
        if FourNinthsDiagonalTakesAt d then 2 ^ (d + 1) + 1 else 0 := by
  change (∑ a ∈ Finset.range ((d + 1) + 1),
      fourNinthsStateBit (fourNinthsDiagonalState (d + 1)) a *
        localMersenneQuotient (2 * (d + 1)) a) = _
  rw [Finset.sum_range_succ,
    fourNinthsDiagonalPrefixQuotient_oldPart_succ,
    fourNinthsDiagonalPrefixQuotient_newPart_succ]

/-- Signed even-horizon quotient defect of the executable diagonal support. -/
def fourNinthsDiagonalQuotientDefect (d : ℕ) : ℤ :=
  (fourNinthsQuotientTarget d : ℤ) -
    (fourNinthsDiagonalPrefixQuotient d : ℤ)

/-- The signed quotient defect obeys the executable history-increment recurrence. -/
theorem fourNinthsDiagonalQuotientDefect_succ (d : ℕ) :
    fourNinthsDiagonalQuotientDefect (d + 1) =
      4 * fourNinthsDiagonalQuotientDefect d +
        fourNinthsDiagonalHistoryIncrement d := by
  classical
  by_cases htake : FourNinthsDiagonalTakesAt d
  · rw [fourNinthsDiagonalQuotientDefect, fourNinthsDiagonalQuotientDefect,
      fourNinthsQuotientTarget_succ, fourNinthsDiagonalPrefixQuotient_succ]
    simp [fourNinthsDiagonalHistoryIncrement,
      fourNinthsDiagonalHistoryCoinCharge, htake]
    push_cast
    ring
  · rw [fourNinthsDiagonalQuotientDefect, fourNinthsDiagonalQuotientDefect,
      fourNinthsQuotientTarget_succ, fourNinthsDiagonalPrefixQuotient_succ]
    simp [fourNinthsDiagonalHistoryIncrement,
      fourNinthsDiagonalHistoryCoinCharge, htake]
    push_cast
    ring

/-- **Quotient-defect bridge.**  The executable remainder is exactly the signed difference
between `floor(4^(d+1)/9)` and the selected Mersenne quotient mass at endpoint `2d`. -/
theorem fourNinthsDiagonalState_rho_eq_quotientDefect (d : ℕ) :
    (fourNinthsDiagonalState d).rho = fourNinthsDiagonalQuotientDefect d := by
  induction d with
  | zero => decide
  | succ d ih =>
      rw [fourNinthsDiagonalState_rho_succ_eq_historyIncrement,
        fourNinthsDiagonalQuotientDefect_succ, ih]

/-- Expanded form of the bridge, with both integral quotient terms visible. -/
theorem fourNinthsDiagonalState_rho_eq_target_sub_prefixQuotient (d : ℕ) :
    (fourNinthsDiagonalState d).rho =
      (fourNinthsQuotientTarget d : ℤ) -
        (fourNinthsDiagonalPrefixQuotient d : ℤ) := by
  simpa [fourNinthsDiagonalQuotientDefect] using
    fourNinthsDiagonalState_rho_eq_quotientDefect d

/-- Remainder nonnegativity is exactly quotient admissibility of the actual bit row. -/
theorem fourNinthsDiagonalState_rho_nonnegative_iff_prefixQuotient_le (d : ℕ) :
    0 ≤ (fourNinthsDiagonalState d).rho ↔
      fourNinthsDiagonalPrefixQuotient d ≤ fourNinthsQuotientTarget d := by
  rw [fourNinthsDiagonalState_rho_eq_target_sub_prefixQuotient]
  push_cast
  omega

/-- Inside the nonnegative strip, the dyadic remainder ceiling is literally a small
even-horizon quotient-defect window. -/
theorem fourNinthsDiagonalState_rho_lt_twoPow_iff_quotientWindow
    (d : ℕ)
    (_hnonneg : 0 ≤ (fourNinthsDiagonalState d).rho) :
    (fourNinthsDiagonalState d).rho < (2 : ℤ) ^ d ↔
      fourNinthsQuotientTarget d <
        fourNinthsDiagonalPrefixQuotient d + 2 ^ d := by
  have hbridge := fourNinthsDiagonalState_rho_eq_target_sub_prefixQuotient d
  have hpowcast : (((2 ^ d : ℕ) : ℤ)) = (2 : ℤ) ^ d := by norm_cast
  constructor
  · intro hlt
    have hcast :
        (fourNinthsQuotientTarget d : ℤ) <
          (fourNinthsDiagonalPrefixQuotient d : ℤ) + ((2 ^ d : ℕ) : ℤ) := by
      omega
    exact_mod_cast hcast
  · intro hlt
    have hcast :
        (fourNinthsQuotientTarget d : ℤ) <
          (fourNinthsDiagonalPrefixQuotient d : ℤ) + ((2 ^ d : ℕ) : ℤ) := by
      exact_mod_cast hlt
    omega

#print axioms fourNinthsQuotientTarget_succ
#print axioms fourNinthsDiagonalState_new_bit
#print axioms fourNinthsMersenneTwoStepPulse_eq_rankLoad
#print axioms fourNinthsDiagonalPrefixQuotient_succ
#print axioms fourNinthsDiagonalQuotientDefect_succ
#print axioms fourNinthsDiagonalState_rho_eq_quotientDefect
#print axioms fourNinthsDiagonalState_rho_nonnegative_iff_prefixQuotient_le
#print axioms fourNinthsDiagonalState_rho_lt_twoPow_iff_quotientWindow

end FourNinthsQuotientDefect

end ErdosProblems.Erdos257
