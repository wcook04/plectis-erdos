import Erdos257PeriodNoncollapse.BooleanMobiusCarry
import Erdos257PeriodNoncollapse.TwentyOneQuotientGreedy
import ErdosProblems.Erdos257.HalfCounterexampleFrontier

/-!
# Erdős #257: the denominator-21 running-maximum producer

Let `Q N` be the canonical denominator-`21` greedy defect and let

`H N = 1 + max {Q k | k < N}`.

This module isolates the exact doubling-height inequality suggested by the
record census,

`H (2 * d) ≤ 2 * H d`.

The inequality alone forces a global linear bound for `Q`; hence `Q` is
subexponential relative to `2^N`, and the already checked exact defect
criterion puts `1/21` in the Mersenne achievement set.  The doubling-height
inequality is the primary open producer in this module.  The record-only,
nested-height, and sharper causal-midpoint forms below isolate sufficient
source-specific alternatives; none of those all-depth laws is proved here.
-/

namespace ErdosProblems.Erdos257

open Erdos257PeriodNoncollapse
open Filter Set

/-- One plus the largest denominator-`21` defect strictly before `N`. -/
noncomputable def twentyOneDefectHeight : ℕ → ℕ
  | 0 => 1
  | N + 1 => max (twentyOneDefectHeight N) (twentyOneGreedyDefect N + 1)

@[simp] theorem twentyOneDefectHeight_zero :
    twentyOneDefectHeight 0 = 1 := rfl

@[simp] theorem twentyOneDefectHeight_succ (N : ℕ) :
    twentyOneDefectHeight (N + 1) =
      max (twentyOneDefectHeight N) (twentyOneGreedyDefect N + 1) := rfl

/-- The running height is nondecreasing. -/
theorem twentyOneDefectHeight_le_succ (N : ℕ) :
    twentyOneDefectHeight N ≤ twentyOneDefectHeight (N + 1) := by
  rw [twentyOneDefectHeight_succ]
  exact le_max_left _ _

theorem twentyOneDefectHeight_monotone :
    Monotone twentyOneDefectHeight :=
  monotone_nat_of_le_succ twentyOneDefectHeight_le_succ

/-- Every defect is dominated by the height immediately after it. -/
theorem twentyOneGreedyDefect_add_one_le_height_succ (N : ℕ) :
    twentyOneGreedyDefect N + 1 ≤ twentyOneDefectHeight (N + 1) := by
  rw [twentyOneDefectHeight_succ]
  exact le_max_right _ _

/-- The sole arithmetic producer on this route. -/
def TwentyOneDefectDoublingHeightBound : Prop :=
  ∀ d : ℕ, twentyOneDefectHeight (2 * d) ≤ 2 * twentyOneDefectHeight d

/-- Record-only form of the doubling producer.  When `Q_N + 1` starts a new
height plateau, it is enough to compare that new height with the height at the
ceiling midpoint of the plateau start `N+1`.  Non-record ranks carry no new
obligation. -/
def TwentyOneDefectRecordMidpointBound : Prop :=
  ∀ N : ℕ,
    twentyOneDefectHeight N < twentyOneGreedyDefect N + 1 →
      twentyOneGreedyDefect N + 1 ≤
        2 * twentyOneDefectHeight ((N + 2) / 2)

/-- Phase-neutral nested-height service at an even midpoint.  The antecedent
says that `2*d-1` is a strict defect record.  This is the coupled inequality
`(NH')`; neither of its two natural summands is asserted to be bounded
separately. -/
def TwentyOneDefectNestedHeightService : Prop :=
  ∀ d : ℕ, 0 < d → Even d →
    twentyOneDefectHeight (2 * d - 1) <
        twentyOneGreedyDefect (2 * d - 1) + 1 →
      2 * (twentyOneGreedyDefect (2 * d - 1) -
            twentyOneGreedyDefect (d - 1)) +
          twentyOneGreedyDefect d ≤
        twentyOneDefectHeight d + twentyOneDefectHeight (d / 2)

/-- The sharper causal service suggested by the deep denominator-`21` audit.
It replaces the second height by the exact constant two.  This is stronger
than `TwentyOneDefectNestedHeightService`, but its left side depends only on
the record and its midpoint prefix. -/
def TwentyOneDefectCausalMidpointService : Prop :=
  ∀ d : ℕ, 0 < d → Even d →
    twentyOneDefectHeight (2 * d - 1) <
        twentyOneGreedyDefect (2 * d - 1) + 1 →
      2 * (twentyOneGreedyDefect (2 * d - 1) -
            twentyOneGreedyDefect (d - 1)) +
          twentyOneGreedyDefect d ≤
        twentyOneDefectHeight d + 2

/-- Source-specific quarter-phase lock after the finite seed: every later
strict record successor is divisible by four. -/
def TwentyOneDefectQuarterPhaseRecordLock : Prop :=
  ∀ N : ℕ, 19 < N →
    twentyOneDefectHeight N < twentyOneGreedyDefect N + 1 →
      4 ∣ N + 1

/-- The finite record-midpoint certificate through the last exceptional
seed rank.  Keeping this separate prevents finite computation from being
mistaken for either all-depth producer. -/
def TwentyOneDefectInitialRecordMidpointBound : Prop :=
  ∀ N : ℕ, N ≤ 19 →
    twentyOneDefectHeight N < twentyOneGreedyDefect N + 1 →
      twentyOneGreedyDefect N + 1 ≤
        2 * twentyOneDefectHeight ((N + 2) / 2)

private def twentyOneInitialSupport : Finset ℕ :=
  {5, 7, 8, 9, 10, 11, 13, 16, 18, 20}

/-- Kernel-reduced rational greedy certificate for the complete seed prefix
used below. -/
private theorem greedyMersennePrefixRat_one_div_twenty_one_twenty :
    greedyMersennePrefixRat (1 / 21 : ℚ) 20 = twentyOneInitialSupport := by
  native_decide

private theorem mem_twentyOnePrefixRat_iff_real_support
    {n d : ℕ} (hd1 : 1 ≤ d) (hdn : d ≤ n) :
    d ∈ greedyMersennePrefixRat (1 / 21 : ℚ) n ↔
      d ∈ greedyMersenneSupport (1 / 21 : ℝ) := by
  classical
  unfold greedyMersennePrefixRat
  constructor
  · intro hd
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hd
    obtain ⟨-, htake⟩ := Finset.mem_filter.mp hj
    have htakeR :=
      (rational_greedy_take_iff_real (1 / 21 : ℚ) j).1 htake
    norm_num at htakeR
    exact (succ_mem_greedyMersenneSupport_iff (1 / 21 : ℝ) j).2 htakeR
  · intro hd
    refine Finset.mem_image.mpr ⟨d - 1, ?_, by omega⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_range.mpr (by omega), ?_⟩
    apply (rational_greedy_take_iff_real (1 / 21 : ℚ) (d - 1)).2
    have htakeR :=
      (succ_mem_greedyMersenneSupport_iff (1 / 21 : ℝ) (d - 1)).1
        (by simpa only [Nat.sub_add_cancel hd1] using hd)
    norm_num at htakeR ⊢
    exact htakeR

private theorem twentyOneSupport_inter_Iic_twenty :
    greedyMersenneSupport (1 / 21 : ℝ) ∩ Set.Iic 20 =
      (twentyOneInitialSupport : Set ℕ) := by
  classical
  ext d
  constructor
  · rintro ⟨hdA, hd20⟩
    have hd1 : 1 ≤ d := by
      by_contra hdnot
      have hd0 : d = 0 := by omega
      subst d
      exact (zero_not_mem_greedyMersenneSupport (1 / 21 : ℝ)) hdA
    have hpref : d ∈ greedyMersennePrefixRat (1 / 21 : ℚ) 20 :=
      (mem_twentyOnePrefixRat_iff_real_support hd1 hd20).2 hdA
    rw [greedyMersennePrefixRat_one_div_twenty_one_twenty] at hpref
    exact hpref
  · intro hdP
    have hpref : d ∈ greedyMersennePrefixRat (1 / 21 : ℚ) 20 := by
      rw [greedyMersennePrefixRat_one_div_twenty_one_twenty]
      exact hdP
    have hdP' : d ∈ twentyOneInitialSupport := by
      rw [← greedyMersennePrefixRat_one_div_twenty_one_twenty]
      exact hpref
    have hdBounds : 1 ≤ d ∧ d ≤ 20 := by
      simp [twentyOneInitialSupport] at hdP'
      omega
    exact ⟨(mem_twentyOnePrefixRat_iff_real_support
      hdBounds.1 hdBounds.2).1 hpref, hdBounds.2⟩

private theorem twentyOneSupportCoeff_eq_initial
    {n : ℕ} (hn : n ≤ 20) :
    supportCoeff (greedyMersenneSupport (1 / 21 : ℝ)) n =
      supportCoeff (twentyOneInitialSupport : Set ℕ) n := by
  rw [← supportCoeff_inter_Iic_eq_of_le
    (greedyMersenneSupport (1 / 21 : ℝ)) hn,
    twentyOneSupport_inter_Iic_twenty]

private theorem twentyOneBinaryCoeffPrefixNumerator_eq_initial
    (N : ℕ) (hN : N ≤ 20) :
    binaryCoeffPrefixNumerator
        (supportCoeff (greedyMersenneSupport (1 / 21 : ℝ))) N =
      binaryCoeffPrefixNumerator
        (supportCoeff (twentyOneInitialSupport : Set ℕ)) N := by
  induction N with
  | zero => rfl
  | succ N ih =>
      rw [binaryCoeffPrefixNumerator, binaryCoeffPrefixNumerator,
        ih (by omega), twentyOneSupportCoeff_eq_initial (by omega)]

private theorem twentyOneGreedyDefect_le_one_through_eighteen
    (N : ℕ) (hN : N ≤ 18) :
    twentyOneGreedyDefect N ≤ 1 := by
  interval_cases N <;>
    rw [twentyOneGreedyDefect,
      twentyOneBinaryCoeffPrefixNumerator_eq_initial _ (by omega)] <;>
    norm_num [binaryCoeffPrefixNumerator, supportCoeff_eq_card_filter,
      twentyOneInitialSupport] <;> decide

private theorem twentyOneGreedyDefect_six :
    twentyOneGreedyDefect 6 = 1 := by
  rw [twentyOneGreedyDefect,
    twentyOneBinaryCoeffPrefixNumerator_eq_initial 6 (by omega)]
  norm_num [binaryCoeffPrefixNumerator, supportCoeff_eq_card_filter,
    twentyOneInitialSupport] <;> decide

private theorem twentyOneGreedyDefect_nineteen :
    twentyOneGreedyDefect 19 = 2 := by
  rw [twentyOneGreedyDefect,
    twentyOneBinaryCoeffPrefixNumerator_eq_initial 19 (by omega)]
  norm_num [binaryCoeffPrefixNumerator, supportCoeff_eq_card_filter,
    twentyOneInitialSupport] <;> decide

/-- At every late record midpoint, the causal `H(d)+2` service already pays
the record-midpoint bill.  The constant two is absorbed by the proved seed
height `H(7) >= Q_6+1 = 2`. -/
theorem twentyOneRecordMidpointBound_of_causalMidpoint_at
    {d : ℕ} (hd7 : 7 ≤ d)
    (hrecord :
      twentyOneDefectHeight (2 * d - 1) <
        twentyOneGreedyDefect (2 * d - 1) + 1)
    (hservice :
      2 * (twentyOneGreedyDefect (2 * d - 1) -
            twentyOneGreedyDefect (d - 1)) +
          twentyOneGreedyDefect d ≤
        twentyOneDefectHeight d + 2) :
    twentyOneGreedyDefect (2 * d - 1) + 1 ≤
      2 * twentyOneDefectHeight d := by
  have hd : 0 < d := by omega
  have hdle : d ≤ 2 * d - 1 := by omega
  have hheight :
      twentyOneDefectHeight d ≤ twentyOneDefectHeight (2 * d - 1) :=
    twentyOneDefectHeight_monotone hdle
  have hprev :
      twentyOneGreedyDefect (d - 1) + 1 ≤ twentyOneDefectHeight d := by
    have h := twentyOneGreedyDefect_add_one_le_height_succ (d - 1)
    simpa only [Nat.sub_add_cancel hd] using h
  have hprevRecord :
      twentyOneGreedyDefect (d - 1) ≤
        twentyOneGreedyDefect (2 * d - 1) := by
    omega
  have hQ6 := twentyOneGreedyDefect_add_one_le_height_succ 6
  rw [twentyOneGreedyDefect_six] at hQ6
  norm_num only [Nat.reduceAdd] at hQ6
  have hH7d : twentyOneDefectHeight 7 ≤ twentyOneDefectHeight d :=
    twentyOneDefectHeight_monotone hd7
  omega

/-- The only record successor not divisible by four is the finite seed at
rank six, and its midpoint budget is exact. -/
theorem twentyOneDefectInitialRecordMidpointBound :
    TwentyOneDefectInitialRecordMidpointBound := by
  intro N hN _hrecord
  by_cases hN18 : N ≤ 18
  · have hQ := twentyOneGreedyDefect_le_one_through_eighteen N hN18
    have hheight : 1 ≤ twentyOneDefectHeight ((N + 2) / 2) := by
      rw [← twentyOneDefectHeight_zero]
      exact twentyOneDefectHeight_monotone (Nat.zero_le _)
    omega
  · have hN19 : N = 19 := by omega
    subst N
    have hQ6 := twentyOneGreedyDefect_add_one_le_height_succ 6
    rw [twentyOneGreedyDefect_six] at hQ6
    norm_num only [Nat.reduceAdd] at hQ6
    have hH : twentyOneDefectHeight 7 ≤ twentyOneDefectHeight 10 :=
      twentyOneDefectHeight_monotone (by omega)
    rw [twentyOneGreedyDefect_nineteen]
    norm_num only [Nat.reduceAdd, Nat.reduceDiv]
    omega

/-- Exact doubled-service identity.  It is the recurrence-level bridge from
the new divisor layer `f(2d)-f(d)` to the phase-neutral record increment.
No record, phase, or asymptotic hypothesis is used. -/
theorem twentyOneEulerMidpointService_identity (d : ℕ) (hd : 0 < d) :
    ((supportCoeff (greedyMersenneSupport (1 / 21 : ℝ)) (2 * d) : ℤ) -
          (supportCoeff (greedyMersenneSupport (1 / 21 : ℝ)) d : ℤ)) +
        (twentyOneGreedyDefect (2 * d) : ℤ) =
      2 * ((twentyOneGreedyDefect (2 * d - 1) : ℤ) -
            (twentyOneGreedyDefect (d - 1) : ℤ)) +
        (twentyOneGreedyDefect d : ℤ) +
          twentyOneFloorBit (2 * d - 1) - twentyOneFloorBit (d - 1) := by
  have hdouble := twentyOneGreedyDefect_succ (2 * d - 1)
  have hmid := twentyOneGreedyDefect_succ (d - 1)
  have hdoubleIndex : 2 * d - 1 + 1 = 2 * d := by omega
  have hmidIndex : d - 1 + 1 = d := by omega
  rw [hdoubleIndex] at hdouble
  rw [hmidIndex] at hmid
  omega

/-- The nested-height service at one strict record supplies its required
record-midpoint bound.  Monotonicity pays the two old-height contributions;
the coupled service pays only the genuinely new record increment. -/
theorem twentyOneRecordMidpointBound_of_nestedHeight_at
    {d : ℕ} (hd : 0 < d)
    (hrecord :
      twentyOneDefectHeight (2 * d - 1) <
        twentyOneGreedyDefect (2 * d - 1) + 1)
    (hservice :
      2 * (twentyOneGreedyDefect (2 * d - 1) -
            twentyOneGreedyDefect (d - 1)) +
          twentyOneGreedyDefect d ≤
        twentyOneDefectHeight d + twentyOneDefectHeight (d / 2)) :
    twentyOneGreedyDefect (2 * d - 1) + 1 ≤
      2 * twentyOneDefectHeight d := by
  have hdle : d ≤ 2 * d - 1 := by omega
  have hheight :
      twentyOneDefectHeight d ≤ twentyOneDefectHeight (2 * d - 1) :=
    twentyOneDefectHeight_monotone hdle
  have hprev :
      twentyOneGreedyDefect (d - 1) + 1 ≤ twentyOneDefectHeight d := by
    have h := twentyOneGreedyDefect_add_one_le_height_succ (d - 1)
    simpa only [Nat.sub_add_cancel hd] using h
  have hprevRecord :
      twentyOneGreedyDefect (d - 1) ≤
        twentyOneGreedyDefect (2 * d - 1) := by
    omega
  have hhalf :
      twentyOneDefectHeight (d / 2) ≤ twentyOneDefectHeight d :=
    twentyOneDefectHeight_monotone (Nat.div_le_self d 2)
  omega

/-- The finite seed certificate, quarter-phase lock, and nested-height
service together prove the exact record-only producer. -/
theorem twentyOneDefectRecordMidpointBound_of_nestedHeightService
    (hseed : TwentyOneDefectInitialRecordMidpointBound)
    (hphase : TwentyOneDefectQuarterPhaseRecordLock)
    (hservice : TwentyOneDefectNestedHeightService) :
    TwentyOneDefectRecordMidpointBound := by
  intro N hrecord
  by_cases hN : N ≤ 19
  · exact hseed N hN hrecord
  · have hlate : 19 < N := by omega
    obtain ⟨k, hk⟩ := hphase N hlate hrecord
    let d := 2 * k
    have hd : 0 < d := by
      dsimp [d]
      omega
    have heven : Even d := ⟨k, by
      dsimp [d]
      omega⟩
    have hNform : N = 2 * d - 1 := by
      dsimp [d]
      omega
    have hmid : (N + 2) / 2 = d := by
      dsimp [d]
      omega
    have hrecord' :
        twentyOneDefectHeight (2 * d - 1) <
          twentyOneGreedyDefect (2 * d - 1) + 1 := by
      simpa only [← hNform] using hrecord
    have hnested := hservice d hd heven hrecord'
    have hbound :=
      twentyOneRecordMidpointBound_of_nestedHeight_at hd hrecord' hnested
    calc
      twentyOneGreedyDefect N + 1 =
          twentyOneGreedyDefect (2 * d - 1) + 1 := by rw [hNform]
      _ ≤ 2 * twentyOneDefectHeight d := hbound
      _ = 2 * twentyOneDefectHeight ((N + 2) / 2) := by rw [hmid]

/-- The proved finite seed and quarter-phase lock turn the sharper causal
midpoint service directly into the record-only producer. -/
theorem twentyOneDefectRecordMidpointBound_of_causalMidpointService
    (hseed : TwentyOneDefectInitialRecordMidpointBound)
    (hphase : TwentyOneDefectQuarterPhaseRecordLock)
    (hservice : TwentyOneDefectCausalMidpointService) :
    TwentyOneDefectRecordMidpointBound := by
  intro N hrecord
  by_cases hN : N ≤ 19
  · exact hseed N hN hrecord
  · have hlate : 19 < N := by omega
    obtain ⟨k, hk⟩ := hphase N hlate hrecord
    let d := 2 * k
    have hd : 0 < d := by
      dsimp [d]
      omega
    have hd7 : 7 ≤ d := by
      dsimp [d]
      omega
    have heven : Even d := ⟨k, by
      dsimp [d]
      omega⟩
    have hNform : N = 2 * d - 1 := by
      dsimp [d]
      omega
    have hmid : (N + 2) / 2 = d := by
      dsimp [d]
      omega
    have hrecord' :
        twentyOneDefectHeight (2 * d - 1) <
          twentyOneGreedyDefect (2 * d - 1) + 1 := by
      simpa only [← hNform] using hrecord
    have hcausal := hservice d hd heven hrecord'
    have hbound :=
      twentyOneRecordMidpointBound_of_causalMidpoint_at hd7 hrecord' hcausal
    calc
      twentyOneGreedyDefect N + 1 =
          twentyOneGreedyDefect (2 * d - 1) + 1 := by rw [hNform]
      _ ≤ 2 * twentyOneDefectHeight d := hbound
      _ = 2 * twentyOneDefectHeight ((N + 2) / 2) := by rw [hmid]

/-- The record-only inequality controls the height at every horizon.  The
induction spends the producer only when `Q_N+1` is strictly above the old
height; otherwise monotonicity transports the preceding midpoint bound. -/
theorem twentyOneDefectHeight_le_two_mul_midpoint
    (hrecord : TwentyOneDefectRecordMidpointBound) (N : ℕ) :
    twentyOneDefectHeight N ≤
      2 * twentyOneDefectHeight ((N + 1) / 2) := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [twentyOneDefectHeight_succ]
      apply max_le
      · calc
          twentyOneDefectHeight N ≤
              2 * twentyOneDefectHeight ((N + 1) / 2) := ih
          _ ≤ 2 * twentyOneDefectHeight ((N + 2) / 2) := by
            apply Nat.mul_le_mul_left
            apply twentyOneDefectHeight_monotone
            omega
      · by_cases hnew :
          twentyOneDefectHeight N < twentyOneGreedyDefect N + 1
        · exact hrecord N hnew
        · have hold :
              twentyOneGreedyDefect N + 1 ≤ twentyOneDefectHeight N := by
            omega
          calc
            twentyOneGreedyDefect N + 1 ≤ twentyOneDefectHeight N := hold
            _ ≤ 2 * twentyOneDefectHeight ((N + 1) / 2) := ih
            _ ≤ 2 * twentyOneDefectHeight ((N + 2) / 2) := by
              apply Nat.mul_le_mul_left
              apply twentyOneDefectHeight_monotone
              omega

/-- The record-midpoint producer implies the original all-pairs doubling
height producer. -/
theorem twentyOneDefectDoublingHeightBound_of_recordMidpointBound
    (hrecord : TwentyOneDefectRecordMidpointBound) :
    TwentyOneDefectDoublingHeightBound := by
  intro d
  have h := twentyOneDefectHeight_le_two_mul_midpoint hrecord (2 * d)
  have hdiv : (2 * d + 1) / 2 = d := by omega
  simpa only [hdiv] using h

/-- Conversely, the doubling-height producer controls every new plateau at
its ceiling midpoint.  Thus the million-pair-looking statement is exactly a
one-row obligation at each strict defect record. -/
theorem twentyOneDefectRecordMidpointBound_of_doublingHeightBound
    (hdouble : TwentyOneDefectDoublingHeightBound) :
    TwentyOneDefectRecordMidpointBound := by
  intro N hnew
  let d := (N + 2) / 2
  have hstart : N + 1 ≤ 2 * d := by
    dsimp [d]
    omega
  have hplateau :
      twentyOneDefectHeight (N + 1) = twentyOneGreedyDefect N + 1 := by
    rw [twentyOneDefectHeight_succ, max_eq_right]
    exact hnew.le
  calc
    twentyOneGreedyDefect N + 1 = twentyOneDefectHeight (N + 1) :=
      hplateau.symm
    _ ≤ twentyOneDefectHeight (2 * d) :=
      twentyOneDefectHeight_monotone hstart
    _ ≤ 2 * twentyOneDefectHeight d := hdouble d

theorem twentyOneDefectDoublingHeightBound_iff_recordMidpointBound :
    TwentyOneDefectDoublingHeightBound ↔
      TwentyOneDefectRecordMidpointBound :=
  ⟨twentyOneDefectRecordMidpointBound_of_doublingHeightBound,
    twentyOneDefectDoublingHeightBound_of_recordMidpointBound⟩

/-- Iteration of the doubling-height producer along dyadic ranks. -/
theorem twentyOneDefectHeight_pow_two_le
    (hdouble : TwentyOneDefectDoublingHeightBound) (k : ℕ) :
    twentyOneDefectHeight (2 ^ k) ≤
      2 ^ k * twentyOneDefectHeight 1 := by
  induction k with
  | zero => exact le_rfl
  | succ k ih =>
      calc
        twentyOneDefectHeight (2 ^ (k + 1)) =
            twentyOneDefectHeight (2 * 2 ^ k) := by
              congr 1
              rw [pow_succ]
              omega
        _ ≤ 2 * twentyOneDefectHeight (2 ^ k) := hdouble (2 ^ k)
        _ ≤ 2 * (2 ^ k * twentyOneDefectHeight 1) :=
          Nat.mul_le_mul_left 2 ih
        _ = 2 ^ (k + 1) * twentyOneDefectHeight 1 := by
          simp [pow_succ, Nat.mul_comm, Nat.mul_left_comm]

/-- The doubling-height inequality already gives a global linear envelope.
The harmless factor `2` comes from rounding `N` up to the next power of two.
-/
theorem twentyOneDefectHeight_le_linear
    (hdouble : TwentyOneDefectDoublingHeightBound) (N : ℕ) :
    twentyOneDefectHeight N ≤
      2 * (N + 1) * twentyOneDefectHeight 1 := by
  let k := (Nat.log 2 N).succ
  have hNpow : N ≤ 2 ^ k := by
    exact (Nat.lt_pow_succ_log_self (by omega : 1 < 2) N).le
  calc
    twentyOneDefectHeight N ≤ twentyOneDefectHeight (2 ^ k) :=
      twentyOneDefectHeight_monotone hNpow
    _ ≤ 2 ^ k * twentyOneDefectHeight 1 :=
      twentyOneDefectHeight_pow_two_le hdouble k
    _ ≤ 2 * (N + 1) * twentyOneDefectHeight 1 := by
      apply Nat.mul_le_mul_right (twentyOneDefectHeight 1)
      dsimp [k]
      rw [pow_succ]
      simpa [Nat.mul_comm] using
        Nat.mul_le_mul_left 2 (Nat.pow_log_le_add_one 2 N)

/-- A convenient affine defect envelope consumed by the asymptotic step. -/
theorem twentyOneGreedyDefect_add_one_le_linear
    (hdouble : TwentyOneDefectDoublingHeightBound) (N : ℕ) :
    twentyOneGreedyDefect N + 1 ≤
      4 * twentyOneDefectHeight 1 * (N + 1) := by
  calc
    twentyOneGreedyDefect N + 1 ≤ twentyOneDefectHeight (N + 1) :=
      twentyOneGreedyDefect_add_one_le_height_succ N
    _ ≤ 2 * ((N + 1) + 1) * twentyOneDefectHeight 1 :=
      twentyOneDefectHeight_le_linear hdouble (N + 1)
    _ ≤ 4 * twentyOneDefectHeight 1 * (N + 1) := by
      have h : N + 2 ≤ 2 * (N + 1) := by omega
      calc
        2 * ((N + 1) + 1) * twentyOneDefectHeight 1 =
            (N + 2) * (2 * twentyOneDefectHeight 1) := by ring
        _ ≤ (2 * (N + 1)) * (2 * twentyOneDefectHeight 1) :=
          Nat.mul_le_mul_right (2 * twentyOneDefectHeight 1) h
        _ = 4 * twentyOneDefectHeight 1 * (N + 1) := by ring

/-- The running-maximum producer forces the exact subexponential defect
condition already known to be equivalent to membership at `1/21`. -/
theorem twentyOneGreedyDefectSubexponential_of_doublingHeightBound
    (hdouble : TwentyOneDefectDoublingHeightBound) :
    TwentyOneGreedyDefectSubexponential := by
  have hNatRatio :
      Tendsto (fun N : ℕ => (N : ℝ) / (2 : ℝ) ^ N)
        atTop (nhds 0) :=
    by
      simpa only [pow_one] using
        (tendsto_pow_const_div_const_pow_of_one_lt 1
          (r := (2 : ℝ)) (by norm_num))
  have hOneRatio :
      Tendsto (fun N : ℕ => (1 : ℝ) / (2 : ℝ) ^ N)
        atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop
      (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2))
  have hLinearRatio :
      Tendsto (fun N : ℕ => ((N : ℝ) + 1) / (2 : ℝ) ^ N)
        atTop (nhds 0) := by
    convert hNatRatio.add hOneRatio using 1
    · funext N
      ring
    · simp
  let C : ℝ := 4 * twentyOneDefectHeight 1
  have hScaledRatio :
      Tendsto (fun N : ℕ => C * ((N : ℝ) + 1) / (2 : ℝ) ^ N)
        atTop (nhds 0) := by
    have hC : Tendsto (fun _ : ℕ => C) atTop (nhds C) :=
      tendsto_const_nhds
    have h := hC.mul hLinearRatio
    convert h using 1
    · funext N
      ring
    · simp
  intro δ hδ
  obtain ⟨K, hK⟩ := (Metric.tendsto_atTop.1 hScaledRatio) δ hδ
  refine ⟨K, fun N hKN => ?_⟩
  have hdist := hK N hKN
  have hscaled_nonneg :
      0 ≤ C * ((N : ℝ) + 1) / (2 : ℝ) ^ N := by
    dsimp [C]
    positivity
  have hratio :
      C * ((N : ℝ) + 1) / (2 : ℝ) ^ N < δ := by
    rw [Real.dist_eq, sub_zero, abs_of_nonneg hscaled_nonneg] at hdist
    exact hdist
  have hboundNat := twentyOneGreedyDefect_add_one_le_linear hdouble N
  have hboundReal :
      (twentyOneGreedyDefect N : ℝ) + 1 ≤ C * ((N : ℝ) + 1) := by
    dsimp [C]
    exact_mod_cast hboundNat
  have hpow : (0 : ℝ) < (2 : ℝ) ^ N := by positivity
  have hratio' :
      ((twentyOneGreedyDefect N : ℝ) + 1) / (2 : ℝ) ^ N < δ :=
    lt_of_le_of_lt (div_le_div_of_nonneg_right hboundReal hpow.le) hratio
  simpa [mul_comm] using (div_lt_iff₀ hpow).1 hratio'

/-- Checked endpoint: the single doubling-height inequality constructs the
rational target `1/21` in the Mersenne achievement set. -/
theorem one_div_twenty_one_mem_of_doublingHeightBound
    (hdouble : TwentyOneDefectDoublingHeightBound) :
    (1 / 21 : ℝ) ∈ mersenneAchievementSet :=
  one_div_twenty_one_mem_mersenneAchievementSet_of_defectSubexponential
    (twentyOneGreedyDefectSubexponential_of_doublingHeightBound hdouble)

/-- The represented support is necessarily infinite: a finite support cannot
contain rank `1` (that single term already has value one), and the audited
finite-denominator theorem excludes every finite support on ranks at least
two. -/
theorem exists_infinite_one_div_twenty_one_counterexample_of_doublingHeightBound
    (hdouble : TwentyOneDefectDoublingHeightBound) :
    ∃ A : Set ℕ, A.Infinite ∧
      erdosSupportSeries 2 A = (1 : ℝ) / 21 := by
  classical
  rcases one_div_twenty_one_mem_of_doublingHeightBound hdouble with
    ⟨A, hA0, hvalue⟩
  have hseries : erdosSupportSeries 2 A = (1 : ℝ) / 21 := by
    rw [← positiveMersenneSupportValue_eq_erdosSupportSeries]
    exact hvalue.symm
  refine ⟨A, ?_, hseries⟩
  intro hfinite
  let F : Finset ℕ := hfinite.toFinset
  have hFA : (↑F : Set ℕ) = A := by
    dsimp [F]
    exact hfinite.coe_toFinset
  have hcast : ((finiteErdosSum F 2 : ℚ) : ℝ) = (1 : ℝ) / 21 := by
    rw [← erdosSupportSeries_finset_eq_cast_finiteErdosSum F, hFA]
    exact hseries
  have hrat : finiteErdosSum F 2 = (1 : ℚ) / 21 := by
    apply Rat.cast_injective (α := ℝ)
    simpa using hcast
  have hFzero : 0 ∉ F := by
    intro hzero
    apply hA0
    rw [← hFA]
    simpa using hzero
  have hFone : 1 ∉ F := by
    intro hone
    have hle :
        (1 / (((2 : ℚ) ^ 1) - 1)) ≤ finiteErdosSum F 2 := by
      unfold finiteErdosSum
      exact Finset.single_le_sum
        (f := fun n : ℕ => 1 / (((2 : ℚ) ^ n) - 1))
        (fun n _ => by
          apply div_nonneg (by norm_num)
          exact sub_nonneg.mpr (one_le_pow₀ (by norm_num : (1 : ℚ) ≤ 2)))
        hone
    rw [hrat] at hle
    norm_num at hle
  have hFmin : ∀ n ∈ F, 2 ≤ n := by
    intro n hn
    have hn0 : n ≠ 0 := fun h => hFzero (h ▸ hn)
    have hn1 : n ≠ 1 := fun h => hFone (h ▸ hn)
    omega
  exact finiteErdosSum_ne_one_div_twenty_one F hFmin hrat

/-- Conditional final endpoint: the running-maximum inequality refutes the
universal irrationality assertion in Erdős #257. -/
theorem not_universal_of_twentyOneDefectDoublingHeightBound
    (hdouble : TwentyOneDefectDoublingHeightBound) :
    ¬ UniversalMersenneSubseriesIrrationality := by
  obtain ⟨A, hA, hseries⟩ :=
    exists_infinite_one_div_twenty_one_counterexample_of_doublingHeightBound
      hdouble
  intro huniversal
  have hirr := huniversal A hA
  rw [hseries] at hirr
  have hcast : (1 / 21 : ℝ) = ((1 / 21 : ℚ) : ℝ) := by norm_num
  rw [hcast] at hirr
  exact (Rat.not_irrational (1 / 21 : ℚ)) hirr

/-- Record-only final endpoint.  It is enough to service each strict defect
record at the ceiling midpoint of its plateau start. -/
theorem not_universal_of_twentyOneDefectRecordMidpointBound
    (hrecord : TwentyOneDefectRecordMidpointBound) :
    ¬ UniversalMersenneSubseriesIrrationality :=
  not_universal_of_twentyOneDefectDoublingHeightBound
    (twentyOneDefectDoublingHeightBound_of_recordMidpointBound hrecord)

/-- Service-law final endpoint.  After the finite seed, the two genuine
all-depth inputs are exactly nested-height compensation and the quarter-phase
record lock. -/
theorem not_universal_of_twentyOneNestedHeightService
    (hphase : TwentyOneDefectQuarterPhaseRecordLock)
    (hservice : TwentyOneDefectNestedHeightService) :
    ¬ UniversalMersenneSubseriesIrrationality :=
  not_universal_of_twentyOneDefectRecordMidpointBound
    (twentyOneDefectRecordMidpointBound_of_nestedHeightService
      twentyOneDefectInitialRecordMidpointBound hphase hservice)

/-- Sharper causal-service endpoint.  A proof of the audited `H(d)+2` law,
together with the quarter-phase record lock, disproves universal
irrationality. -/
theorem not_universal_of_twentyOneCausalMidpointService
    (hphase : TwentyOneDefectQuarterPhaseRecordLock)
    (hservice : TwentyOneDefectCausalMidpointService) :
    ¬ UniversalMersenneSubseriesIrrationality :=
  not_universal_of_twentyOneDefectRecordMidpointBound
    (twentyOneDefectRecordMidpointBound_of_causalMidpointService
      twentyOneDefectInitialRecordMidpointBound hphase hservice)

#print axioms twentyOneEulerMidpointService_identity
#print axioms twentyOneRecordMidpointBound_of_nestedHeight_at
#print axioms twentyOneDefectInitialRecordMidpointBound
#print axioms twentyOneDefectRecordMidpointBound_of_nestedHeightService
#print axioms twentyOneRecordMidpointBound_of_causalMidpoint_at
#print axioms twentyOneDefectRecordMidpointBound_of_causalMidpointService
#print axioms twentyOneDefectDoublingHeightBound_iff_recordMidpointBound
#print axioms one_div_twenty_one_mem_of_doublingHeightBound
#print axioms not_universal_of_twentyOneDefectDoublingHeightBound
#print axioms not_universal_of_twentyOneDefectRecordMidpointBound
#print axioms not_universal_of_twentyOneNestedHeightService
#print axioms not_universal_of_twentyOneCausalMidpointService

end ErdosProblems.Erdos257
