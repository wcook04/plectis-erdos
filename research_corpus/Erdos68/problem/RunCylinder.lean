import ErdosProblems.Erdos68.GapScalarNormalForm
import ErdosProblems.Erdos68.PrimeZeroBranch

/-!
# Erdős #68: consecutive failure cylinders

The tail-free predecessor-gap certificate fails at `m` precisely when the
gap lies in an interval of radius about `1 / m`.  Two consecutive failures
are much more rigid: the exact affine recurrence forces the carry at the
first step to be `0` or `1`, and the initial gap lies in one of two intervals
of radius about `1 / m^2`.

This file kernel-checks both the pointwise composition to Erdős #68 and the
two-cylinder classification.  It makes no metric-to-pointwise inference: the
remaining problem is still to exclude these cylinders for the distinguished
factorial-gap orbit cofinally.
-/

namespace ErdosProblems.Erdos68

/-- Radius of the tail-free predecessor-gap failure interval. -/
noncomputable def predecessorFailureRadius (m : ℕ) : ℝ :=
  (1 + 1 / ((m.factorial : ℝ) - 1) + 2 / (m : ℝ)) / (m : ℝ)

/-- Failure of the finite predecessor-gap threshold at one index. -/
def predecessorGapThresholdFailure (m : ℕ) : Prop :=
  (m : ℝ) * factorialGapPredecessorGap m <
    1 + 1 / ((m.factorial : ℝ) - 1) + 2 / (m : ℝ)

theorem predecessorGapThresholdFailure_iff_gap_lt_radius
    {m : ℕ} (hm : 1 ≤ m) :
    predecessorGapThresholdFailure m ↔
      factorialGapPredecessorGap m < predecessorFailureRadius m := by
  unfold predecessorGapThresholdFailure predecessorFailureRadius
  have hmPos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  constructor
  · intro h
    apply (lt_div_iff₀ hmPos).2
    simpa [mul_comm] using h
  · intro h
    have h' := (lt_div_iff₀ hmPos).1 h
    simpa [mul_comm] using h'

/-- The next failure radius is strictly smaller than `2 / m`. -/
theorem predecessorFailureRadius_succ_lt_two_div
    {m : ℕ} (hm : 3 ≤ m) :
    predecessorFailureRadius (m + 1) < 2 / (m : ℝ) := by
  have hmPos : (0 : ℝ) < (m : ℝ) := by positivity
  have hm1Pos : (0 : ℝ) < ((m + 1 : ℕ) : ℝ) := by positivity
  have hfacNat : 2 < (m + 1).factorial := by
    have hsix : 6 ≤ (m + 1).factorial := by
      calc
        6 = (3 : ℕ).factorial := by norm_num
        _ ≤ (m + 1).factorial := Nat.factorial_le (by omega)
    omega
  have hfacReal : (2 : ℝ) < ((m + 1).factorial : ℝ) := by
    exact_mod_cast hfacNat
  have hdenOne : (1 : ℝ) < ((m + 1).factorial : ℝ) - 1 := by linarith
  have hdenPos : (0 : ℝ) < ((m + 1).factorial : ℝ) - 1 := by linarith
  have hepsLt :
      1 / (((m + 1).factorial : ℝ) - 1) < (1 : ℝ) :=
    (div_lt_one hdenPos).2 hdenOne
  unfold predecessorFailureRadius
  rw [div_lt_iff₀ hm1Pos]
  push_cast
  have hmR : (3 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hratio : 2 / ((m : ℝ) + 1) < 2 / (m : ℝ) := by
    rw [div_lt_div_iff₀ (by positivity) hmPos]
    nlinarith
  have hid : 2 / (m : ℝ) * ((m : ℝ) + 1) = 2 + 2 / (m : ℝ) := by
    field_simp
  rw [hid]
  linarith

/-- A pointwise no-repeat theorem would already settle Erdős #68.  This is
the exact composition used by the metric run-cylinder argument; the missing
input is deliberately a statement about the distinguished orbit. -/
theorem irrational_factorialGapSeries_of_eventually_no_consecutive_failures
    (hpair : ∃ M : ℕ, ∀ m : ℕ, M ≤ m →
      ¬(predecessorGapThresholdFailure m ∧
        predecessorGapThresholdFailure (m + 1))) :
    Irrational _root_.Erdos68.factorialGapSeries := by
  apply irrational_factorialGapSeries_of_cofinal_predecessorGap_threshold
  intro B
  obtain ⟨M, hM⟩ := hpair
  let m := max (max M (B + 1)) 3
  have hmM : M ≤ m := le_trans (le_max_left M (B + 1)) (le_max_left _ 3)
  have hm3 : 3 ≤ m := le_max_right _ _
  have hmB : B < m := by
    have : B + 1 ≤ m :=
      le_trans (le_max_right M (B + 1)) (le_max_left _ 3)
    omega
  have hnot := hM m hmM
  by_cases hfail : predecessorGapThresholdFailure m
  · have hnext : ¬predecessorGapThresholdFailure (m + 1) := by
      intro hnextFail
      exact hnot ⟨hfail, hnextFail⟩
    refine ⟨m + 1, by omega, by omega, ?_⟩
    unfold predecessorGapThresholdFailure at hnext
    exact le_of_not_gt hnext
  · refine ⟨m, hm3, hmB, ?_⟩
    unfold predecessorGapThresholdFailure at hfail
    exact le_of_not_gt hfail

/-- **Exact two-cylinder classification for the actual orbit.**  Two
consecutive threshold failures force the first carry to be `0` or `1`.
After subtracting the tiny factorial correction, the scaled gap lies in the
corresponding pullback of the next failure interval. -/
theorem consecutive_predecessorGap_failures_iff_two_cylinders
    {m : ℕ} (hm : 3 ≤ m) :
    predecessorGapThresholdFailure m ∧
        predecessorGapThresholdFailure (m + 1) ↔
      (factorialGapStepCarry m = 0 ∧
        0 < (m : ℝ) * factorialGapPredecessorGap m -
            1 / ((m.factorial : ℝ) - 1) ∧
        (m : ℝ) * factorialGapPredecessorGap m -
            1 / ((m.factorial : ℝ) - 1) <
              predecessorFailureRadius (m + 1)) ∨
      (factorialGapStepCarry m = 1 ∧
        1 < (m : ℝ) * factorialGapPredecessorGap m -
            1 / ((m.factorial : ℝ) - 1) ∧
        (m : ℝ) * factorialGapPredecessorGap m -
            1 / ((m.factorial : ℝ) - 1) <
              1 + predecessorFailureRadius (m + 1)) := by
  let z : ℝ := (m : ℝ) * factorialGapPredecessorGap m -
    1 / ((m.factorial : ℝ) - 1)
  have hrec := predGap_succ_eq m (by omega)
  have hgapPos := (factorialGapPredecessorGap_pos_le_one m).1
  have hnextPos := (factorialGapPredecessorGap_pos_le_one (m + 1)).1
  have hnextOne := (factorialGapPredecessorGap_pos_le_one (m + 1)).2
  have hradius := predecessorFailureRadius_succ_lt_two_div hm
  have hmPos : (0 : ℝ) < (m : ℝ) := by positivity
  have hmR : (3 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hbounds := factorialGapStepCarry_bounds hm
  have hzEq :
      z = factorialGapPredecessorGap (m + 1) +
        (factorialGapStepCarry m : ℝ) := by
    dsimp [z]
    linarith
  constructor
  · rintro ⟨hfail, hnextFail⟩
    have hzUpper : z < 1 + 2 / (m : ℝ) := by
      unfold predecessorGapThresholdFailure at hfail
      dsimp [z]
      linarith
    have hzTwo : z < 2 := by
      have hinv : 1 / (m : ℝ) ≤ 1 / 3 :=
        one_div_le_one_div_of_le (by norm_num) hmR
      have htwo : 2 / (m : ℝ) ≤ 2 / 3 := by
        calc
          2 / (m : ℝ) = 2 * (1 / (m : ℝ)) := by ring
          _ ≤ 2 * (1 / 3) := by gcongr
          _ = 2 / 3 := by ring
      linarith
    have hnextRadius :
        factorialGapPredecessorGap (m + 1) <
          predecessorFailureRadius (m + 1) :=
      (predecessorGapThresholdFailure_iff_gap_lt_radius (by omega)).mp
        hnextFail
    have hzPos : 0 < z := by
      by_contra hnpos
      have hzNonpos : z ≤ 0 := le_of_not_gt hnpos
      have hbLe : factorialGapStepCarry m ≤ -1 := by
        have hbLtR : (factorialGapStepCarry m : ℝ) < 0 := by
          rw [hzEq] at hzNonpos
          linarith
        have hbLt : factorialGapStepCarry m < 0 := by exact_mod_cast hbLtR
        omega
      have hbNeg : factorialGapStepCarry m = -1 := by omega
      have hfacNat : 2 < m.factorial := by
        have hsix : 6 ≤ m.factorial := by
          calc 6 = (3 : ℕ).factorial := by norm_num
               _ ≤ m.factorial := Nat.factorial_le hm
        omega
      have hfacReal : (2 : ℝ) < (m.factorial : ℝ) := by exact_mod_cast hfacNat
      have hdenOne : (1 : ℝ) < (m.factorial : ℝ) - 1 := by linarith
      have hdenPos : (0 : ℝ) < (m.factorial : ℝ) - 1 := by linarith
      have hepsLt : 1 / ((m.factorial : ℝ) - 1) < (1 : ℝ) :=
        (div_lt_one hdenPos).2 hdenOne
      have hzLower : -(1 / ((m.factorial : ℝ) - 1)) < z := by
        have hmulPos : 0 < (m : ℝ) * factorialGapPredecessorGap m :=
          mul_pos hmPos hgapPos
        dsimp [z]
        simpa only [zero_sub] using
          (sub_lt_sub_right hmulPos (1 / ((m.factorial : ℝ) - 1)))
      rw [hbNeg] at hzEq
      push_cast at hzEq
      have hfourFifths : (4 / 5 : ℝ) ≤
          1 - 1 / ((m.factorial : ℝ) - 1) := by
        have hfacSixNat : 6 ≤ m.factorial := by
          calc 6 = (3 : ℕ).factorial := by norm_num
               _ ≤ m.factorial := Nat.factorial_le hm
        have hfacSix : (6 : ℝ) ≤ (m.factorial : ℝ) := by
          exact_mod_cast hfacSixNat
        have hdenFive : (5 : ℝ) ≤ (m.factorial : ℝ) - 1 := by linarith
        have hinv : 1 / ((m.factorial : ℝ) - 1) ≤ 1 / 5 := by
          exact one_div_le_one_div_of_le (by norm_num) hdenFive
        linarith
      have hinv : 1 / (m : ℝ) ≤ 1 / 3 :=
        one_div_le_one_div_of_le (by norm_num) hmR
      have htwoThirds : 2 / (m : ℝ) ≤ (2 / 3 : ℝ) := by
        calc
          2 / (m : ℝ) = 2 * (1 / (m : ℝ)) := by ring
          _ ≤ 2 * (1 / 3) := by gcongr
          _ = 2 / 3 := by ring
      have hnextLower :
          1 - 1 / ((m.factorial : ℝ) - 1) <
            factorialGapPredecessorGap (m + 1) := by
        linarith [hzLower, hzEq]
      have hnextFourFifths :
          (4 / 5 : ℝ) < factorialGapPredecessorGap (m + 1) :=
        lt_of_le_of_lt hfourFifths hnextLower
      have hnextTwoThirds :
          factorialGapPredecessorGap (m + 1) < (2 / 3 : ℝ) :=
        lt_of_lt_of_le hnextRadius (hradius.le.trans htwoThirds)
      norm_num at hnextFourFifths hnextTwoThirds
      linarith
    have hbLowerR : (0 : ℝ) ≤ (factorialGapStepCarry m : ℝ) := by
      rw [hzEq] at hzPos
      have hgtR : (-1 : ℝ) < (factorialGapStepCarry m : ℝ) := by
        linarith [hnextOne]
      have hgt : (-1 : ℤ) < factorialGapStepCarry m := by exact_mod_cast hgtR
      exact_mod_cast (show (0 : ℤ) ≤ factorialGapStepCarry m by omega)
    have hbUpperR : (factorialGapStepCarry m : ℝ) < 2 := by
      rw [hzEq] at hzTwo
      linarith
    have hbCases : factorialGapStepCarry m = 0 ∨
        factorialGapStepCarry m = 1 := by
      have hb0 : (0 : ℤ) ≤ factorialGapStepCarry m := by exact_mod_cast hbLowerR
      have hb2 : factorialGapStepCarry m < (2 : ℤ) := by exact_mod_cast hbUpperR
      omega
    rcases hbCases with hb0 | hb1
    · left
      refine ⟨hb0, hzPos, ?_⟩
      rw [hb0] at hzEq
      push_cast at hzEq
      linarith
    · right
      refine ⟨hb1, ?_, ?_⟩
      · rw [hb1] at hzEq
        push_cast at hzEq
        linarith
      · rw [hb1] at hzEq
        push_cast at hzEq
        linarith
  · intro hcyl
    have hnextRadiusPos : 0 < predecessorFailureRadius (m + 1) := by
      unfold predecessorFailureRadius
      have hfac : (1 : ℝ) < (m + 1).factorial := by
        exact_mod_cast Nat.one_lt_factorial.mpr (show 2 ≤ m + 1 by omega)
      have hden : (0 : ℝ) < ((m + 1).factorial : ℝ) - 1 := by linarith
      have hm1Pos : (0 : ℝ) < ((m + 1 : ℕ) : ℝ) := by positivity
      positivity
    rcases hcyl with hzero | hone
    · rcases hzero with ⟨hb, hzPos, hzUpper⟩
      change 0 < z at hzPos
      change z < predecessorFailureRadius (m + 1) at hzUpper
      constructor
      · unfold predecessorGapThresholdFailure
        dsimp [z] at hzUpper ⊢
        linarith
      · rw [predecessorGapThresholdFailure_iff_gap_lt_radius (by omega)]
        rw [hb] at hzEq
        push_cast at hzEq
        linarith
    · rcases hone with ⟨hb, hzOne, hzUpper⟩
      change 1 < z at hzOne
      change z < 1 + predecessorFailureRadius (m + 1) at hzUpper
      constructor
      · unfold predecessorGapThresholdFailure
        dsimp [z] at hzUpper ⊢
        linarith
      · rw [predecessorGapThresholdFailure_iff_gap_lt_radius (by omega)]
        rw [hb] at hzEq
        push_cast at hzEq
        linarith

#print axioms consecutive_predecessorGap_failures_iff_two_cylinders
#print axioms irrational_factorialGapSeries_of_eventually_no_consecutive_failures

end ErdosProblems.Erdos68
