import ErdosProblems.Erdos257.TwentyOneRunningMaximumProducer

/-!
# Erdős #257: selected-divisor height reduction for the denominator-21 defect

The running defect height `H(d)` has a free lower comparison with the largest
selected-divisor load through `d`.  It comes directly from nonnegativity of
the next defect in the exact recurrence

`Q_(N+1) = 2 Q_N + t_N - f(N+1)`.

Consequently the doubling producer `H(2d) ≤ 2H(d)` follows from one upper
comparison: the defect height before `2d` is at most one plus the largest
selected-divisor load through `d`.  This module formalizes that reduction;
the upper comparison remains the sole open producer here.
-/

namespace ErdosProblems.Erdos257

open Erdos257PeriodNoncollapse

/-- Largest selected-divisor coefficient in the positive rows through `d`.
The zero value at `d = 0` keeps the recurrence subtraction-free. -/
noncomputable def twentyOneSelectedDivisorHeight : ℕ → ℕ
  | 0 => 0
  | d + 1 =>
      max (twentyOneSelectedDivisorHeight d)
        (supportCoeff (greedyMersenneSupport (1 / 21 : ℝ)) (d + 1))

@[simp] theorem twentyOneSelectedDivisorHeight_zero :
    twentyOneSelectedDivisorHeight 0 = 0 := rfl

@[simp] theorem twentyOneSelectedDivisorHeight_succ (d : ℕ) :
    twentyOneSelectedDivisorHeight (d + 1) =
      max (twentyOneSelectedDivisorHeight d)
        (supportCoeff (greedyMersenneSupport (1 / 21 : ℝ)) (d + 1)) := rfl

/-- Nonnegativity of the successor defect pays half of the divisor-load
comparison for free: `f(N+1) ≤ 2Q_N+1`. -/
theorem twentyOneSelectedDivisorLoad_le_two_defect_add_one (N : ℕ) :
    supportCoeff (greedyMersenneSupport (1 / 21 : ℝ)) (N + 1) ≤
      2 * twentyOneGreedyDefect N + 1 := by
  have hrec := twentyOneGreedyDefect_succ N
  have hbit := twentyOneFloorBit_le_one N
  have hnonneg : (0 : ℤ) ≤ (twentyOneGreedyDefect (N + 1) : ℤ) := by
    positivity
  have hload :
      (supportCoeff (greedyMersenneSupport (1 / 21 : ℝ)) (N + 1) : ℤ) ≤
        2 * (twentyOneGreedyDefect N : ℤ) + 1 := by
    omega
  exact_mod_cast hload

/-- **Free lower half of the divisor-height comparison.**  One plus the
largest selected-divisor load through `d` is at most twice the running
defect height before `d`. -/
theorem twentyOneSelectedDivisorHeight_add_one_le_two_defectHeight (d : ℕ) :
    twentyOneSelectedDivisorHeight d + 1 ≤ 2 * twentyOneDefectHeight d := by
  induction d with
  | zero => simp
  | succ d ih =>
      have hmono := twentyOneDefectHeight_le_succ d
      have hprevious :
          twentyOneSelectedDivisorHeight d + 1 ≤
            2 * twentyOneDefectHeight (d + 1) := by
        omega
      have hload := twentyOneSelectedDivisorLoad_le_two_defect_add_one d
      have hQ := twentyOneGreedyDefect_add_one_le_height_succ d
      have hcurrent :
          supportCoeff (greedyMersenneSupport (1 / 21 : ℝ)) (d + 1) + 1 ≤
            2 * twentyOneDefectHeight (d + 1) := by
        omega
      rw [twentyOneSelectedDivisorHeight_succ]
      omega

/-- The remaining selected-divisor half-range producer.  In maximum
notation this is exactly

`max_{N < 2d} Q_N ≤ max_{m ≤ d} supportCoeff(A,m)`.

Unlike the lower comparison above, this is an upper bound on the greedy
defect and is not proved by the recurrence alone. -/
def TwentyOneSelectedDivisorHalfRangeBound : Prop :=
  ∀ d : ℕ,
    twentyOneDefectHeight (2 * d) ≤ twentyOneSelectedDivisorHeight d + 1

/-- The selected-divisor half-range bound closes the original doubling
height producer with constant exactly two. -/
theorem twentyOneDefectDoublingHeightBound_of_selectedDivisorHalfRange
    (hselected : TwentyOneSelectedDivisorHalfRangeBound) :
    TwentyOneDefectDoublingHeightBound := by
  intro d
  exact (hselected d).trans
    (twentyOneSelectedDivisorHeight_add_one_le_two_defectHeight d)

/-- Final counterexample endpoint from the single selected-divisor upper
comparison. -/
theorem not_universal_of_twentyOneSelectedDivisorHalfRangeBound
    (hselected : TwentyOneSelectedDivisorHalfRangeBound) :
    ¬ UniversalMersenneSubseriesIrrationality :=
  not_universal_of_twentyOneDefectDoublingHeightBound
    (twentyOneDefectDoublingHeightBound_of_selectedDivisorHalfRange hselected)

#print axioms twentyOneSelectedDivisorLoad_le_two_defect_add_one
#print axioms twentyOneSelectedDivisorHeight_add_one_le_two_defectHeight
#print axioms twentyOneDefectDoublingHeightBound_of_selectedDivisorHalfRange
#print axioms not_universal_of_twentyOneSelectedDivisorHalfRangeBound

end ErdosProblems.Erdos257
