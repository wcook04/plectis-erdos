/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib
import ErdosProblems.Erdos1049.RationalBaseContour

/-!
# Source transport for the Erdős #1049 rational-base contour

The declarations below restate the Mathlib-only challenge vocabulary and
transport the exact source theorems of
`ErdosProblems.Erdos1049.RationalBaseContour` without strengthening their
hypotheses.  The redeclared constants unfold to the source constants, so each
transport is the source theorem itself.
-/

namespace Erdos249257.ExternalVerification1049RationalBaseContour

noncomputable def trigammaSeries (x : ℝ) : ℝ := ∑' k : ℕ, 1 / ((k : ℝ) + x) ^ 2

noncomputable def zudilinJTerm (u v : ℝ) : ℝ := trigammaSeries u - trigammaSeries v

noncomputable def zudilinJ : ℝ :=
  zudilinJTerm (1 / 14) (1 / 12) + zudilinJTerm (1 / 7) (1 / 6) +
    zudilinJTerm (3 / 14) (1 / 4) + zudilinJTerm (2 / 7) (1 / 3) +
    zudilinJTerm (5 / 14) (2 / 5) + zudilinJTerm (3 / 7) (7 / 15) +
    zudilinJTerm (1 / 2) (8 / 15) + zudilinJTerm (4 / 7) (3 / 5) +
    zudilinJTerm (9 / 14) (2 / 3) + zudilinJTerm (5 / 7) (11 / 15) +
    zudilinJTerm (11 / 14) (4 / 5) + zudilinJTerm (6 / 7) (13 / 15) +
    zudilinJTerm (13 / 14) (14 / 15)

noncomputable def zudilinC1 : ℝ := 1091 / 2

noncomputable def zudilinC0 : ℝ := 266 - 3 / Real.pi ^ 2 * (225 - zudilinJ)

noncomputable def zudilinContour : ℝ := zudilinC0 / zudilinC1

def ZudilinContourRegion (a b : ℕ) : Prop :=
  Real.log b / Real.log a < zudilinContour

theorem trigammaSeries_eq (x : ℝ) :
    trigammaSeries x = ErdosProblems.Erdos1049.trigammaSeries x := rfl

theorem zudilinJ_eq : zudilinJ = ErdosProblems.Erdos1049.zudilinJ := rfl

theorem zudilinC0_eq : zudilinC0 = ErdosProblems.Erdos1049.zudilinC0 := rfl

theorem zudilinContour_eq :
    zudilinContour = ErdosProblems.Erdos1049.zudilinContour := rfl

theorem zudilinContourRegion_iff (a b : ℕ) :
    ZudilinContourRegion a b ↔ ErdosProblems.Erdos1049.ZudilinContourRegion a b :=
  Iff.rfl

theorem eightyOne_twoHundredths_lt_zudilinContour :
    (81 : ℝ) / 200 < zudilinContour := by
  rw [zudilinContour_eq]
  exact ErdosProblems.Erdos1049.eightyOne_twoHundredths_lt_zudilinContour

theorem zudilinContour_lt_half : zudilinContour < 1 / 2 := by
  rw [zudilinContour_eq]
  exact ErdosProblems.Erdos1049.zudilinContour_lt_half

theorem threeHalves_outside_zudilinContourRegion :
    ¬ ZudilinContourRegion 3 2 := by
  rw [zudilinContourRegion_iff]
  exact ErdosProblems.Erdos1049.threeHalves_outside_zudilinContourRegion

theorem thirtyoneFour_power_mem_zudilinContourRegion (r : ℕ) (hr : 0 < r) :
    ZudilinContourRegion (31 ^ r) (4 ^ r) := by
  rw [zudilinContourRegion_iff]
  exact ErdosProblems.Erdos1049.thirtyoneFour_power_mem_zudilinContourRegion r hr

theorem zudilinJ_ge : (776 : ℝ) / 10 ≤ zudilinJ := by
  rw [zudilinJ_eq]
  exact ErdosProblems.Erdos1049.zudilinJ_ge

theorem zudilinC0_gt : (88371 : ℝ) / 400 < zudilinC0 := by
  rw [zudilinC0_eq]
  exact ErdosProblems.Erdos1049.zudilinC0_gt

end Erdos249257.ExternalVerification1049RationalBaseContour
