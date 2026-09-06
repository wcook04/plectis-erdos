import Erdos249257.HalfResetSqrtEscapeMiddleDischarge

/-!
# Finite base band for the reset margin producers

Exact seam-greedy remainders for rows 9-17, computed inside Lean by
`native_decide`, together with the consumption-ready base instances of
the ceiling and floor margin producers on rows 10-15 and 13.  These are
the finite base cases a future descent lemma quantifies away; every
statement here is a computation, not an orbit assumption.
-/

namespace Erdos249257

open HalfCylinderIntegerGreedy

theorem seamRemainderNine : seamIntegerGreedyRemainder 9 = 541 := by native_decide
theorem seamRemainderTen : seamIntegerGreedyRemainder 10 = 1135 := by native_decide
theorem seamRemainderEleven : seamIntegerGreedyRemainder 11 = 2485 := by native_decide
theorem seamRemainderTwelve : seamIntegerGreedyRemainder 12 = 5836 := by native_decide
theorem seamRemainderThirteen : seamIntegerGreedyRemainder 13 = 15147 := by native_decide
theorem seamRemainderFourteen : seamIntegerGreedyRemainder 14 = 392 := by native_decide
theorem seamRemainderFifteen : seamIntegerGreedyRemainder 15 = 34333 := by native_decide
theorem seamRemainderSixteen : seamIntegerGreedyRemainder 16 = 71791 := by native_decide
theorem seamRemainderSeventeen : seamIntegerGreedyRemainder 17 = 156085 := by native_decide

/-- Ceiling producer base instances: `4 * R_(d+1) >= threshold` on
rows `d = 10..15`. -/
theorem ceilingBaseTen : (3 * 2 ^ ((10 + 6) / 2) + 2 * (10 - 1) : ℕ) ≤
    4 * seamIntegerGreedyRemainder 11 := by native_decide
theorem ceilingBaseEleven : (3 * 2 ^ ((11 + 6) / 2) + 2 * (11 - 1) : ℕ) ≤
    4 * seamIntegerGreedyRemainder 12 := by native_decide
theorem ceilingBaseTwelve : (3 * 2 ^ ((12 + 6) / 2) + 2 * (12 - 1) : ℕ) ≤
    4 * seamIntegerGreedyRemainder 13 := by native_decide
theorem ceilingBaseThirteen : (3 * 2 ^ ((13 + 6) / 2) + 2 * (13 - 1) : ℕ) ≤
    4 * seamIntegerGreedyRemainder 14 := by native_decide
theorem ceilingBaseFourteen : (3 * 2 ^ ((14 + 6) / 2) + 2 * (14 - 1) : ℕ) ≤
    4 * seamIntegerGreedyRemainder 15 := by native_decide
theorem ceilingBaseFifteen : (3 * 2 ^ ((15 + 6) / 2) + 2 * (15 - 1) : ℕ) ≤
    4 * seamIntegerGreedyRemainder 16 := by native_decide

/-- Floor producer binding base instance at the numerically tightest
upper reset: `E_13 >= 3 * 2 ^ 9`. -/
theorem floorBaseThirteen :
    (3 * 2 ^ ((13 + 5) / 2) : ℕ) ≤
      2 ^ (13 + 1) - seamIntegerGreedyRemainder 14 := by native_decide


/-- Full-threshold take-margin base instances on rows `t = 10, 11, 12,
14, 15` (row `13` is an upper-reset landing, not a take, so its
full-threshold instance is not required - the reset path consumes the
ceiling instances above). -/
theorem takeMarginBaseTen : (3 * 2 ^ ((10 + 6) / 2) + 2 * (10 - 1) : ℕ) ≤
    seamIntegerGreedyRemainder 11 := by native_decide
theorem takeMarginBaseEleven : (3 * 2 ^ ((11 + 6) / 2) + 2 * (11 - 1) : ℕ) ≤
    seamIntegerGreedyRemainder 12 := by native_decide
theorem takeMarginBaseTwelve : (3 * 2 ^ ((12 + 6) / 2) + 2 * (12 - 1) : ℕ) ≤
    seamIntegerGreedyRemainder 13 := by native_decide
theorem takeMarginBaseFourteen : (3 * 2 ^ ((14 + 6) / 2) + 2 * (14 - 1) : ℕ) ≤
    seamIntegerGreedyRemainder 15 := by native_decide
theorem takeMarginBaseFifteen : (3 * 2 ^ ((15 + 6) / 2) + 2 * (15 - 1) : ℕ) ≤
    seamIntegerGreedyRemainder 16 := by native_decide

#print axioms takeMarginBaseTen
#print axioms ceilingBaseThirteen
#print axioms floorBaseThirteen

end Erdos249257
