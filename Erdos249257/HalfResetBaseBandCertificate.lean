import Erdos249257.HalfResetSqrtEscapeMiddleDischarge

/-!
# Finite base band for the reset margin producers

Exact seam-greedy remainders for rows 9-17, computed inside Lean by
`decide +kernel`, together with the consumption-ready base instances of
the ceiling and floor margin producers on rows 10-15 and 13.  These are
the finite base cases a future descent lemma quantifies away; every
statement here is a computation, not an orbit assumption.
-/

namespace Erdos249257

open HalfCylinderIntegerGreedy

theorem seamRemainderNine : seamIntegerGreedyRemainder 9 = 541 := by decide +kernel
theorem seamRemainderTen : seamIntegerGreedyRemainder 10 = 1135 := by decide +kernel
theorem seamRemainderEleven : seamIntegerGreedyRemainder 11 = 2485 := by decide +kernel
theorem seamRemainderTwelve : seamIntegerGreedyRemainder 12 = 5836 := by decide +kernel
theorem seamRemainderThirteen : seamIntegerGreedyRemainder 13 = 15147 := by decide +kernel
theorem seamRemainderFourteen : seamIntegerGreedyRemainder 14 = 392 := by decide +kernel
theorem seamRemainderFifteen : seamIntegerGreedyRemainder 15 = 34333 := by decide +kernel
theorem seamRemainderSixteen : seamIntegerGreedyRemainder 16 = 71791 := by decide +kernel
theorem seamRemainderSeventeen : seamIntegerGreedyRemainder 17 = 156085 := by decide +kernel

/-- Ceiling producer base instances: `4 * R_(d+1) >= threshold` on
rows `d = 10..15`. -/
theorem ceilingBaseTen : (3 * 2 ^ ((10 + 6) / 2) + 2 * (10 - 1) : ℕ) ≤
    4 * seamIntegerGreedyRemainder 11 := by decide +kernel
theorem ceilingBaseEleven : (3 * 2 ^ ((11 + 6) / 2) + 2 * (11 - 1) : ℕ) ≤
    4 * seamIntegerGreedyRemainder 12 := by decide +kernel
theorem ceilingBaseTwelve : (3 * 2 ^ ((12 + 6) / 2) + 2 * (12 - 1) : ℕ) ≤
    4 * seamIntegerGreedyRemainder 13 := by decide +kernel
theorem ceilingBaseThirteen : (3 * 2 ^ ((13 + 6) / 2) + 2 * (13 - 1) : ℕ) ≤
    4 * seamIntegerGreedyRemainder 14 := by decide +kernel
theorem ceilingBaseFourteen : (3 * 2 ^ ((14 + 6) / 2) + 2 * (14 - 1) : ℕ) ≤
    4 * seamIntegerGreedyRemainder 15 := by decide +kernel
theorem ceilingBaseFifteen : (3 * 2 ^ ((15 + 6) / 2) + 2 * (15 - 1) : ℕ) ≤
    4 * seamIntegerGreedyRemainder 16 := by decide +kernel

/-- Floor producer binding base instance at the numerically tightest
upper reset: `E_13 >= 3 * 2 ^ 9`. -/
theorem floorBaseThirteen :
    (3 * 2 ^ ((13 + 5) / 2) : ℕ) ≤
      2 ^ (13 + 1) - seamIntegerGreedyRemainder 14 := by decide +kernel


/-- Full-threshold take-margin base instances on rows `t = 10, 11, 12,
14, 15` (row `13` is an upper-reset landing, not a take, so its
full-threshold instance is not required - the reset path consumes the
ceiling instances above). -/
theorem takeMarginBaseTen : (3 * 2 ^ ((10 + 6) / 2) + 2 * (10 - 1) : ℕ) ≤
    seamIntegerGreedyRemainder 11 := by decide +kernel
theorem takeMarginBaseEleven : (3 * 2 ^ ((11 + 6) / 2) + 2 * (11 - 1) : ℕ) ≤
    seamIntegerGreedyRemainder 12 := by decide +kernel
theorem takeMarginBaseTwelve : (3 * 2 ^ ((12 + 6) / 2) + 2 * (12 - 1) : ℕ) ≤
    seamIntegerGreedyRemainder 13 := by decide +kernel
theorem takeMarginBaseFourteen : (3 * 2 ^ ((14 + 6) / 2) + 2 * (14 - 1) : ℕ) ≤
    seamIntegerGreedyRemainder 15 := by decide +kernel
theorem takeMarginBaseFifteen : (3 * 2 ^ ((15 + 6) / 2) + 2 * (15 - 1) : ℕ) ≤
    seamIntegerGreedyRemainder 16 := by decide +kernel

#print axioms takeMarginBaseTen
#print axioms ceilingBaseThirteen
#print axioms floorBaseThirteen

end Erdos249257
