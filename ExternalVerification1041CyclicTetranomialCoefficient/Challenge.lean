import Mathlib

namespace Erdos249257.ExternalVerification1041CyclicTetranomialCoefficient

/-- Abel summation for a root of a centred tetranomial. -/
theorem tetranomialRoot_spoke_factorization
    {m r s : ℕ} {a b c w : ℂ} {u : ℝ}
    (hroot : w ^ m + a * w ^ r + b * w ^ s + c = 0) :
    (u : ℂ) ^ m * w ^ m + a * (u : ℂ) ^ r * w ^ r +
        b * (u : ℂ) ^ s * w ^ s + c =
      ((1 - u ^ s : ℝ) : ℂ) * c -
        ((u ^ s - u ^ r : ℝ) : ℂ) * (a * w ^ r + w ^ m) -
          ((u ^ r - u ^ m : ℝ) : ℂ) * w ^ m := by
  sorry

/-- The sharp root-dependent coefficient condition forces the complete root
spoke strictly inside the unit lemniscate. -/
theorem tetranomialRoot_spoke_norm_lt_one_of_rootBudget
    {m r s : ℕ} (hs : 1 ≤ s) (hsr : s ≤ r) (hrm : r ≤ m)
    {a b c w : ℂ}
    (hroot : w ^ m + a * w ^ r + b * w ^ s + c = 0)
    (hw : ‖w‖ < 1) (hc : ‖c‖ < 1)
    (hbudget : ‖c‖ + ‖b‖ * ‖w‖ ^ s < 1) {u : ℝ}
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    ‖(u : ℂ) ^ m * w ^ m + a * (u : ℂ) ^ r * w ^ r +
        b * (u : ℂ) ^ s * w ^ s + c‖ < 1 := by
  sorry

/-- The coefficient-only corollary: the middle coefficient `a` is
unrestricted, while `b` and `c` spend at most the unit budget. -/
theorem tetranomialRoot_spoke_norm_lt_one_of_lowCoeffBudget
    {m r s : ℕ} (hs : 1 ≤ s) (hsr : s ≤ r) (hrm : r ≤ m)
    {a b c w : ℂ}
    (hroot : w ^ m + a * w ^ r + b * w ^ s + c = 0)
    (hw : ‖w‖ < 1) (hc : ‖c‖ < 1)
    (hbudget : ‖b‖ + ‖c‖ ≤ 1) {u : ℝ}
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    ‖(u : ℂ) ^ m * w ^ m + a * (u : ℂ) ^ r * w ^ r +
        b * (u : ℂ) ^ s * w ^ s + c‖ < 1 := by
  sorry

end Erdos249257.ExternalVerification1041CyclicTetranomialCoefficient
