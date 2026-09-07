import Mathlib

namespace Erdos249257.ExternalVerification1041CyclicTetranomialCoefficient

theorem tetranomialRoot_spoke_norm_lt_one_of_lowCoeffBudget
    (_extra : True)
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
