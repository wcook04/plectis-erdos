import Mathlib
import ErdosProblems.Erdos1041.CyclicTetranomialCoefficientCase

namespace Erdos249257.ExternalVerification1041CyclicTetranomialCoefficient

theorem tetranomialRoot_spoke_factorization
    {m r s : ℕ} {a b c w : ℂ} {u : ℝ}
    (hroot : w ^ m + a * w ^ r + b * w ^ s + c = 0) :
    (u : ℂ) ^ m * w ^ m + a * (u : ℂ) ^ r * w ^ r +
        b * (u : ℂ) ^ s * w ^ s + c =
      ((1 - u ^ s : ℝ) : ℂ) * c -
        ((u ^ s - u ^ r : ℝ) : ℂ) * (a * w ^ r + w ^ m) -
          ((u ^ r - u ^ m : ℝ) : ℂ) * w ^ m :=
  ErdosProblems.Erdos1041.tetranomialRoot_spoke_factorization hroot

theorem tetranomialRoot_spoke_norm_lt_one_of_rootBudget
    {m r s : ℕ} (hs : 1 ≤ s) (hsr : s ≤ r) (hrm : r ≤ m)
    {a b c w : ℂ}
    (hroot : w ^ m + a * w ^ r + b * w ^ s + c = 0)
    (hw : ‖w‖ < 1) (hc : ‖c‖ < 1)
    (hbudget : ‖c‖ + ‖b‖ * ‖w‖ ^ s < 1) {u : ℝ}
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    ‖(u : ℂ) ^ m * w ^ m + a * (u : ℂ) ^ r * w ^ r +
        b * (u : ℂ) ^ s * w ^ s + c‖ < 1 :=
  ErdosProblems.Erdos1041.tetranomialRoot_spoke_norm_lt_one_of_rootBudget
    hs hsr hrm hroot hw hc hbudget hu0 hu1

theorem tetranomialRoot_spoke_norm_lt_one_of_lowCoeffBudget
    {m r s : ℕ} (hs : 1 ≤ s) (hsr : s ≤ r) (hrm : r ≤ m)
    {a b c w : ℂ}
    (hroot : w ^ m + a * w ^ r + b * w ^ s + c = 0)
    (hw : ‖w‖ < 1) (hc : ‖c‖ < 1)
    (hbudget : ‖b‖ + ‖c‖ ≤ 1) {u : ℝ}
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    ‖(u : ℂ) ^ m * w ^ m + a * (u : ℂ) ^ r * w ^ r +
        b * (u : ℂ) ^ s * w ^ s + c‖ < 1 :=
  ErdosProblems.Erdos1041.tetranomialRoot_spoke_norm_lt_one_of_lowCoeffBudget
    hs hsr hrm hroot hw hc hbudget hu0 hu1

end Erdos249257.ExternalVerification1041CyclicTetranomialCoefficient
