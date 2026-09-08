import ErdosProblems.Erdos68.PaperCompleteKernelSizeSum
import Mathlib.Order.Interval.Finset.Nat

/-!
# Size-only finite denominator certificate

This branch preserves the returned 80000-bit interval and Farey witnesses,
without importing the 300005-term grid computation. The two floor-block
leaves and each finite comparison below must elaborate before any numerical
exclusion is established. No certificate predicate is assumed by the final
theorem. These source candidates have not yet been kernel checked.
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

namespace ErdosProblems.Erdos68.PaperComplete.FiniteLead.SizeOnly

theorem tail_quotient_checked :
    (2 ^ 80000) / Nat.factorial 7053 = 3 := by
  have hchecked : (2 ^ 80000) / kernelFactorial 7053 = 3 := by decide +kernel
  exact (congrArg (fun d : ℕ => (2 ^ 80000) / d)
    (kernelFactorial_eq 7053).symm).trans hchecked

#print axioms tail_quotient_checked

private theorem upper_eq_of_tail (L C T : ℕ) (hc : C = 7052) (ht : T = 3) :
    L + 7056 = L + C + T + 1 := by
  omega

theorem dyadic_valid_checked : sizeDyadic.Valid := by
  change 2 ≤ 7053 ∧ sizeLower = floorPrefix (2 ^ 80000) 7053 ∧
    sizeLower + 7056 = sizeLower + (Finset.Icc 2 7053).card +
      (2 ^ 80000) / Nat.factorial 7053 + 1
  exact And.intro (by decide) (And.intro size_floorPrefix_checked.symm
    (upper_eq_of_tail sizeLower (Finset.Icc 2 7053).card
      ((2 ^ 80000) / Nat.factorial 7053) (Nat.card_Icc 2 7053)
      tail_quotient_checked))

#print axioms dyadic_valid_checked

theorem farey_valid_checked : sizeFarey.Valid sizeDyadic (2 ^ 39990) := by
  decide +kernel

#print axioms farey_valid_checked

theorem sharp_checked : sizeFarey.Sharp sizeDyadic := by
  decide +kernel

#print axioms sharp_checked

theorem decimal_bound_checked :
    (10 : ℕ) ^ 12040 < sizeFarey.leftDen + sizeFarey.rightDen := by
  decide +kernel

/-- The printed binary bound and the stronger exact denominator sum follow
from the actual series representation, without any validity hypothesis. -/
theorem denominator_exclusion
    (a : ℤ) (q : ℕ) (hq : 0 < q)
    (hS : _root_.Erdos68.factorialGapSeries = (a : ℝ) / q) :
    (2 : ℕ) ^ 39990 ≤ q ∧
      sizeFarey.leftDen + sizeFarey.rightDen ≤ q ∧ (10 : ℕ) ^ 12040 < q := by
  have hexact := denominator_bound_of_farey_sum dyadic_valid_checked
    farey_valid_checked a q hq hS
  exact ⟨denominator_bound_of_farey dyadic_valid_checked farey_valid_checked a q hq hS,
    hexact, decimal_bound_checked.trans_le hexact⟩

end ErdosProblems.Erdos68.PaperComplete.FiniteLead.SizeOnly
