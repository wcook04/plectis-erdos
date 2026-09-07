import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Filter
import Mathlib.Data.Finset.Range
import Mathlib.Data.Nat.GCD.Basic

/-!
# Finite part of the primitive coefficient injection

The ordinary proof of `c_(2,11)(N) ≥ c_(10,11)(N)` reduces one case to

`U (5 * m) ≥ U m` for `m ≤ 1218` and `5 ∤ m`,

where `U m` counts reduced residues in `(m / 2, 6m / 11)`. The analytic
estimate in the accompanying note proves the inequality above this range.
This file certifies exactly the finite residue count used there.
-/

namespace Erdos257PeriodNoncollapse

/-- Reduced residues in the open interval `(n/2, 6n/11)`. -/
def primitive211IntervalCount (n : ℕ) : ℕ :=
  ((Finset.range n).filter fun k =>
    2 * k > n ∧ 11 * k < 6 * n ∧ Nat.Coprime k n).card

/-- The finite part of the scale-five inequality. -/
theorem primitive211IntervalCount_scale_five_small :
    ∀ m ∈ Finset.range 1219,
      1 ≤ m → m % 5 ≠ 0 →
        primitive211IntervalCount m ≤
          primitive211IntervalCount (5 * m) := by
  native_decide

end Erdos257PeriodNoncollapse
