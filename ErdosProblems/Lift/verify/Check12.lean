import ErdosProblems.Lift.Recon249

open Erdos249257 Erdos249257.TotientTailPeriodKiller
open ErdosProblems.Lift.Recon249

#print axioms windowDiscrepancy_diagonal
#print axioms windowDiscrepancy_sub_dvd
#print axioms certifiedKill_transfer
#print axioms factorization_window
#print axioms diagCoeff_lift_coprime
#print axioms diagCoeff_lift_dvd
#print axioms uncoveredOffsets_card
#print axioms lift_depth_floor_growth
#print axioms certifiedKill_periodLcm_67_depth
#print axioms natural_lift_guess_fails_at_four
#print axioms diagCoeff_61_two_ne_four
#print axioms windowDiscrepancy_shift_emod

/-! ## PROBE A: which direction does `certifiedKill_transfer` run? -/

-- `certifiedKill_transfer` demands `N' + h' ≤ N + h`, i.e. the TARGET cell must be
-- no larger than the SOURCE cell.  A lift goes H ↦ p*H with p ≥ 2, so the target is
-- strictly larger.  The side condition is therefore unsatisfiable in the lift direction.
theorem transfer_direction_blocks_lift {p H : ℕ} (hp : 2 ≤ p) (hH : 1 ≤ H) :
    ¬ (p * H + p * H ≤ H + H) := by
  have : 2 * H ≤ p * H := Nat.mul_le_mul_right H hp
  omega

-- Concretely at the frontier: the transfer lemma can never be instantiated with
-- source `(periodLcm 66, periodLcm 66)` and target `(periodLcm 67, periodLcm 67)`.
theorem transfer_unusable_at_67 :
    ¬ (periodLcm 67 + periodLcm 67 ≤ periodLcm 66 + periodLcm 66) := by
  rw [periodLcm_66_val, periodLcm_67_val]; norm_num

-- The lemma DOES run downward, which is the useless direction: the certified cell
-- t = 66 already exists, and transfer only ever yields cells at or below it.

/-! ## PROBE B: does the Result-3 lift law actually fire at the frontier offset d = 67? -/

-- `diagCoeff_lift_coprime` needs `67 ∤ H₆₆+1` and `67 ∤ 2·H₆₆+1`;
-- `diagCoeff_lift_dvd` needs both to be divisible.  Neither side condition is
-- discharged anywhere in Recon249.lean.  They do in fact hold (coprime branch):
theorem lift_law_fires_at_67 :
    ¬ (67 ∣ (periodLcm 66 + 1)) ∧ ¬ (67 ∣ (2 * periodLcm 66 + 1)) := by
  rw [periodLcm_66_val]
  constructor <;> decide

-- so the docstring claim "1 of 98 coefficients determined" is TRUE, but
-- `lift_coverage_at_67` proves only `|{d ∈ (0,98] : 67 ∣ d}| = 1`, a fact about
-- integers, not about the lift law firing.

/-! ## PROBE C: is the divisible branch ever reachable at a prime frontier? -/

-- `diagCoeff_lift_dvd` needs p ∣ (H+e) AND p ∣ (2H+e); subtracting, p ∣ H.
-- At every prime-power frontier t = p (p prime, p > t-1) we have p ∤ periodLcm (p-1),
-- so the divisible branch is vacuous there.  Only the coprime branch can ever apply.
theorem dvd_branch_needs_p_dvd_H {p H e : ℕ} (h1 : p ∣ (H + e)) (h2 : p ∣ (2 * H + e)) :
    p ∣ H := by
  have : (2 * H + e) - (H + e) = H := by omega
  simpa [this] using Nat.dvd_sub h2 h1

/-! ## PROBE D: the "natural guess" is NOT the hypothesis `certifiedKill_transfer` consumes. -/

-- `certifiedKill_transfer` consumes `c_new(d) - c_old(d) ≡ 0 mod 2^d`.
-- Result 5 refutes `c_new(d) - p * c_old(d) ≡ 0 mod 2^d`.  These are different
-- statements whenever p ≠ 1, and the p-scaled one does NOT carry a certificate:
-- multiplication by p on ℤ/2^L is a bijection for odd p but does not preserve the
-- excluded arc.  Explicit witness that "A_old safe" does not imply "2·A_old safe":
theorem scaling_does_not_preserve_the_arc :
    (5 : ℤ) < 513 % 2 ^ 10 ∧ (513 : ℤ) % 2 ^ 10 < 2 ^ 10 - 5
      ∧ ¬ ((5 : ℤ) < (2 * 513) % 2 ^ 10) := by
  refine ⟨by norm_num, by norm_num, by norm_num⟩
