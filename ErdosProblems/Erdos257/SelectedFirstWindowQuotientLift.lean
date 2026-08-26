import Erdos249257.BooleanMobiusExactTransition
import Erdos249257.BooleanMobiusGreedyReduction
import Erdos249257.HalfCylinderFullShellSeamBridge

/-!
# The selected first window is an exact quotient lift

This file changes coordinates in the frozen first-window producer.  For a
fixed finite support, the binary coefficient window between rows `n` and
`n + J` is exactly the part of the row-`n + J` Mersenne quotient which is not
obtained by merely shifting the row-`n` quotient by `J` binary places.

At the full shell `J = n`, the frozen greedy margin is therefore exactly the
gap between the actual prefix quotient at row `2n` and the seam target.  This
is an identity, not a new estimate: it records that the full-shell charge
producer and the corresponding quotient-row inequality are the same open
boundary in two coordinates.
-/

namespace ErdosProblems.Erdos257

open Erdos257PeriodNoncollapse
open Erdos257PeriodNoncollapse.HalfCarryReachability
open Erdos257PeriodNoncollapse.HalfCylinderFiniteShadow
open Erdos257PeriodNoncollapse.HalfCylinderIntegerGreedy
open Erdos257PeriodNoncollapse.BooleanMobiusGreedyReduction

/-! ## A fixed support: coefficient windows are quotient lifts -/

/-- Iterating the exact quotient transition over `J` rows separates the
shifted old quotient from the newly exposed divisor-coefficient window. -/
theorem localPrefixQuotient_add_eq_pow_mul_add_finiteCoeffWindowNumerator
    {D : Finset ℕ} {n J : ℕ}
    (hn : 1 ≤ n) (hD : ∀ d ∈ D, 2 ≤ d) :
    localPrefixQuotient D (n + J) =
      2 ^ J * localPrefixQuotient D n +
        finiteCoeffWindowNumerator (↑D : Set ℕ) n J := by
  induction J with
  | zero =>
      simp [finiteCoeffWindowNumerator]
  | succ J ih =>
      rw [show n + (J + 1) = (n + J) + 1 by omega]
      rw [localPrefixQuotient_succ hD, ih]
      rw [finiteCoeffWindowNumerator]
      rw [endpointDivisorContribution_eq_supportCoeff (by omega)]
      rw [pow_succ]
      ring

/-- Subtractive form of the quotient lift.  The subtraction is exact because
the preceding theorem supplies the required order automatically. -/
theorem finiteCoeffWindowNumerator_eq_localPrefixQuotient_sub_shift
    {D : Finset ℕ} {n J : ℕ}
    (hn : 1 ≤ n) (hD : ∀ d ∈ D, 2 ≤ d) :
    finiteCoeffWindowNumerator (↑D : Set ℕ) n J =
      localPrefixQuotient D (n + J) -
        2 ^ J * localPrefixQuotient D n := by
  have h := localPrefixQuotient_add_eq_pow_mul_add_finiteCoeffWindowNumerator
    (D := D) (n := n) (J := J) hn hD
  omega

/-! ## Frozen margin as one moving quotient-row gap -/

/-- Self-contained finite-support bridge between the carry recurrence and the
local quotient defect.  Keeping this small bridge here avoids importing the
much larger critical-capacity frontier merely to cancel the two coordinates. -/
theorem mobiusCenteredHalfCarry_finset_eq_localEndpointDefect
    {D : Finset ℕ}
    (hD : ∀ d ∈ D, 2 ≤ d) (N : ℕ) :
    mobiusCenteredHalfCarry (↑D : Set ℕ) N =
      localEndpointDefect D (N + 1) := by
  induction N with
  | zero =>
      have hquot : localPrefixQuotient D 1 = 0 := by
        unfold localPrefixQuotient
        apply Finset.sum_eq_zero
        intro d hd
        unfold localMersenneQuotient
        apply Nat.div_eq_of_lt
        have hpow : 2 ^ 2 ≤ 2 ^ d :=
          Nat.pow_le_pow_right (by norm_num) (hD d hd)
        norm_num at hpow ⊢
        omega
      simp [localEndpointDefect, halfEndpointTarget, hquot]
  | succ N ih =>
      rw [mobiusCenteredHalfCarry_succ, ih,
        localEndpointDefect_succ (M := N + 1) (by omega) hD,
        endpointDivisorContribution_eq_supportCoeff
          (D := D) (n := N + 2) (by omega)]

/-- After the fixed-support quotient lift, the old row quotient cancels
exactly against the Möbius-centred carry.  Thus every frozen-margin horizon,
not only the full shell, is a single quotient-row gap. -/
theorem greedyHalfFrozenMargin_eq_localPrefixQuotient_sub_scaled_target
    (n J : ℕ) (hn : 2 ≤ n) :
    greedyHalfFrozenMargin (n - 1) J =
      (localPrefixQuotient (halfGreedyPrefixSupport (n - 1)) (n + J) : ℤ) -
        (2 : ℤ) ^ J * (halfEndpointTarget n : ℤ) := by
  let P := halfGreedyPrefixSupport (n - 1)
  have hbelow : ∀ d ∈ P, 2 ≤ d ∧ d < n :=
    halfGreedyPrefixSupport_pred_below n hn
  have hlift :=
    localPrefixQuotient_add_eq_pow_mul_add_finiteCoeffWindowNumerator
      (D := P) (n := n) (J := J) (by omega)
      (fun d hd ↦ (hbelow d hd).1)
  have hcarry :=
    mobiusCenteredHalfCarry_finset_eq_localEndpointDefect
      (D := P) (fun d hd ↦ (hbelow d hd).1) (n - 1)
  rw [Nat.sub_add_cancel (by omega : 1 ≤ n)] at hcarry
  have hliftZ :
      (localPrefixQuotient P (n + J) : ℤ) =
        (2 : ℤ) ^ J * (localPrefixQuotient P n : ℤ) +
          (finiteCoeffWindowNumerator (↑P : Set ℕ) n J : ℤ) := by
    exact_mod_cast hlift
  unfold greedyHalfFrozenMargin
  rw [Nat.sub_add_cancel (by omega : 1 ≤ n), hcarry]
  unfold localEndpointDefect
  dsimp [P] at hliftZ ⊢
  rw [hliftZ]
  ring

/-- Exact crossing criterion at every governed horizon.  This is the finite
quotient-row form of frozen first passage. -/
theorem greedyHalfFrozenMargin_nonneg_iff_scaled_target_le_quotient
    (n J : ℕ) (hn : 2 ≤ n) :
    0 ≤ greedyHalfFrozenMargin (n - 1) J ↔
      2 ^ J * halfEndpointTarget n ≤
        localPrefixQuotient (halfGreedyPrefixSupport (n - 1)) (n + J) := by
  rw [greedyHalfFrozenMargin_eq_localPrefixQuotient_sub_scaled_target n J hn]
  rw [sub_nonneg]
  norm_cast

/-! ## The actual half-greedy prefix at the full shell -/

/-- On a support contained in the proper half row, the seam's truncated
Mersenne sum is literally the row-`2n` local quotient. -/
theorem stemTruncatedSum_eq_localPrefixQuotient_two_mul
    {D : Finset ℕ} {n : ℕ}
    (hbelow : ∀ d ∈ D, 2 ≤ d ∧ d < n) :
    stemTruncatedSum n D = localPrefixQuotient D (2 * n) := by
  rw [stemTruncatedSum_eq_sum_support hbelow]
  unfold localPrefixQuotient
  apply Finset.sum_congr rfl
  intro d hd
  exact (localMersenneQuotient_two_mul_eq_truncatedMersenneWeight n d).symm

/-- The first full-shell margin of the actual half-greedy prefix is exactly
its row-`2n` quotient gap from the seam target. -/
theorem greedyHalfFrozenMargin_fullShell_eq_localPrefixQuotient_sub_target
    (n : ℕ) (hn : 2 ≤ n) :
    greedyHalfFrozenMargin (n - 1) n =
      (localPrefixQuotient (halfGreedyPrefixSupport (n - 1)) (2 * n) : ℤ) -
        (seamSubsetTarget n : ℤ) := by
  rw [greedyHalfFrozenMargin_fullShell_eq_stemTruncatedSum_sub_target n hn]
  rw [stemTruncatedSum_eq_localPrefixQuotient_two_mul
    (halfGreedyPrefixSupport_pred_below n hn)]

/-- Consequently, proving nonnegative first-window charge is neither weaker
nor stronger than proving that the actual prefix quotient reaches the seam
target at row `2n`. -/
theorem greedyHalfFrozenMargin_fullShell_nonneg_iff_seamSubsetTarget_le_quotient
    (n : ℕ) (hn : 2 ≤ n) :
    0 ≤ greedyHalfFrozenMargin (n - 1) n ↔
      seamSubsetTarget n ≤
        localPrefixQuotient (halfGreedyPrefixSupport (n - 1)) (2 * n) := by
  rw [greedyHalfFrozenMargin_fullShell_eq_localPrefixQuotient_sub_target n hn]
  omega

/-- Full-shell specialization of the aggregate lift for the actual frozen
half-greedy prefix. -/
theorem halfGreedyPrefix_fullShell_quotient_lift
    (n : ℕ) (hn : 2 ≤ n) :
    localPrefixQuotient (halfGreedyPrefixSupport (n - 1)) (2 * n) =
      2 ^ n * localPrefixQuotient (halfGreedyPrefixSupport (n - 1)) n +
        finiteCoeffWindowNumerator
          (↑(halfGreedyPrefixSupport (n - 1)) : Set ℕ) n n := by
  have h := localPrefixQuotient_add_eq_pow_mul_add_finiteCoeffWindowNumerator
    (D := halfGreedyPrefixSupport (n - 1)) (n := n) (J := n)
    (by omega) (fun d hd ↦
      (halfGreedyPrefixSupport_pred_below n hn d hd).1)
  simpa [two_mul] using h

#print axioms localPrefixQuotient_add_eq_pow_mul_add_finiteCoeffWindowNumerator
#print axioms finiteCoeffWindowNumerator_eq_localPrefixQuotient_sub_shift
#print axioms mobiusCenteredHalfCarry_finset_eq_localEndpointDefect
#print axioms greedyHalfFrozenMargin_eq_localPrefixQuotient_sub_scaled_target
#print axioms greedyHalfFrozenMargin_nonneg_iff_scaled_target_le_quotient
#print axioms stemTruncatedSum_eq_localPrefixQuotient_two_mul
#print axioms greedyHalfFrozenMargin_fullShell_eq_localPrefixQuotient_sub_target
#print axioms greedyHalfFrozenMargin_fullShell_nonneg_iff_seamSubsetTarget_le_quotient
#print axioms halfGreedyPrefix_fullShell_quotient_lift

end ErdosProblems.Erdos257
