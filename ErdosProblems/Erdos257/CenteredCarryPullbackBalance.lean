import Erdos249257.HalfCylinderPullbackCardPropagation
import Mathlib.Tactic

/-!
# Centered-carry balance in an exact pullback cylinder

The frozen divisor-incidence charge of a seam pullback is a finite
multiplicity window.  After subtracting its all-ones baseline, the window is
a coboundary between two centered Möbius carries.  This file substitutes that
coboundary into an arbitrary exact base-four cylinder.

The resulting identity is useful as a boundary law: a small pullback
coordinate cannot be studied independently of the two endpoint carries.
-/

namespace ErdosProblems.Erdos257

open Erdos257PeriodNoncollapse
open Erdos257PeriodNoncollapse.HalfCarryReachability
open Erdos257PeriodNoncollapse.HalfCylinderIntegerGreedy
open Erdos257PeriodNoncollapse.HalfCylinderPullbackCardPropagation
open Erdos257PeriodNoncollapse.HalfUpperResetCriticalBand

noncomputable section

/-- Exact endpoint-carry form of a frozen pullback cylinder.  If

`G + C = 4^k Q`,

then the centered carry at the far endpoint is

`e₁ = 4^k (e₀ + 1 - Q) + G - 1`.

Thus the multiplicity window contributes no hidden interior error: every
incidence is absorbed by the two endpoint carries and the explicit baseline.
-/
theorem fixedSupport_exactCylinder_centeredCarry_balance
    (b : ℕ) (A : Finset ℕ) (k : ℕ) (G Q : ℤ) (hb : 1 ≤ b)
    (hcylinder :
      G + (fixedSupportPulseCharge b A k : ℤ) = (4 : ℤ) ^ k * Q) :
    mobiusCenteredHalfCarry (↑A : Set ℕ) (2 * b + 2 * k - 1) =
      (4 : ℤ) ^ k *
          (mobiusCenteredHalfCarry (↑A : Set ℕ) (2 * b - 1) + 1 - Q) +
        G - 1 := by
  have hcoboundary :=
    fixedSupportPulseCharge_sub_geometric_eq_centeredCarry b A k hb
  linear_combination hcoboundary - hcylinder

/-- Exact slack decomposition for the two-stage base-four amplifier.  The
unused margin in the composed parent/child inequality is not a scalar error:
it is the backward-cylinder slack amplified by `4^k`, plus three copies of
the forward-cylinder slack.  This is the lossless coordinate needed by any
recursive packet induction. -/
theorem twoStage_amplification_slack_decomposition
    (R G Q : ℤ) (m k : ℕ) :
    9 * R -
          ((4 : ℤ) ^ (m + k) * Q +
            2 * (4 : ℤ) ^ k * Q + 6 * G) =
      (4 : ℤ) ^ k *
          (3 * G - ((4 : ℤ) ^ m * Q + 2 * Q)) +
        3 * (3 * R - ((4 : ℤ) ^ k * G + 2 * G)) := by
  rw [pow_add]
  ring

#print axioms fixedSupport_exactCylinder_centeredCarry_balance
#print axioms twoStage_amplification_slack_decomposition

end

end ErdosProblems.Erdos257
