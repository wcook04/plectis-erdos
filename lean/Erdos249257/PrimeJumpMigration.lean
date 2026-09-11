import Erdos249257.ActualForeignResidueProjection
import Mathlib.Tactic

/-!
# Prime-jump residue-channel migration

This file records the channel-level correction required by every prime-jump
argument: the actual transition contribution is the post-jump value plus the
pre-jump migration of the same channel.  It proves exact old-carrier
cancellation and records the first migration sign reversal as a kernel-checkable
fixture.  It does not assert a full residue-tsum identity or the missing
prime-saturated-versus-prime-free separation theorem.
-/

namespace Erdos249257.PrimeJumpMigration

open ActualForeignResidueProjection
open TotientTailPeriodKiller

/-! ## Channel-level migration -/

/-- Contribution of residue channel `d` to `D(pH) - p D(H)`. -/
noncomputable def residueHeckeDefect (d H p : ℕ) : ℝ :=
  residueIncrement d (p * H) - p * residueIncrement d H

/-- The divisor value seen after the jump.  For a newly absorbed channel this
is the explicit post-jump contribution. -/
noncomputable def postJumpResidueChannel (d H p : ℕ) : ℝ :=
  residueIncrement d (p * H)

/-- The pre-jump value of the same channel, transported with coefficient
`-p`.  This is the migration term omitted by a post-jump-only split. -/
noncomputable def preJumpMigrationChannel (d H p : ℕ) : ℝ :=
  -p * residueIncrement d H

/-- The actual transition channel is post-jump contribution plus same-channel
migration. -/
theorem residueHeckeDefect_eq_postJump_add_migration (d H p : ℕ) :
    residueHeckeDefect d H p =
      postJumpResidueChannel d H p + preJumpMigrationChannel d H p := by
  unfold residueHeckeDefect postJumpResidueChannel preJumpMigrationChannel
  ring

/-- Every carrier already dividing `H` cancels exactly in the prime-jump
commutator.  No analytic estimate is used. -/
theorem residueHeckeDefect_eq_zero_of_dvd
    {d H p : ℕ} (hd : 0 < d) (hdvd : d ∣ H) :
    residueHeckeDefect d H p = 0 := by
  have hpdvd : d ∣ p * H := hdvd.mul_left p
  rw [residueHeckeDefect, residueIncrement_of_dvd hd hpdvd,
    residueIncrement_of_dvd hd hdvd]
  push_cast
  ring

/-- At the first new-prime jump, the `d = 5` transition channel is positive:
the pre-jump migration reverses the sign of its negative post-jump divisor
contribution. -/
theorem residueHeckeDefect_five_twelve :
    residueHeckeDefect 5 12 5 = (10228 : ℝ) / 961 := by
  have hmu : ArithmeticFunction.moebius 5 = -1 :=
    ArithmeticFunction.moebius_apply_prime (by norm_num)
  norm_num [residueHeckeDefect, residueIncrement, foreignResidueKernel,
    residueOffset, hmu]

/-- The post-jump part of the same fixture is negative. -/
theorem postJumpResidueChannel_five_twelve :
    postJumpResidueChannel 5 12 5 = -(12 : ℝ) / 31 := by
  have hmu : ArithmeticFunction.moebius 5 = -1 :=
    ArithmeticFunction.moebius_apply_prime (by norm_num)
  norm_num [postJumpResidueChannel, residueIncrement, foreignResidueKernel,
    residueOffset, hmu]


#print axioms residueHeckeDefect_eq_zero_of_dvd
#print axioms residueHeckeDefect_five_twelve

end Erdos249257.PrimeJumpMigration
