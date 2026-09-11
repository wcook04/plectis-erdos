/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Erdos249257.LcmConeNonflat
import Erdos249257.DiagonalPincerCertificatesT31

/-!
# The lcm-jump shift coincides with the diagonal at `t = 2^k - 1`

`LcmConeNonflat.irrational_totient_series_of_lcm_jump_kill_supply` derives #249
from a cofinal supply of kills at the *lcm-jump* shift,

  `certifiedKill (periodLcm (t+1) - periodLcm t) (periodLcm t) L`,

and the diagonal collapse in `LcmDiagonalReduction` derives #249 from a cofinal
supply of kills at the *diagonal* shift, `certifiedKill (periodLcm t) (periodLcm t) L`.
The two routes were developed separately and the corpus recorded no instance of
the first at any scale.

They are not independent. `periodLcm t = lcm (1, ..., t)` grows by a factor of
`q` exactly when `t+1` is a prime power `q`, so the jump length is
`periodLcm (t+1) - periodLcm t = (q - 1) * periodLcm t`. At `q = 2` -- that is,
at `t + 1 = 2^k`, so `t = 2^k - 1` -- the factor is one and the jump length
equals the starting height. At those `t` the two shifts are the *same natural
number*, and every diagonal certificate already deposited there is a jump
certificate without any new totient arithmetic.

`periodLcm_strict_jump_sub_ge` already records the inequality
`periodLcm t <= periodLcm (t+1) - periodLcm t`. What follows is the equality
case, which is where the two routes meet.

This does not close the jump-supply hypothesis: that hypothesis is cofinal and
the diagonal deposits are finite, so the same open supply obligation remains.
What it does is remove the appearance that the jump route is a separate and
wholly unproduced obstacle. Any cofinal diagonal supply along the powers of two
discharges it.
-/

namespace Erdos249

open Erdos249257 Erdos249257.TotientTailPeriodKiller

/-- At `t + 1 = 2^k` the lcm height exactly doubles, so the jump length equals
the starting height and the jump shift *is* the diagonal shift.

Stated for the concrete scales at which the corpus holds diagonal deposits;
`decide` settles each by evaluating `lcm (1, ..., t)`. -/
theorem periodLcm_jump_eq_height_at_one :
    periodLcm 2 - periodLcm 1 = periodLcm 1 := by decide

theorem periodLcm_jump_eq_height_at_three :
    periodLcm 4 - periodLcm 3 = periodLcm 3 := by decide

theorem periodLcm_jump_eq_height_at_seven :
    periodLcm 8 - periodLcm 7 = periodLcm 7 := by decide

theorem periodLcm_jump_eq_height_at_fifteen :
    periodLcm 16 - periodLcm 15 = periodLcm 15 := by decide

theorem periodLcm_jump_eq_height_at_thirtyone :
    periodLcm 32 - periodLcm 31 = periodLcm 31 := by
  norm_num [periodLcm, Nat.lcm]

/-- **A kill at an lcm-jump shift, at `t = 7`.**  The diagonal deposit at
`lcm (1, ..., 7) = 420`, depth `14`, read at the jump shift. -/
theorem certifiedKill_lcm_jump_at_seven :
    certifiedKill (periodLcm 8 - periodLcm 7) (periodLcm 7) 14 := by
  rw [periodLcm_jump_eq_height_at_seven]
  exact certifiedKill_periodLcm_diagonal_at_seven

/-- **Kills at lcm-jump shifts, at `t = 1` and `t = 3`.**  Read off the
`1 <= t <= 6` diagonal deposit at the two scales in that range where the jump
coincides with the height. -/
theorem certifiedKill_lcm_jump_at_one :
    certifiedKill (periodLcm 2 - periodLcm 1) (periodLcm 1) (diagonalKillDepth 1) := by
  rw [periodLcm_jump_eq_height_at_one]
  exact certifiedKill_periodLcm_diagonal_upto_six 1 (by decide)

theorem certifiedKill_lcm_jump_at_three :
    certifiedKill (periodLcm 4 - periodLcm 3) (periodLcm 3) (diagonalKillDepth 3) := by
  rw [periodLcm_jump_eq_height_at_three]
  exact certifiedKill_periodLcm_diagonal_upto_six 3 (by decide)

/-! ### The two scales still missing

`{1, 3, 7, 15, 31, 63}` are the scales where the jump coincides with the height.
Four of them (`1, 3, 7, 31`) carry diagonal deposits and are discharged above.
`t = 15` and `t = 63` do not: the deposited scales run `1..8` and then `19, 23,
25, 27, 29, 31, 32, 37, ..., 61, 64`, skipping both.

Neither is out of reach, and neither is a one-liner.  `certifiedKill` at these
scales needs `Nat.totient` at roughly `2^24` and `2^90`, which `decide` cannot
evaluate -- it would filter a range of that size.  The deposited scales get their
totients from factorisation plus imported Lucas primality certificates, which is
what the emitting generator produces.  Running that generator at `t = 15` and
`t = 63` would yield two further jump instances for free, and `t = 63` in
particular would extend the exhibited jump family past the current `t = 31`. -/

/-- **A kill at an lcm-jump shift, at `t = 31`.**  The wave-31 diagonal
certificate at `lcm (1, ..., 31) = 72201776446800`, depth `49`, read at the jump
shift `periodLcm 32 - periodLcm 31`.

The underlying certificate already evaluates totients in both the block above
`periodLcm 31` and the block above `periodLcm 32`, because the diagonal window
at `h = N = periodLcm 31` reaches `N + h = periodLcm 32`.  So this is the same
kernel computation, not a new one. -/
theorem certifiedKill_lcm_jump_at_thirtyone :
    certifiedKill (periodLcm 32 - periodLcm 31) (periodLcm 31) 49 := by
  rw [periodLcm_jump_eq_height_at_thirtyone]
  exact certifiedKill_diagonal_t31

end Erdos249
