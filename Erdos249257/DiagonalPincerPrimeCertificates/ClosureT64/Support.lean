import Erdos249257.DiagonalPincerCertificates

/-!
# Shared support for the Lucas closure through t=64

This generated support module contains the two proof-kernel-preserving helper
lemmas shared by the dependency-safe ClosureT64 certificate shards.
-/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

theorem natCast_zmod_eq_one_iff (a m : ℕ) :
    (a : ZMod m) = 1 ↔ a % m = 1 % m := by
  simpa using ZMod.natCast_eq_natCast_iff' a 1 m

theorem natCast_zmod_ne_one_iff (a m : ℕ) :
    (a : ZMod m) ≠ 1 ↔ a % m ≠ 1 % m := by
  exact not_congr (natCast_zmod_eq_one_iff a m)

end TotientTailPeriodKiller
end Erdos249257
