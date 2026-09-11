import Erdos249257.DiagonalPincerPrimeCertificates.ClosureT64.Support
import Erdos249257.DiagonalPincerPrimeCertificates.ClosureT64.Level4A

/-!
# ClosureT64 dependency level 5

Generated deterministically by `scripts/shard_closure_t64.py`; proof bodies are preserved verbatim from the original monolith.
-/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

theorem prime_lucas_78201579809029247 : Nat.Prime 78201579809029247 := by
  have hfermat : (5 : ZMod 78201579809029247) ^ (78201579809029247 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (5 : ZMod 78201579809029247) ^ ((78201579809029247 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (5 : ZMod 78201579809029247) ^ ((78201579809029247 - 1) / 39100789904514623) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 78201579809029247 (5 : ZMod 78201579809029247)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (39100789904514623, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (39100789904514623, 1)] : List FactorBlock).map factorBlockValue).prod = 78201579809029247 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · norm_num
      · exact prime_lucas_39100789904514623) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · exact hfactor_0
    · exact hfactor_1

end TotientTailPeriodKiller
end Erdos249257
