import Erdos249257.DiagonalPincerPrimeCertificates.ClosureT64.Support
import Erdos249257.DiagonalPincerPrimeCertificates.ClosureT64.Level5A

/-!
# ClosureT64 dependency level 6

Generated deterministically by `scripts/shard_closure_t64.py`; proof bodies are preserved verbatim from the original monolith.
-/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

theorem prime_lucas_73287897909498984337 : Nat.Prime 73287897909498984337 := by
  have hfermat : (5 : ZMod 73287897909498984337) ^ (73287897909498984337 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (5 : ZMod 73287897909498984337) ^ ((73287897909498984337 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (5 : ZMod 73287897909498984337) ^ ((73287897909498984337 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (5 : ZMod 73287897909498984337) ^ ((73287897909498984337 - 1) / 17) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (5 : ZMod 73287897909498984337) ^ ((73287897909498984337 - 1) / 89813600379287971) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 73287897909498984337 (5 : ZMod 73287897909498984337)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 4), (3, 1), (17, 1), (89813600379287971, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 4), (3, 1), (17, 1), (89813600379287971, 1)] : List FactorBlock).map factorBlockValue).prod = 73287897909498984337 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · exact prime_lucas_89813600379287971) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3

end TotientTailPeriodKiller
end Erdos249257
