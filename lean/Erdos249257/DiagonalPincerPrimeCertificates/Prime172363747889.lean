import Erdos249257.DiagonalPincerCertificates
import Erdos249257.DiagonalPincerPrimeCertificates.Prime10772734243

/-! A bounded Lucas certificate for one t=37 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_172363747889 : Nat.Prime 172363747889 := by
  have hfermat : (3 : ZMod 172363747889) ^ (172363747889 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (3 : ZMod 172363747889) ^ ((172363747889 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (3 : ZMod 172363747889) ^ ((172363747889 - 1) / 10772734243) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 172363747889 (3 : ZMod 172363747889)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 4), (10772734243, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 4), (10772734243, 1)] : List FactorBlock).map factorBlockValue).prod = 172363747889 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · norm_num
      · exact prime_lucas_10772734243) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · exact hfactor_0
    · exact hfactor_1

#print axioms prime_lucas_172363747889

end TotientTailPeriodKiller
end Erdos249257
