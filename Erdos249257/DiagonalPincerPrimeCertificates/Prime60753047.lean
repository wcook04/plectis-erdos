import Erdos249257.DiagonalPincerCertificates

/-! A bounded Lucas certificate for one t=29 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_60753047 : Nat.Prime 60753047 := by
  have hfermat : (5 : ZMod 60753047) ^ (60753047 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (5 : ZMod 60753047) ^ ((60753047 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (5 : ZMod 60753047) ^ ((60753047 - 1) / 47) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (5 : ZMod 60753047) ^ ((60753047 - 1) / 646309) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 60753047 (5 : ZMod 60753047)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (47, 1), (646309, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (47, 1), (646309, 1)] : List FactorBlock).map factorBlockValue).prod = 60753047 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2

#print axioms prime_lucas_60753047

end TotientTailPeriodKiller
end Erdos249257
