import Erdos249257.DiagonalPincerCertificates

/-! A bounded Lucas certificate for one t=43 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_15015387713309 : Nat.Prime 15015387713309 := by
  have hfermat : (2 : ZMod 15015387713309) ^ (15015387713309 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (2 : ZMod 15015387713309) ^ ((15015387713309 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (2 : ZMod 15015387713309) ^ ((15015387713309 - 1) / 103) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (2 : ZMod 15015387713309) ^ ((15015387713309 - 1) / 3529) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (2 : ZMod 15015387713309) ^ ((15015387713309 - 1) / 10327321) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 15015387713309 (2 : ZMod 15015387713309)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (103, 1), (3529, 1), (10327321, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (103, 1), (3529, 1), (10327321, 1)] : List FactorBlock).map factorBlockValue).prod = 15015387713309 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · norm_num) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3

#print axioms prime_lucas_15015387713309

end TotientTailPeriodKiller
end Erdos249257
