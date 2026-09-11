import Erdos249257.DiagonalPincerCertificates

/-! A bounded Lucas certificate for one t=29 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_46078157 : Nat.Prime 46078157 := by
  have hfermat : (2 : ZMod 46078157) ^ (46078157 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (2 : ZMod 46078157) ^ ((46078157 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (2 : ZMod 46078157) ^ ((46078157 - 1) / 11519539) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 46078157 (2 : ZMod 46078157)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (11519539, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (11519539, 1)] : List FactorBlock).map factorBlockValue).prod = 46078157 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · norm_num
      · norm_num) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · exact hfactor_0
    · exact hfactor_1

#print axioms prime_lucas_46078157

end TotientTailPeriodKiller
end Erdos249257
