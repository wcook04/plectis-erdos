import Erdos249257.DiagonalPincerCertificates
import Erdos249257.DiagonalPincerPrimeCertificates.Prime95942699

/-! A bounded Lucas certificate for one t=41 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_2302624777 : Nat.Prime 2302624777 := by
  have hfermat : (7 : ZMod 2302624777) ^ (2302624777 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (7 : ZMod 2302624777) ^ ((2302624777 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (7 : ZMod 2302624777) ^ ((2302624777 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (7 : ZMod 2302624777) ^ ((2302624777 - 1) / 95942699) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 2302624777 (7 : ZMod 2302624777)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (3, 1), (95942699, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (3, 1), (95942699, 1)] : List FactorBlock).map factorBlockValue).prod = 2302624777 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · norm_num
      · norm_num
      · exact prime_lucas_95942699) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2

#print axioms prime_lucas_2302624777

end TotientTailPeriodKiller
end Erdos249257
