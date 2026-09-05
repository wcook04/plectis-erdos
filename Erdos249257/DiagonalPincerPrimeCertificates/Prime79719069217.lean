import Erdos249257.DiagonalPincerCertificates
import Erdos249257.DiagonalPincerPrimeCertificates.Prime830406971

/-! A bounded Lucas certificate for one t=37 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_79719069217 : Nat.Prime 79719069217 := by
  have hfermat : (10 : ZMod 79719069217) ^ (79719069217 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (10 : ZMod 79719069217) ^ ((79719069217 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (10 : ZMod 79719069217) ^ ((79719069217 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (10 : ZMod 79719069217) ^ ((79719069217 - 1) / 830406971) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 79719069217 (10 : ZMod 79719069217)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 5), (3, 1), (830406971, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 5), (3, 1), (830406971, 1)] : List FactorBlock).map factorBlockValue).prod = 79719069217 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · norm_num
      · norm_num
      · exact prime_lucas_830406971) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2

#print axioms prime_lucas_79719069217

end TotientTailPeriodKiller
end Erdos249257
