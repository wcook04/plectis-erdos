import Erdos249257.DiagonalPincerCertificates
import Erdos249257.DiagonalPincerPrimeCertificates.Prime149951768321

/-! A bounded Lucas certificate for one t=32 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_299903536643 : Nat.Prime 299903536643 := by
  have hfermat : (2 : ZMod 299903536643) ^ (299903536643 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (2 : ZMod 299903536643) ^ ((299903536643 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (2 : ZMod 299903536643) ^ ((299903536643 - 1) / 149951768321) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 299903536643 (2 : ZMod 299903536643)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (149951768321, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (149951768321, 1)] : List FactorBlock).map factorBlockValue).prod = 299903536643 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · norm_num
      · exact prime_lucas_149951768321) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · exact hfactor_0
    · exact hfactor_1

#print axioms prime_lucas_299903536643

end TotientTailPeriodKiller
end Erdos249257
