import Erdos249257.DiagonalPincerCertificates
import Erdos249257.DiagonalPincerPrimeCertificates.Prime1732632480223

/-! A bounded Lucas certificate for one t=41 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_6930529920893 : Nat.Prime 6930529920893 := by
  have hfermat : (2 : ZMod 6930529920893) ^ (6930529920893 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (2 : ZMod 6930529920893) ^ ((6930529920893 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (2 : ZMod 6930529920893) ^ ((6930529920893 - 1) / 1732632480223) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 6930529920893 (2 : ZMod 6930529920893)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (1732632480223, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (1732632480223, 1)] : List FactorBlock).map factorBlockValue).prod = 6930529920893 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · norm_num
      · exact prime_lucas_1732632480223) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · exact hfactor_0
    · exact hfactor_1

#print axioms prime_lucas_6930529920893

end TotientTailPeriodKiller
end Erdos249257
