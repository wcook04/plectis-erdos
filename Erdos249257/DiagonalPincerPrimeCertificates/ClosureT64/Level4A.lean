import Erdos249257.DiagonalPincerPrimeCertificates.ClosureT64.Support
import Erdos249257.DiagonalPincerPrimeCertificates.ClosureT64.Level3A

/-!
# ClosureT64 dependency level 4

Generated deterministically by `scripts/shard_closure_t64.py`; proof bodies are preserved verbatim from the original monolith.
-/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

theorem prime_lucas_2078214060642768968671 : Nat.Prime 2078214060642768968671 := by
  have hfermat : (11 : ZMod 2078214060642768968671) ^ (2078214060642768968671 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (11 : ZMod 2078214060642768968671) ^ ((2078214060642768968671 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (11 : ZMod 2078214060642768968671) ^ ((2078214060642768968671 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (11 : ZMod 2078214060642768968671) ^ ((2078214060642768968671 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (11 : ZMod 2078214060642768968671) ^ ((2078214060642768968671 - 1) / 17) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_4 : (11 : ZMod 2078214060642768968671) ^ ((2078214060642768968671 - 1) / 150923315950818371) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 2078214060642768968671 (11 : ZMod 2078214060642768968671)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 4), (5, 1), (17, 1), (150923315950818371, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 4), (5, 1), (17, 1), (150923315950818371, 1)] : List FactorBlock).map factorBlockValue).prod = 2078214060642768968671 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · exact prime_lucas_150923315950818371) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4
theorem prime_lucas_2993786679309599 : Nat.Prime 2993786679309599 := by
  have hfermat : (17 : ZMod 2993786679309599) ^ (2993786679309599 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (17 : ZMod 2993786679309599) ^ ((2993786679309599 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (17 : ZMod 2993786679309599) ^ ((2993786679309599 - 1) / 37) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (17 : ZMod 2993786679309599) ^ ((2993786679309599 - 1) / 40456576747427) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 2993786679309599 (17 : ZMod 2993786679309599)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (37, 1), (40456576747427, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (37, 1), (40456576747427, 1)] : List FactorBlock).map factorBlockValue).prod = 2993786679309599 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · norm_num
      · norm_num
      · exact prime_lucas_40456576747427) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
theorem prime_lucas_39100789904514623 : Nat.Prime 39100789904514623 := by
  have hfermat : (5 : ZMod 39100789904514623) ^ (39100789904514623 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (5 : ZMod 39100789904514623) ^ ((39100789904514623 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (5 : ZMod 39100789904514623) ^ ((39100789904514623 - 1) / 19550394952257311) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 39100789904514623 (5 : ZMod 39100789904514623)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (19550394952257311, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (19550394952257311, 1)] : List FactorBlock).map factorBlockValue).prod = 39100789904514623 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · norm_num
      · exact prime_lucas_19550394952257311) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · exact hfactor_0
    · exact hfactor_1

end TotientTailPeriodKiller
end Erdos249257
