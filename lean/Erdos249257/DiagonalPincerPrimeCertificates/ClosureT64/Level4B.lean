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

theorem prime_lucas_3133899934268755463899 : Nat.Prime 3133899934268755463899 := by
  have hfermat : (3 : ZMod 3133899934268755463899) ^ (3133899934268755463899 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (3 : ZMod 3133899934268755463899) ^ ((3133899934268755463899 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (3 : ZMod 3133899934268755463899) ^ ((3133899934268755463899 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (3 : ZMod 3133899934268755463899) ^ ((3133899934268755463899 - 1) / 151) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (3 : ZMod 3133899934268755463899) ^ ((3133899934268755463899 - 1) / 383) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_4 : (3 : ZMod 3133899934268755463899) ^ ((3133899934268755463899 - 1) / 9031463968866551) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 3133899934268755463899 (3 : ZMod 3133899934268755463899)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (151, 1), (383, 1), (9031463968866551, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (151, 1), (383, 1), (9031463968866551, 1)] : List FactorBlock).map factorBlockValue).prod = 3133899934268755463899 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · exact prime_lucas_9031463968866551) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4
theorem prime_lucas_79065530937124474520923 : Nat.Prime 79065530937124474520923 := by
  have hfermat : (2 : ZMod 79065530937124474520923) ^ (79065530937124474520923 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (2 : ZMod 79065530937124474520923) ^ ((79065530937124474520923 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (2 : ZMod 79065530937124474520923) ^ ((79065530937124474520923 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (2 : ZMod 79065530937124474520923) ^ ((79065530937124474520923 - 1) / 103) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (2 : ZMod 79065530937124474520923) ^ ((79065530937124474520923 - 1) / 127937752325444133529) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 79065530937124474520923 (2 : ZMod 79065530937124474520923)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (103, 1), (127937752325444133529, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (103, 1), (127937752325444133529, 1)] : List FactorBlock).map factorBlockValue).prod = 79065530937124474520923 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · exact prime_lucas_127937752325444133529) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3

end TotientTailPeriodKiller
end Erdos249257
