import Erdos249257.DiagonalPincerPrimeCertificates.ClosureT64.Support
import Erdos249257.DiagonalPincerPrimeCertificates.ClosureT64.Level2A
import Erdos249257.DiagonalPincerPrimeCertificates.ClosureT64.Level2B

/-!
# ClosureT64 dependency level 3

Generated deterministically by `scripts/shard_closure_t64.py`; proof bodies are preserved verbatim from the original monolith.
-/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

theorem prime_lucas_1091237183384554093 : Nat.Prime 1091237183384554093 := by
  have hfermat : (2 : ZMod 1091237183384554093) ^ (1091237183384554093 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (2 : ZMod 1091237183384554093) ^ ((1091237183384554093 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (2 : ZMod 1091237183384554093) ^ ((1091237183384554093 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (2 : ZMod 1091237183384554093) ^ ((1091237183384554093 - 1) / 107) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (2 : ZMod 1091237183384554093) ^ ((1091237183384554093 - 1) / 167) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_4 : (2 : ZMod 1091237183384554093) ^ ((1091237183384554093 - 1) / 5089061052589) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 1091237183384554093 (2 : ZMod 1091237183384554093)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (107, 1), (167, 1), (5089061052589, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (107, 1), (167, 1), (5089061052589, 1)] : List FactorBlock).map factorBlockValue).prod = 1091237183384554093 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · exact prime_lucas_5089061052589) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4
theorem prime_lucas_11521489571681101 : Nat.Prime 11521489571681101 := by
  have hfermat : (6 : ZMod 11521489571681101) ^ (11521489571681101 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (6 : ZMod 11521489571681101) ^ ((11521489571681101 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (6 : ZMod 11521489571681101) ^ ((11521489571681101 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (6 : ZMod 11521489571681101) ^ ((11521489571681101 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (6 : ZMod 11521489571681101) ^ ((11521489571681101 - 1) / 11) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_4 : (6 : ZMod 11521489571681101) ^ ((11521489571681101 - 1) / 3491360476267) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 11521489571681101 (6 : ZMod 11521489571681101)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (5, 2), (11, 1), (3491360476267, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (5, 2), (11, 1), (3491360476267, 1)] : List FactorBlock).map factorBlockValue).prod = 11521489571681101 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · exact prime_lucas_3491360476267) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4
theorem prime_lucas_12166619164817616699203 : Nat.Prime 12166619164817616699203 := by
  have hfermat : (2 : ZMod 12166619164817616699203) ^ (12166619164817616699203 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (2 : ZMod 12166619164817616699203) ^ ((12166619164817616699203 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (2 : ZMod 12166619164817616699203) ^ ((12166619164817616699203 - 1) / 2659) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (2 : ZMod 12166619164817616699203) ^ ((12166619164817616699203 - 1) / 2797) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (2 : ZMod 12166619164817616699203) ^ ((12166619164817616699203 - 1) / 817954441114487) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 12166619164817616699203 (2 : ZMod 12166619164817616699203)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (2659, 1), (2797, 1), (817954441114487, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (2659, 1), (2797, 1), (817954441114487, 1)] : List FactorBlock).map factorBlockValue).prod = 12166619164817616699203 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · exact prime_lucas_817954441114487) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
theorem prime_lucas_127937752325444133529 : Nat.Prime 127937752325444133529 := by
  have hfermat : (11 : ZMod 127937752325444133529) ^ (127937752325444133529 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (11 : ZMod 127937752325444133529) ^ ((127937752325444133529 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (11 : ZMod 127937752325444133529) ^ ((127937752325444133529 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (11 : ZMod 127937752325444133529) ^ ((127937752325444133529 - 1) / 17) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (11 : ZMod 127937752325444133529) ^ ((127937752325444133529 - 1) / 19) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_4 : (11 : ZMod 127937752325444133529) ^ ((127937752325444133529 - 1) / 127) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_5 : (11 : ZMod 127937752325444133529) ^ ((127937752325444133529 - 1) / 129951480466757) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 127937752325444133529 (11 : ZMod 127937752325444133529)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (3, 1), (17, 1), (19, 1), (127, 1), (129951480466757, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (3, 1), (17, 1), (19, 1), (127, 1), (129951480466757, 1)] : List FactorBlock).map factorBlockValue).prod = 127937752325444133529 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · exact prime_lucas_129951480466757) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4
    · exact hfactor_5
theorem prime_lucas_1496172945001888482463 : Nat.Prime 1496172945001888482463 := by
  have hfermat : (3 : ZMod 1496172945001888482463) ^ (1496172945001888482463 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (3 : ZMod 1496172945001888482463) ^ ((1496172945001888482463 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (3 : ZMod 1496172945001888482463) ^ ((1496172945001888482463 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (3 : ZMod 1496172945001888482463) ^ ((1496172945001888482463 - 1) / 7) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (3 : ZMod 1496172945001888482463) ^ ((1496172945001888482463 - 1) / 11874388452395940337) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 1496172945001888482463 (3 : ZMod 1496172945001888482463)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 2), (7, 1), (11874388452395940337, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 2), (7, 1), (11874388452395940337, 1)] : List FactorBlock).map factorBlockValue).prod = 1496172945001888482463 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · exact prime_lucas_11874388452395940337) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
theorem prime_lucas_150923315950818371 : Nat.Prime 150923315950818371 := by
  have hfermat : (2 : ZMod 150923315950818371) ^ (150923315950818371 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (2 : ZMod 150923315950818371) ^ ((150923315950818371 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (2 : ZMod 150923315950818371) ^ ((150923315950818371 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (2 : ZMod 150923315950818371) ^ ((150923315950818371 - 1) / 15092331595081837) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 150923315950818371 (2 : ZMod 150923315950818371)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 1), (15092331595081837, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 1), (15092331595081837, 1)] : List FactorBlock).map factorBlockValue).prod = 150923315950818371 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · norm_num
      · norm_num
      · exact prime_lucas_15092331595081837) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
theorem prime_lucas_19447760641101259799 : Nat.Prime 19447760641101259799 := by
  have hfermat : (13 : ZMod 19447760641101259799) ^ (19447760641101259799 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (13 : ZMod 19447760641101259799) ^ ((19447760641101259799 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (13 : ZMod 19447760641101259799) ^ ((19447760641101259799 - 1) / 9723880320550629899) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 19447760641101259799 (13 : ZMod 19447760641101259799)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (9723880320550629899, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (9723880320550629899, 1)] : List FactorBlock).map factorBlockValue).prod = 19447760641101259799 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · norm_num
      · exact prime_lucas_9723880320550629899) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
theorem prime_lucas_19550394952257311 : Nat.Prime 19550394952257311 := by
  have hfermat : (7 : ZMod 19550394952257311) ^ (19550394952257311 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (7 : ZMod 19550394952257311) ^ ((19550394952257311 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (7 : ZMod 19550394952257311) ^ ((19550394952257311 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (7 : ZMod 19550394952257311) ^ ((19550394952257311 - 1) / 67) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (7 : ZMod 19550394952257311) ^ ((19550394952257311 - 1) / 29179693958593) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 19550394952257311 (7 : ZMod 19550394952257311)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 1), (67, 1), (29179693958593, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 1), (67, 1), (29179693958593, 1)] : List FactorBlock).map factorBlockValue).prod = 19550394952257311 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · exact prime_lucas_29179693958593) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
theorem prime_lucas_288835808679779267 : Nat.Prime 288835808679779267 := by
  have hfermat : (2 : ZMod 288835808679779267) ^ (288835808679779267 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (2 : ZMod 288835808679779267) ^ ((288835808679779267 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (2 : ZMod 288835808679779267) ^ ((288835808679779267 - 1) / 144417904339889633) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 288835808679779267 (2 : ZMod 288835808679779267)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (144417904339889633, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (144417904339889633, 1)] : List FactorBlock).map factorBlockValue).prod = 288835808679779267 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · norm_num
      · exact prime_lucas_144417904339889633) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
theorem prime_lucas_3000422669393 : Nat.Prime 3000422669393 := by
  have hfermat : (3 : ZMod 3000422669393) ^ (3000422669393 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (3 : ZMod 3000422669393) ^ ((3000422669393 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (3 : ZMod 3000422669393) ^ ((3000422669393 - 1) / 187526416837) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 3000422669393 (3 : ZMod 3000422669393)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 4), (187526416837, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 4), (187526416837, 1)] : List FactorBlock).map factorBlockValue).prod = 3000422669393 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · norm_num
      · exact prime_lucas_187526416837) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
theorem prime_lucas_322270629346999284871 : Nat.Prime 322270629346999284871 := by
  have hfermat : (3 : ZMod 322270629346999284871) ^ (322270629346999284871 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (3 : ZMod 322270629346999284871) ^ ((322270629346999284871 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (3 : ZMod 322270629346999284871) ^ ((322270629346999284871 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (3 : ZMod 322270629346999284871) ^ ((322270629346999284871 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (3 : ZMod 322270629346999284871) ^ ((322270629346999284871 - 1) / 32939) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_4 : (3 : ZMod 322270629346999284871) ^ ((322270629346999284871 - 1) / 326128732249511) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 322270629346999284871 (3 : ZMod 322270629346999284871)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (5, 1), (32939, 1), (326128732249511, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (5, 1), (32939, 1), (326128732249511, 1)] : List FactorBlock).map factorBlockValue).prod = 322270629346999284871 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · exact prime_lucas_326128732249511) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4
theorem prime_lucas_3921026324879 : Nat.Prime 3921026324879 := by
  have hfermat : (11 : ZMod 3921026324879) ^ (3921026324879 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (11 : ZMod 3921026324879) ^ ((3921026324879 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (11 : ZMod 3921026324879) ^ ((3921026324879 - 1) / 13) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (11 : ZMod 3921026324879) ^ ((3921026324879 - 1) / 150808704803) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 3921026324879 (11 : ZMod 3921026324879)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (13, 1), (150808704803, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (13, 1), (150808704803, 1)] : List FactorBlock).map factorBlockValue).prod = 3921026324879 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · norm_num
      · norm_num
      · exact prime_lucas_150808704803) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
theorem prime_lucas_40456576747427 : Nat.Prime 40456576747427 := by
  have hfermat : (2 : ZMod 40456576747427) ^ (40456576747427 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (2 : ZMod 40456576747427) ^ ((40456576747427 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (2 : ZMod 40456576747427) ^ ((40456576747427 - 1) / 7) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (2 : ZMod 40456576747427) ^ ((40456576747427 - 1) / 2889755481959) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 40456576747427 (2 : ZMod 40456576747427)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (7, 1), (2889755481959, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (7, 1), (2889755481959, 1)] : List FactorBlock).map factorBlockValue).prod = 40456576747427 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · norm_num
      · norm_num
      · exact prime_lucas_2889755481959) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
theorem prime_lucas_460540872544088591 : Nat.Prime 460540872544088591 := by
  have hfermat : (13 : ZMod 460540872544088591) ^ (460540872544088591 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (13 : ZMod 460540872544088591) ^ ((460540872544088591 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (13 : ZMod 460540872544088591) ^ ((460540872544088591 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (13 : ZMod 460540872544088591) ^ ((460540872544088591 - 1) / 16901) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (13 : ZMod 460540872544088591) ^ ((460540872544088591 - 1) / 2724932681759) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 460540872544088591 (13 : ZMod 460540872544088591)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 1), (16901, 1), (2724932681759, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 1), (16901, 1), (2724932681759, 1)] : List FactorBlock).map factorBlockValue).prod = 460540872544088591 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · exact prime_lucas_2724932681759) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
theorem prime_lucas_490161250177302761 : Nat.Prime 490161250177302761 := by
  have hfermat : (3 : ZMod 490161250177302761) ^ (490161250177302761 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (3 : ZMod 490161250177302761) ^ ((490161250177302761 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (3 : ZMod 490161250177302761) ^ ((490161250177302761 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (3 : ZMod 490161250177302761) ^ ((490161250177302761 - 1) / 7) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (3 : ZMod 490161250177302761) ^ ((490161250177302761 - 1) / 1750575893490367) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 490161250177302761 (3 : ZMod 490161250177302761)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (5, 1), (7, 1), (1750575893490367, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (5, 1), (7, 1), (1750575893490367, 1)] : List FactorBlock).map factorBlockValue).prod = 490161250177302761 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · exact prime_lucas_1750575893490367) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
theorem prime_lucas_6893684455410042376159543 : Nat.Prime 6893684455410042376159543 := by
  have hfermat : (5 : ZMod 6893684455410042376159543) ^ (6893684455410042376159543 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (5 : ZMod 6893684455410042376159543) ^ ((6893684455410042376159543 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (5 : ZMod 6893684455410042376159543) ^ ((6893684455410042376159543 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (5 : ZMod 6893684455410042376159543) ^ ((6893684455410042376159543 - 1) / 7) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (5 : ZMod 6893684455410042376159543) ^ ((6893684455410042376159543 - 1) / 164135344176429580384751) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 6893684455410042376159543 (5 : ZMod 6893684455410042376159543)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (7, 1), (164135344176429580384751, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (7, 1), (164135344176429580384751, 1)] : List FactorBlock).map factorBlockValue).prod = 6893684455410042376159543 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · exact prime_lucas_164135344176429580384751) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
theorem prime_lucas_885441286927427630453 : Nat.Prime 885441286927427630453 := by
  have hfermat : (2 : ZMod 885441286927427630453) ^ (885441286927427630453 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (2 : ZMod 885441286927427630453) ^ ((885441286927427630453 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (2 : ZMod 885441286927427630453) ^ ((885441286927427630453 - 1) / 13) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (2 : ZMod 885441286927427630453) ^ ((885441286927427630453 - 1) / 61) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (2 : ZMod 885441286927427630453) ^ ((885441286927427630453 - 1) / 3347) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_4 : (2 : ZMod 885441286927427630453) ^ ((885441286927427630453 - 1) / 83400926968103) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 885441286927427630453 (2 : ZMod 885441286927427630453)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (13, 1), (61, 1), (3347, 1), (83400926968103, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (13, 1), (61, 1), (3347, 1), (83400926968103, 1)] : List FactorBlock).map factorBlockValue).prod = 885441286927427630453 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · exact prime_lucas_83400926968103) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4
theorem prime_lucas_9031463968866551 : Nat.Prime 9031463968866551 := by
  have hfermat : (7 : ZMod 9031463968866551) ^ (9031463968866551 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (7 : ZMod 9031463968866551) ^ ((9031463968866551 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (7 : ZMod 9031463968866551) ^ ((9031463968866551 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (7 : ZMod 9031463968866551) ^ ((9031463968866551 - 1) / 457) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (7 : ZMod 9031463968866551) ^ ((9031463968866551 - 1) / 395250064283) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 9031463968866551 (7 : ZMod 9031463968866551)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 2), (457, 1), (395250064283, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 2), (457, 1), (395250064283, 1)] : List FactorBlock).map factorBlockValue).prod = 9031463968866551 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · exact prime_lucas_395250064283) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
theorem prime_lucas_9381625142821823891 : Nat.Prime 9381625142821823891 := by
  have hfermat : (2 : ZMod 9381625142821823891) ^ (9381625142821823891 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (2 : ZMod 9381625142821823891) ^ ((9381625142821823891 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (2 : ZMod 9381625142821823891) ^ ((9381625142821823891 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (2 : ZMod 9381625142821823891) ^ ((9381625142821823891 - 1) / 938162514282182389) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 9381625142821823891 (2 : ZMod 9381625142821823891)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 1), (938162514282182389, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 1), (938162514282182389, 1)] : List FactorBlock).map factorBlockValue).prod = 9381625142821823891 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · norm_num
      · norm_num
      · exact prime_lucas_938162514282182389) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2

end TotientTailPeriodKiller
end Erdos249257
