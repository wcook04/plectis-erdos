import Erdos249257.DiagonalPincerPrimeCertificates.ClosureT64.Support
import Erdos249257.DiagonalPincerPrimeCertificates.ClosureT64.Level0A
import Erdos249257.DiagonalPincerPrimeCertificates.ClosureT64.Level1A
import Erdos249257.DiagonalPincerPrimeCertificates.ClosureT64.Level1B

/-!
# ClosureT64 dependency level 2

Generated deterministically by `scripts/shard_closure_t64.py`; proof bodies are preserved verbatim from the original monolith.
-/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

theorem prime_lucas_10166976687473210366869 : Nat.Prime 10166976687473210366869 := by
  have hfermat : (6 : ZMod 10166976687473210366869) ^ (10166976687473210366869 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (6 : ZMod 10166976687473210366869) ^ ((10166976687473210366869 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (6 : ZMod 10166976687473210366869) ^ ((10166976687473210366869 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (6 : ZMod 10166976687473210366869) ^ ((10166976687473210366869 - 1) / 11633107) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (6 : ZMod 10166976687473210366869) ^ ((10166976687473210366869 - 1) / 72830762864077) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 10166976687473210366869 (6 : ZMod 10166976687473210366869)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (11633107, 1), (72830762864077, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (11633107, 1), (72830762864077, 1)] : List FactorBlock).map factorBlockValue).prod = 10166976687473210366869 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · exact prime_lucas_72830762864077) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
theorem prime_lucas_10189408545301797546401 : Nat.Prime 10189408545301797546401 := by
  have hfermat : (3 : ZMod 10189408545301797546401) ^ (10189408545301797546401 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (3 : ZMod 10189408545301797546401) ^ ((10189408545301797546401 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (3 : ZMod 10189408545301797546401) ^ ((10189408545301797546401 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (3 : ZMod 10189408545301797546401) ^ ((10189408545301797546401 - 1) / 601) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (3 : ZMod 10189408545301797546401) ^ ((10189408545301797546401 - 1) / 39107) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_4 : (3 : ZMod 10189408545301797546401) ^ ((10189408545301797546401 - 1) / 541913556319) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 10189408545301797546401 (3 : ZMod 10189408545301797546401)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 5), (5, 2), (601, 1), (39107, 1), (541913556319, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 5), (5, 2), (601, 1), (39107, 1), (541913556319, 1)] : List FactorBlock).map factorBlockValue).prod = 10189408545301797546401 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · exact prime_lucas_541913556319) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4
theorem prime_lucas_1037009604451347647 : Nat.Prime 1037009604451347647 := by
  have hfermat : (7 : ZMod 1037009604451347647) ^ (1037009604451347647 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (7 : ZMod 1037009604451347647) ^ ((1037009604451347647 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (7 : ZMod 1037009604451347647) ^ ((1037009604451347647 - 1) / 7) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (7 : ZMod 1037009604451347647) ^ ((1037009604451347647 - 1) / 17929) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (7 : ZMod 1037009604451347647) ^ ((1037009604451347647 - 1) / 4131413609441) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 1037009604451347647 (7 : ZMod 1037009604451347647)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (7, 1), (17929, 1), (4131413609441, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (7, 1), (17929, 1), (4131413609441, 1)] : List FactorBlock).map factorBlockValue).prod = 1037009604451347647 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · exact prime_lucas_4131413609441) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
theorem prime_lucas_1135087761943573 : Nat.Prime 1135087761943573 := by
  have hfermat : (5 : ZMod 1135087761943573) ^ (1135087761943573 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (5 : ZMod 1135087761943573) ^ ((1135087761943573 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (5 : ZMod 1135087761943573) ^ ((1135087761943573 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (5 : ZMod 1135087761943573) ^ ((1135087761943573 - 1) / 94590646828631) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 1135087761943573 (5 : ZMod 1135087761943573)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (94590646828631, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (94590646828631, 1)] : List FactorBlock).map factorBlockValue).prod = 1135087761943573 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · norm_num
      · norm_num
      · exact prime_lucas_94590646828631) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
theorem prime_lucas_114738249096931 : Nat.Prime 114738249096931 := by
  have hfermat : (3 : ZMod 114738249096931) ^ (114738249096931 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (3 : ZMod 114738249096931) ^ ((114738249096931 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (3 : ZMod 114738249096931) ^ ((114738249096931 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (3 : ZMod 114738249096931) ^ ((114738249096931 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (3 : ZMod 114738249096931) ^ ((114738249096931 - 1) / 29) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_4 : (3 : ZMod 114738249096931) ^ ((114738249096931 - 1) / 337) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_5 : (3 : ZMod 114738249096931) ^ ((114738249096931 - 1) / 391344347) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 114738249096931 (3 : ZMod 114738249096931)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (5, 1), (29, 1), (337, 1), (391344347, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (5, 1), (29, 1), (337, 1), (391344347, 1)] : List FactorBlock).map factorBlockValue).prod = 114738249096931 - 1 by
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
      · exact prime_lucas_391344347) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4
    · exact hfactor_5
theorem prime_lucas_1170561271388932938130061 : Nat.Prime 1170561271388932938130061 := by
  have hfermat : (2 : ZMod 1170561271388932938130061) ^ (1170561271388932938130061 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (2 : ZMod 1170561271388932938130061) ^ ((1170561271388932938130061 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (2 : ZMod 1170561271388932938130061) ^ ((1170561271388932938130061 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (2 : ZMod 1170561271388932938130061) ^ ((1170561271388932938130061 - 1) / 58528063569446646906503) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 1170561271388932938130061 (2 : ZMod 1170561271388932938130061)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (5, 1), (58528063569446646906503, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (5, 1), (58528063569446646906503, 1)] : List FactorBlock).map factorBlockValue).prod = 1170561271388932938130061 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · norm_num
      · norm_num
      · exact prime_lucas_58528063569446646906503) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
theorem prime_lucas_120782150239507 : Nat.Prime 120782150239507 := by
  have hfermat : (3 : ZMod 120782150239507) ^ (120782150239507 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (3 : ZMod 120782150239507) ^ ((120782150239507 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (3 : ZMod 120782150239507) ^ ((120782150239507 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (3 : ZMod 120782150239507) ^ ((120782150239507 - 1) / 7) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (3 : ZMod 120782150239507) ^ ((120782150239507 - 1) / 2875765481893) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 120782150239507 (3 : ZMod 120782150239507)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (7, 1), (2875765481893, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (7, 1), (2875765481893, 1)] : List FactorBlock).map factorBlockValue).prod = 120782150239507 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · exact prime_lucas_2875765481893) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
theorem prime_lucas_128089586576687136241751 : Nat.Prime 128089586576687136241751 := by
  have hfermat : (11 : ZMod 128089586576687136241751) ^ (128089586576687136241751 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (11 : ZMod 128089586576687136241751) ^ ((128089586576687136241751 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (11 : ZMod 128089586576687136241751) ^ ((128089586576687136241751 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (11 : ZMod 128089586576687136241751) ^ ((128089586576687136241751 - 1) / 7) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (11 : ZMod 128089586576687136241751) ^ ((128089586576687136241751 - 1) / 13) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_4 : (11 : ZMod 128089586576687136241751) ^ ((128089586576687136241751 - 1) / 5630311497876357637) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 128089586576687136241751 (11 : ZMod 128089586576687136241751)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 3), (7, 1), (13, 1), (5630311497876357637, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 3), (7, 1), (13, 1), (5630311497876357637, 1)] : List FactorBlock).map factorBlockValue).prod = 128089586576687136241751 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · exact prime_lucas_5630311497876357637) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4
theorem prime_lucas_1303240709915777 : Nat.Prime 1303240709915777 := by
  have hfermat : (3 : ZMod 1303240709915777) ^ (1303240709915777 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (3 : ZMod 1303240709915777) ^ ((1303240709915777 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (3 : ZMod 1303240709915777) ^ ((1303240709915777 - 1) / 10181568046217) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 1303240709915777 (3 : ZMod 1303240709915777)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 7), (10181568046217, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 7), (10181568046217, 1)] : List FactorBlock).map factorBlockValue).prod = 1303240709915777 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · norm_num
      · exact prime_lucas_10181568046217) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
theorem prime_lucas_13094658639069053 : Nat.Prime 13094658639069053 := by
  have hfermat : (2 : ZMod 13094658639069053) ^ (13094658639069053 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (2 : ZMod 13094658639069053) ^ ((13094658639069053 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (2 : ZMod 13094658639069053) ^ ((13094658639069053 - 1) / 2341) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (2 : ZMod 13094658639069053) ^ ((13094658639069053 - 1) / 1398404382643) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 13094658639069053 (2 : ZMod 13094658639069053)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (2341, 1), (1398404382643, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (2341, 1), (1398404382643, 1)] : List FactorBlock).map factorBlockValue).prod = 13094658639069053 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · norm_num
      · norm_num
      · exact prime_lucas_1398404382643) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
theorem prime_lucas_13740066434843123 : Nat.Prime 13740066434843123 := by
  have hfermat : (2 : ZMod 13740066434843123) ^ (13740066434843123 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (2 : ZMod 13740066434843123) ^ ((13740066434843123 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (2 : ZMod 13740066434843123) ^ ((13740066434843123 - 1) / 11) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (2 : ZMod 13740066434843123) ^ ((13740066434843123 - 1) / 53) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (2 : ZMod 13740066434843123) ^ ((13740066434843123 - 1) / 157) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_4 : (2 : ZMod 13740066434843123) ^ ((13740066434843123 - 1) / 75056901131) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 13740066434843123 (2 : ZMod 13740066434843123)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (11, 1), (53, 1), (157, 1), (75056901131, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (11, 1), (53, 1), (157, 1), (75056901131, 1)] : List FactorBlock).map factorBlockValue).prod = 13740066434843123 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · exact prime_lucas_75056901131) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4
theorem prime_lucas_14380716957057989357 : Nat.Prime 14380716957057989357 := by
  have hfermat : (2 : ZMod 14380716957057989357) ^ (14380716957057989357 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (2 : ZMod 14380716957057989357) ^ ((14380716957057989357 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (2 : ZMod 14380716957057989357) ^ ((14380716957057989357 - 1) / 7) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (2 : ZMod 14380716957057989357) ^ ((14380716957057989357 - 1) / 13) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (2 : ZMod 14380716957057989357) ^ ((14380716957057989357 - 1) / 4099) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_4 : (2 : ZMod 14380716957057989357) ^ ((14380716957057989357 - 1) / 9638317679371) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 14380716957057989357 (2 : ZMod 14380716957057989357)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (7, 1), (13, 1), (4099, 1), (9638317679371, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (7, 1), (13, 1), (4099, 1), (9638317679371, 1)] : List FactorBlock).map factorBlockValue).prod = 14380716957057989357 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · exact prime_lucas_9638317679371) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4
theorem prime_lucas_150808704803 : Nat.Prime 150808704803 := by
  have hfermat : (2 : ZMod 150808704803) ^ (150808704803 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (2 : ZMod 150808704803) ^ ((150808704803 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (2 : ZMod 150808704803) ^ ((150808704803 - 1) / 7) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (2 : ZMod 150808704803) ^ ((150808704803 - 1) / 10772050343) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 150808704803 (2 : ZMod 150808704803)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (7, 1), (10772050343, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (7, 1), (10772050343, 1)] : List FactorBlock).map factorBlockValue).prod = 150808704803 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · norm_num
      · norm_num
      · exact prime_lucas_10772050343) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
theorem prime_lucas_15092331595081837 : Nat.Prime 15092331595081837 := by
  have hfermat : (2 : ZMod 15092331595081837) ^ (15092331595081837 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (2 : ZMod 15092331595081837) ^ ((15092331595081837 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (2 : ZMod 15092331595081837) ^ ((15092331595081837 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (2 : ZMod 15092331595081837) ^ ((15092331595081837 - 1) / 1257694299590153) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 15092331595081837 (2 : ZMod 15092331595081837)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (1257694299590153, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (1257694299590153, 1)] : List FactorBlock).map factorBlockValue).prod = 15092331595081837 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · norm_num
      · norm_num
      · exact prime_lucas_1257694299590153) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
theorem prime_lucas_1509852757849 : Nat.Prime 1509852757849 := by
  have hfermat : (13 : ZMod 1509852757849) ^ (1509852757849 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (13 : ZMod 1509852757849) ^ ((1509852757849 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (13 : ZMod 1509852757849) ^ ((1509852757849 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (13 : ZMod 1509852757849) ^ ((1509852757849 - 1) / 62910531577) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 1509852757849 (13 : ZMod 1509852757849)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (3, 1), (62910531577, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (3, 1), (62910531577, 1)] : List FactorBlock).map factorBlockValue).prod = 1509852757849 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · norm_num
      · norm_num
      · exact prime_lucas_62910531577) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
theorem prime_lucas_164135344176429580384751 : Nat.Prime 164135344176429580384751 := by
  have hfermat : (73 : ZMod 164135344176429580384751) ^ (164135344176429580384751 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (73 : ZMod 164135344176429580384751) ^ ((164135344176429580384751 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (73 : ZMod 164135344176429580384751) ^ ((164135344176429580384751 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (73 : ZMod 164135344176429580384751) ^ ((164135344176429580384751 - 1) / 656541376705718321539) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 164135344176429580384751 (73 : ZMod 164135344176429580384751)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 3), (656541376705718321539, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 3), (656541376705718321539, 1)] : List FactorBlock).map factorBlockValue).prod = 164135344176429580384751 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · norm_num
      · norm_num
      · exact prime_lucas_656541376705718321539) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
theorem prime_lucas_18124110366539 : Nat.Prime 18124110366539 := by
  have hfermat : (2 : ZMod 18124110366539) ^ (18124110366539 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (2 : ZMod 18124110366539) ^ ((18124110366539 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (2 : ZMod 18124110366539) ^ ((18124110366539 - 1) / 11) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (2 : ZMod 18124110366539) ^ ((18124110366539 - 1) / 113) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (2 : ZMod 18124110366539) ^ ((18124110366539 - 1) / 7290470783) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 18124110366539 (2 : ZMod 18124110366539)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (11, 1), (113, 1), (7290470783, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (11, 1), (113, 1), (7290470783, 1)] : List FactorBlock).map factorBlockValue).prod = 18124110366539 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · exact prime_lucas_7290470783) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
theorem prime_lucas_18264674580043 : Nat.Prime 18264674580043 := by
  have hfermat : (5 : ZMod 18264674580043) ^ (18264674580043 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (5 : ZMod 18264674580043) ^ ((18264674580043 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (5 : ZMod 18264674580043) ^ ((18264674580043 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (5 : ZMod 18264674580043) ^ ((18264674580043 - 1) / 11) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (5 : ZMod 18264674580043) ^ ((18264674580043 - 1) / 25157953967) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 18264674580043 (5 : ZMod 18264674580043)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (11, 2), (25157953967, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (11, 2), (25157953967, 1)] : List FactorBlock).map factorBlockValue).prod = 18264674580043 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · exact prime_lucas_25157953967) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
theorem prime_lucas_1872381924194871065261 : Nat.Prime 1872381924194871065261 := by
  have hfermat : (2 : ZMod 1872381924194871065261) ^ (1872381924194871065261 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (2 : ZMod 1872381924194871065261) ^ ((1872381924194871065261 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (2 : ZMod 1872381924194871065261) ^ ((1872381924194871065261 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (2 : ZMod 1872381924194871065261) ^ ((1872381924194871065261 - 1) / 1459) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (2 : ZMod 1872381924194871065261) ^ ((1872381924194871065261 - 1) / 12927743) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_4 : (2 : ZMod 1872381924194871065261) ^ ((1872381924194871065261 - 1) / 4963481899) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 1872381924194871065261 (2 : ZMod 1872381924194871065261)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (5, 1), (1459, 1), (12927743, 1), (4963481899, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (5, 1), (1459, 1), (12927743, 1), (4963481899, 1)] : List FactorBlock).map factorBlockValue).prod = 1872381924194871065261 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · exact prime_lucas_4963481899) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4
theorem prime_lucas_187526416837 : Nat.Prime 187526416837 := by
  have hfermat : (2 : ZMod 187526416837) ^ (187526416837 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (2 : ZMod 187526416837) ^ ((187526416837 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (2 : ZMod 187526416837) ^ ((187526416837 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (2 : ZMod 187526416837) ^ ((187526416837 - 1) / 11) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (2 : ZMod 187526416837) ^ ((187526416837 - 1) / 1420654673) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 187526416837 (2 : ZMod 187526416837)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (11, 1), (1420654673, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (11, 1), (1420654673, 1)] : List FactorBlock).map factorBlockValue).prod = 187526416837 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · exact prime_lucas_1420654673) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
theorem prime_lucas_19129904347197510533 : Nat.Prime 19129904347197510533 := by
  have hfermat : (2 : ZMod 19129904347197510533) ^ (19129904347197510533 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (2 : ZMod 19129904347197510533) ^ ((19129904347197510533 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (2 : ZMod 19129904347197510533) ^ ((19129904347197510533 - 1) / 357613) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (2 : ZMod 19129904347197510533) ^ ((19129904347197510533 - 1) / 13373328393541) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 19129904347197510533 (2 : ZMod 19129904347197510533)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (357613, 1), (13373328393541, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (357613, 1), (13373328393541, 1)] : List FactorBlock).map factorBlockValue).prod = 19129904347197510533 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · norm_num
      · norm_num
      · exact prime_lucas_13373328393541) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
theorem prime_lucas_1926717003131 : Nat.Prime 1926717003131 := by
  have hfermat : (2 : ZMod 1926717003131) ^ (1926717003131 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (2 : ZMod 1926717003131) ^ ((1926717003131 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (2 : ZMod 1926717003131) ^ ((1926717003131 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (2 : ZMod 1926717003131) ^ ((1926717003131 - 1) / 47) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (2 : ZMod 1926717003131) ^ ((1926717003131 - 1) / 4099397879) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 1926717003131 (2 : ZMod 1926717003131)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 1), (47, 1), (4099397879, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 1), (47, 1), (4099397879, 1)] : List FactorBlock).map factorBlockValue).prod = 1926717003131 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · exact prime_lucas_4099397879) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
theorem prime_lucas_19604484749 : Nat.Prime 19604484749 := by
  have hfermat : (2 : ZMod 19604484749) ^ (19604484749 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (2 : ZMod 19604484749) ^ ((19604484749 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (2 : ZMod 19604484749) ^ ((19604484749 - 1) / 4901121187) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 19604484749 (2 : ZMod 19604484749)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (4901121187, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (4901121187, 1)] : List FactorBlock).map factorBlockValue).prod = 19604484749 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · norm_num
      · exact prime_lucas_4901121187) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
theorem prime_lucas_2048408031805181 : Nat.Prime 2048408031805181 := by
  have hfermat : (2 : ZMod 2048408031805181) ^ (2048408031805181 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (2 : ZMod 2048408031805181) ^ ((2048408031805181 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (2 : ZMod 2048408031805181) ^ ((2048408031805181 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (2 : ZMod 2048408031805181) ^ ((2048408031805181 - 1) / 29) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (2 : ZMod 2048408031805181) ^ ((2048408031805181 - 1) / 27509) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_4 : (2 : ZMod 2048408031805181) ^ ((2048408031805181 - 1) / 128384819) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 2048408031805181 (2 : ZMod 2048408031805181)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (5, 1), (29, 1), (27509, 1), (128384819, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (5, 1), (29, 1), (27509, 1), (128384819, 1)] : List FactorBlock).map factorBlockValue).prod = 2048408031805181 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · exact prime_lucas_128384819) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4
theorem prime_lucas_2167308678465302048600113 : Nat.Prime 2167308678465302048600113 := by
  have hfermat : (10 : ZMod 2167308678465302048600113) ^ (2167308678465302048600113 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (10 : ZMod 2167308678465302048600113) ^ ((2167308678465302048600113 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (10 : ZMod 2167308678465302048600113) ^ ((2167308678465302048600113 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (10 : ZMod 2167308678465302048600113) ^ ((2167308678465302048600113 - 1) / 7) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (10 : ZMod 2167308678465302048600113) ^ ((2167308678465302048600113 - 1) / 1093) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_4 : (10 : ZMod 2167308678465302048600113) ^ ((2167308678465302048600113 - 1) / 33469) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_5 : (10 : ZMod 2167308678465302048600113) ^ ((2167308678465302048600113 - 1) / 58775636296717) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 2167308678465302048600113 (10 : ZMod 2167308678465302048600113)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 4), (3, 2), (7, 1), (1093, 1), (33469, 1), (58775636296717, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 4), (3, 2), (7, 1), (1093, 1), (33469, 1), (58775636296717, 1)] : List FactorBlock).map factorBlockValue).prod = 2167308678465302048600113 - 1 by
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
      · exact prime_lucas_58775636296717) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4
    · exact hfactor_5
theorem prime_lucas_22691823592049 : Nat.Prime 22691823592049 := by
  have hfermat : (3 : ZMod 22691823592049) ^ (22691823592049 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (3 : ZMod 22691823592049) ^ ((22691823592049 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (3 : ZMod 22691823592049) ^ ((22691823592049 - 1) / 13) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (3 : ZMod 22691823592049) ^ ((22691823592049 - 1) / 109095305731) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 22691823592049 (3 : ZMod 22691823592049)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 4), (13, 1), (109095305731, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 4), (13, 1), (109095305731, 1)] : List FactorBlock).map factorBlockValue).prod = 22691823592049 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · norm_num
      · norm_num
      · exact prime_lucas_109095305731) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
theorem prime_lucas_242634839 : Nat.Prime 242634839 := by
  have hfermat : (13 : ZMod 242634839) ^ (242634839 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (13 : ZMod 242634839) ^ ((242634839 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (13 : ZMod 242634839) ^ ((242634839 - 1) / 121317419) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 242634839 (13 : ZMod 242634839)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (121317419, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (121317419, 1)] : List FactorBlock).map factorBlockValue).prod = 242634839 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · norm_num
      · exact prime_lucas_121317419) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
theorem prime_lucas_25149189821625757991 : Nat.Prime 25149189821625757991 := by
  have hfermat : (11 : ZMod 25149189821625757991) ^ (25149189821625757991 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (11 : ZMod 25149189821625757991) ^ ((25149189821625757991 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (11 : ZMod 25149189821625757991) ^ ((25149189821625757991 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (11 : ZMod 25149189821625757991) ^ ((25149189821625757991 - 1) / 31) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (11 : ZMod 25149189821625757991) ^ ((25149189821625757991 - 1) / 8599) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_4 : (11 : ZMod 25149189821625757991) ^ ((25149189821625757991 - 1) / 9434401532671) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 25149189821625757991 (11 : ZMod 25149189821625757991)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 1), (31, 1), (8599, 1), (9434401532671, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 1), (31, 1), (8599, 1), (9434401532671, 1)] : List FactorBlock).map factorBlockValue).prod = 25149189821625757991 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · exact prime_lucas_9434401532671) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4
theorem prime_lucas_260609822486481386147 : Nat.Prime 260609822486481386147 := by
  have hfermat : (2 : ZMod 260609822486481386147) ^ (260609822486481386147 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (2 : ZMod 260609822486481386147) ^ ((260609822486481386147 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (2 : ZMod 260609822486481386147) ^ ((260609822486481386147 - 1) / 31) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (2 : ZMod 260609822486481386147) ^ ((260609822486481386147 - 1) / 8419) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (2 : ZMod 260609822486481386147) ^ ((260609822486481386147 - 1) / 499273575680357) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 260609822486481386147 (2 : ZMod 260609822486481386147)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (31, 1), (8419, 1), (499273575680357, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (31, 1), (8419, 1), (499273575680357, 1)] : List FactorBlock).map factorBlockValue).prod = 260609822486481386147 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · exact prime_lucas_499273575680357) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
theorem prime_lucas_2689475597297 : Nat.Prime 2689475597297 := by
  have hfermat : (3 : ZMod 2689475597297) ^ (2689475597297 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (3 : ZMod 2689475597297) ^ ((2689475597297 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (3 : ZMod 2689475597297) ^ ((2689475597297 - 1) / 733) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (3 : ZMod 2689475597297) ^ ((2689475597297 - 1) / 229320907) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 2689475597297 (3 : ZMod 2689475597297)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 4), (733, 1), (229320907, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 4), (733, 1), (229320907, 1)] : List FactorBlock).map factorBlockValue).prod = 2689475597297 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · norm_num
      · norm_num
      · exact prime_lucas_229320907) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
theorem prime_lucas_2817264174110839 : Nat.Prime 2817264174110839 := by
  have hfermat : (3 : ZMod 2817264174110839) ^ (2817264174110839 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (3 : ZMod 2817264174110839) ^ ((2817264174110839 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (3 : ZMod 2817264174110839) ^ ((2817264174110839 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (3 : ZMod 2817264174110839) ^ ((2817264174110839 - 1) / 136603) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (3 : ZMod 2817264174110839) ^ ((2817264174110839 - 1) / 1145763097) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 2817264174110839 (3 : ZMod 2817264174110839)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 2), (136603, 1), (1145763097, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 2), (136603, 1), (1145763097, 1)] : List FactorBlock).map factorBlockValue).prod = 2817264174110839 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · exact prime_lucas_1145763097) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
theorem prime_lucas_28578137980729 : Nat.Prime 28578137980729 := by
  have hfermat : (11 : ZMod 28578137980729) ^ (28578137980729 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (11 : ZMod 28578137980729) ^ ((28578137980729 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (11 : ZMod 28578137980729) ^ ((28578137980729 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (11 : ZMod 28578137980729) ^ ((28578137980729 - 1) / 7) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (11 : ZMod 28578137980729) ^ ((28578137980729 - 1) / 170107964171) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 28578137980729 (11 : ZMod 28578137980729)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (3, 1), (7, 1), (170107964171, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (3, 1), (7, 1), (170107964171, 1)] : List FactorBlock).map factorBlockValue).prod = 28578137980729 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · exact prime_lucas_170107964171) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
theorem prime_lucas_2901032068267 : Nat.Prime 2901032068267 := by
  have hfermat : (3 : ZMod 2901032068267) ^ (2901032068267 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (3 : ZMod 2901032068267) ^ ((2901032068267 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (3 : ZMod 2901032068267) ^ ((2901032068267 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (3 : ZMod 2901032068267) ^ ((2901032068267 - 1) / 53722816079) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 2901032068267 (3 : ZMod 2901032068267)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 3), (53722816079, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 3), (53722816079, 1)] : List FactorBlock).map factorBlockValue).prod = 2901032068267 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · norm_num
      · norm_num
      · exact prime_lucas_53722816079) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
theorem prime_lucas_3273120906190752319 : Nat.Prime 3273120906190752319 := by
  have hfermat : (3 : ZMod 3273120906190752319) ^ (3273120906190752319 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (3 : ZMod 3273120906190752319) ^ ((3273120906190752319 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (3 : ZMod 3273120906190752319) ^ ((3273120906190752319 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (3 : ZMod 3273120906190752319) ^ ((3273120906190752319 - 1) / 13) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (3 : ZMod 3273120906190752319) ^ ((3273120906190752319 - 1) / 41963088540907081) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 3273120906190752319 (3 : ZMod 3273120906190752319)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (13, 1), (41963088540907081, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (13, 1), (41963088540907081, 1)] : List FactorBlock).map factorBlockValue).prod = 3273120906190752319 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · exact prime_lucas_41963088540907081) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
theorem prime_lucas_328498717450075650878471 : Nat.Prime 328498717450075650878471 := by
  have hfermat : (7 : ZMod 328498717450075650878471) ^ (328498717450075650878471 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (7 : ZMod 328498717450075650878471) ^ ((328498717450075650878471 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (7 : ZMod 328498717450075650878471) ^ ((328498717450075650878471 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (7 : ZMod 328498717450075650878471) ^ ((328498717450075650878471 - 1) / 7) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (7 : ZMod 328498717450075650878471) ^ ((328498717450075650878471 - 1) / 322615759) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_4 : (7 : ZMod 328498717450075650878471) ^ ((328498717450075650878471 - 1) / 14546216946319) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 328498717450075650878471 (7 : ZMod 328498717450075650878471)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 1), (7, 1), (322615759, 1), (14546216946319, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 1), (7, 1), (322615759, 1), (14546216946319, 1)] : List FactorBlock).map factorBlockValue).prod = 328498717450075650878471 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · exact prime_lucas_322615759
      · exact prime_lucas_14546216946319) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4
theorem prime_lucas_3491360476267 : Nat.Prime 3491360476267 := by
  have hfermat : (2 : ZMod 3491360476267) ^ (3491360476267 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (2 : ZMod 3491360476267) ^ ((3491360476267 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (2 : ZMod 3491360476267) ^ ((3491360476267 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (2 : ZMod 3491360476267) ^ ((3491360476267 - 1) / 13) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (2 : ZMod 3491360476267) ^ ((3491360476267 - 1) / 44761031747) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 3491360476267 (2 : ZMod 3491360476267)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (13, 1), (44761031747, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (13, 1), (44761031747, 1)] : List FactorBlock).map factorBlockValue).prod = 3491360476267 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · exact prime_lucas_44761031747) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
theorem prime_lucas_3671953652077 : Nat.Prime 3671953652077 := by
  have hfermat : (2 : ZMod 3671953652077) ^ (3671953652077 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (2 : ZMod 3671953652077) ^ ((3671953652077 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (2 : ZMod 3671953652077) ^ ((3671953652077 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (2 : ZMod 3671953652077) ^ ((3671953652077 - 1) / 305996137673) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 3671953652077 (2 : ZMod 3671953652077)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (305996137673, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (305996137673, 1)] : List FactorBlock).map factorBlockValue).prod = 3671953652077 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · norm_num
      · norm_num
      · exact prime_lucas_305996137673) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
theorem prime_lucas_395250064283 : Nat.Prime 395250064283 := by
  have hfermat : (2 : ZMod 395250064283) ^ (395250064283 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (2 : ZMod 395250064283) ^ ((395250064283 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (2 : ZMod 395250064283) ^ ((395250064283 - 1) / 197625032141) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 395250064283 (2 : ZMod 395250064283)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (197625032141, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (197625032141, 1)] : List FactorBlock).map factorBlockValue).prod = 395250064283 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · norm_num
      · exact prime_lucas_197625032141) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
theorem prime_lucas_4212062026542834349 : Nat.Prime 4212062026542834349 := by
  have hfermat : (2 : ZMod 4212062026542834349) ^ (4212062026542834349 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (2 : ZMod 4212062026542834349) ^ ((4212062026542834349 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (2 : ZMod 4212062026542834349) ^ ((4212062026542834349 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (2 : ZMod 4212062026542834349) ^ ((4212062026542834349 - 1) / 71) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (2 : ZMod 4212062026542834349) ^ ((4212062026542834349 - 1) / 4943734772937599) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 4212062026542834349 (2 : ZMod 4212062026542834349)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (71, 1), (4943734772937599, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (71, 1), (4943734772937599, 1)] : List FactorBlock).map factorBlockValue).prod = 4212062026542834349 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · exact prime_lucas_4943734772937599) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
theorem prime_lucas_4233432875160509 : Nat.Prime 4233432875160509 := by
  have hfermat : (2 : ZMod 4233432875160509) ^ (4233432875160509 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (2 : ZMod 4233432875160509) ^ ((4233432875160509 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (2 : ZMod 4233432875160509) ^ ((4233432875160509 - 1) / 29) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (2 : ZMod 4233432875160509) ^ ((4233432875160509 - 1) / 36495110992763) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 4233432875160509 (2 : ZMod 4233432875160509)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (29, 1), (36495110992763, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (29, 1), (36495110992763, 1)] : List FactorBlock).map factorBlockValue).prod = 4233432875160509 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · norm_num
      · norm_num
      · exact prime_lucas_36495110992763) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
theorem prime_lucas_483498887150858771 : Nat.Prime 483498887150858771 := by
  have hfermat : (2 : ZMod 483498887150858771) ^ (483498887150858771 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (2 : ZMod 483498887150858771) ^ ((483498887150858771 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (2 : ZMod 483498887150858771) ^ ((483498887150858771 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (2 : ZMod 483498887150858771) ^ ((483498887150858771 - 1) / 29) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (2 : ZMod 483498887150858771) ^ ((483498887150858771 - 1) / 1667237541899513) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 483498887150858771 (2 : ZMod 483498887150858771)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 1), (29, 1), (1667237541899513, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 1), (29, 1), (1667237541899513, 1)] : List FactorBlock).map factorBlockValue).prod = 483498887150858771 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · exact prime_lucas_1667237541899513) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
theorem prime_lucas_5002059960833751914533 : Nat.Prime 5002059960833751914533 := by
  have hfermat : (2 : ZMod 5002059960833751914533) ^ (5002059960833751914533 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (2 : ZMod 5002059960833751914533) ^ ((5002059960833751914533 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (2 : ZMod 5002059960833751914533) ^ ((5002059960833751914533 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (2 : ZMod 5002059960833751914533) ^ ((5002059960833751914533 - 1) / 7) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (2 : ZMod 5002059960833751914533) ^ ((5002059960833751914533 - 1) / 19) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_4 : (2 : ZMod 5002059960833751914533) ^ ((5002059960833751914533 - 1) / 4561) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_5 : (2 : ZMod 5002059960833751914533) ^ ((5002059960833751914533 - 1) / 6199) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_6 : (2 : ZMod 5002059960833751914533) ^ ((5002059960833751914533 - 1) / 110849642753) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 5002059960833751914533 (2 : ZMod 5002059960833751914533)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (7, 1), (19, 1), (4561, 1), (6199, 1), (110849642753, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (7, 1), (19, 1), (4561, 1), (6199, 1), (110849642753, 1)] : List FactorBlock).map factorBlockValue).prod = 5002059960833751914533 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · exact prime_lucas_110849642753) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4
    · exact hfactor_5
    · exact hfactor_6
theorem prime_lucas_511229648870179 : Nat.Prime 511229648870179 := by
  have hfermat : (3 : ZMod 511229648870179) ^ (511229648870179 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (3 : ZMod 511229648870179) ^ ((511229648870179 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (3 : ZMod 511229648870179) ^ ((511229648870179 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (3 : ZMod 511229648870179) ^ ((511229648870179 - 1) / 7) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (3 : ZMod 511229648870179) ^ ((511229648870179 - 1) / 12172134496909) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 511229648870179 (3 : ZMod 511229648870179)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (7, 1), (12172134496909, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (7, 1), (12172134496909, 1)] : List FactorBlock).map factorBlockValue).prod = 511229648870179 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · exact prime_lucas_12172134496909) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
theorem prime_lucas_55066055263 : Nat.Prime 55066055263 := by
  have hfermat : (5 : ZMod 55066055263) ^ (55066055263 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (5 : ZMod 55066055263) ^ ((55066055263 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (5 : ZMod 55066055263) ^ ((55066055263 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (5 : ZMod 55066055263) ^ ((55066055263 - 1) / 9177675877) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 55066055263 (5 : ZMod 55066055263)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (9177675877, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (9177675877, 1)] : List FactorBlock).map factorBlockValue).prod = 55066055263 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · norm_num
      · norm_num
      · exact prime_lucas_9177675877) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
theorem prime_lucas_576920451432889 : Nat.Prime 576920451432889 := by
  have hfermat : (19 : ZMod 576920451432889) ^ (576920451432889 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (19 : ZMod 576920451432889) ^ ((576920451432889 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (19 : ZMod 576920451432889) ^ ((576920451432889 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (19 : ZMod 576920451432889) ^ ((576920451432889 - 1) / 127) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (19 : ZMod 576920451432889) ^ ((576920451432889 - 1) / 7010309753) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 576920451432889 (19 : ZMod 576920451432889)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (3, 4), (127, 1), (7010309753, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (3, 4), (127, 1), (7010309753, 1)] : List FactorBlock).map factorBlockValue).prod = 576920451432889 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · exact prime_lucas_7010309753) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
theorem prime_lucas_68933592817856129557 : Nat.Prime 68933592817856129557 := by
  have hfermat : (2 : ZMod 68933592817856129557) ^ (68933592817856129557 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (2 : ZMod 68933592817856129557) ^ ((68933592817856129557 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (2 : ZMod 68933592817856129557) ^ ((68933592817856129557 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (2 : ZMod 68933592817856129557) ^ ((68933592817856129557 - 1) / 12853) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (2 : ZMod 68933592817856129557) ^ ((68933592817856129557 - 1) / 148978605984457) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 68933592817856129557 (2 : ZMod 68933592817856129557)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 2), (12853, 1), (148978605984457, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 2), (12853, 1), (148978605984457, 1)] : List FactorBlock).map factorBlockValue).prod = 68933592817856129557 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · exact prime_lucas_148978605984457) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
theorem prime_lucas_7185896965238456338277 : Nat.Prime 7185896965238456338277 := by
  have hfermat : (2 : ZMod 7185896965238456338277) ^ (7185896965238456338277 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (2 : ZMod 7185896965238456338277) ^ ((7185896965238456338277 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (2 : ZMod 7185896965238456338277) ^ ((7185896965238456338277 - 1) / 13) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (2 : ZMod 7185896965238456338277) ^ ((7185896965238456338277 - 1) / 31) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (2 : ZMod 7185896965238456338277) ^ ((7185896965238456338277 - 1) / 197) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_4 : (2 : ZMod 7185896965238456338277) ^ ((7185896965238456338277 - 1) / 4547) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_5 : (2 : ZMod 7185896965238456338277) ^ ((7185896965238456338277 - 1) / 4976508703597) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 7185896965238456338277 (2 : ZMod 7185896965238456338277)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (13, 1), (31, 1), (197, 1), (4547, 1), (4976508703597, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (13, 1), (31, 1), (197, 1), (4547, 1), (4976508703597, 1)] : List FactorBlock).map factorBlockValue).prod = 7185896965238456338277 - 1 by
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
      · exact prime_lucas_4976508703597) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4
    · exact hfactor_5
theorem prime_lucas_759715652412531949 : Nat.Prime 759715652412531949 := by
  have hfermat : (10 : ZMod 759715652412531949) ^ (759715652412531949 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (10 : ZMod 759715652412531949) ^ ((759715652412531949 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (10 : ZMod 759715652412531949) ^ ((759715652412531949 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (10 : ZMod 759715652412531949) ^ ((759715652412531949 - 1) / 7) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (10 : ZMod 759715652412531949) ^ ((759715652412531949 - 1) / 6211) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_4 : (10 : ZMod 759715652412531949) ^ ((759715652412531949 - 1) / 1456163895877) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 759715652412531949 (10 : ZMod 759715652412531949)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (7, 1), (6211, 1), (1456163895877, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (7, 1), (6211, 1), (1456163895877, 1)] : List FactorBlock).map factorBlockValue).prod = 759715652412531949 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · exact prime_lucas_1456163895877) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4
theorem prime_lucas_775965264098654160067 : Nat.Prime 775965264098654160067 := by
  have hfermat : (2 : ZMod 775965264098654160067) ^ (775965264098654160067 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (2 : ZMod 775965264098654160067) ^ ((775965264098654160067 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (2 : ZMod 775965264098654160067) ^ ((775965264098654160067 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (2 : ZMod 775965264098654160067) ^ ((775965264098654160067 - 1) / 103) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (2 : ZMod 775965264098654160067) ^ ((775965264098654160067 - 1) / 7027) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_4 : (2 : ZMod 775965264098654160067) ^ ((775965264098654160067 - 1) / 7907) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_5 : (2 : ZMod 775965264098654160067) ^ ((775965264098654160067 - 1) / 22598109733) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 775965264098654160067 (2 : ZMod 775965264098654160067)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (103, 1), (7027, 1), (7907, 1), (22598109733, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (103, 1), (7027, 1), (7907, 1), (22598109733, 1)] : List FactorBlock).map factorBlockValue).prod = 775965264098654160067 - 1 by
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
      · exact prime_lucas_22598109733) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4
    · exact hfactor_5
theorem prime_lucas_77851135148107 : Nat.Prime 77851135148107 := by
  have hfermat : (2 : ZMod 77851135148107) ^ (77851135148107 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (2 : ZMod 77851135148107) ^ ((77851135148107 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (2 : ZMod 77851135148107) ^ ((77851135148107 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (2 : ZMod 77851135148107) ^ ((77851135148107 - 1) / 163) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (2 : ZMod 77851135148107) ^ ((77851135148107 - 1) / 499) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_4 : (2 : ZMod 77851135148107) ^ ((77851135148107 - 1) / 159523823) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 77851135148107 (2 : ZMod 77851135148107)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (163, 1), (499, 1), (159523823, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (163, 1), (499, 1), (159523823, 1)] : List FactorBlock).map factorBlockValue).prod = 77851135148107 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · exact prime_lucas_159523823) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4
theorem prime_lucas_85321595874110948137 : Nat.Prime 85321595874110948137 := by
  have hfermat : (10 : ZMod 85321595874110948137) ^ (85321595874110948137 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (10 : ZMod 85321595874110948137) ^ ((85321595874110948137 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (10 : ZMod 85321595874110948137) ^ ((85321595874110948137 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (10 : ZMod 85321595874110948137) ^ ((85321595874110948137 - 1) / 1185022164918207613) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 85321595874110948137 (10 : ZMod 85321595874110948137)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (3, 2), (1185022164918207613, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (3, 2), (1185022164918207613, 1)] : List FactorBlock).map factorBlockValue).prod = 85321595874110948137 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · norm_num
      · norm_num
      · exact prime_lucas_1185022164918207613) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
theorem prime_lucas_88903288392588617 : Nat.Prime 88903288392588617 := by
  have hfermat : (3 : ZMod 88903288392588617) ^ (88903288392588617 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (3 : ZMod 88903288392588617) ^ ((88903288392588617 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (3 : ZMod 88903288392588617) ^ ((88903288392588617 - 1) / 11112911049073577) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 88903288392588617 (3 : ZMod 88903288392588617)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (11112911049073577, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (11112911049073577, 1)] : List FactorBlock).map factorBlockValue).prod = 88903288392588617 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · norm_num
      · exact prime_lucas_11112911049073577) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
theorem prime_lucas_88905616190616804595531 : Nat.Prime 88905616190616804595531 := by
  have hfermat : (2 : ZMod 88905616190616804595531) ^ (88905616190616804595531 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (2 : ZMod 88905616190616804595531) ^ ((88905616190616804595531 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (2 : ZMod 88905616190616804595531) ^ ((88905616190616804595531 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (2 : ZMod 88905616190616804595531) ^ ((88905616190616804595531 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (2 : ZMod 88905616190616804595531) ^ ((88905616190616804595531 - 1) / 7523) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_4 : (2 : ZMod 88905616190616804595531) ^ ((88905616190616804595531 - 1) / 393928026011860537) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 88905616190616804595531 (2 : ZMod 88905616190616804595531)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (5, 1), (7523, 1), (393928026011860537, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (5, 1), (7523, 1), (393928026011860537, 1)] : List FactorBlock).map factorBlockValue).prod = 88905616190616804595531 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · exact prime_lucas_393928026011860537) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4
theorem prime_lucas_929523437269663 : Nat.Prime 929523437269663 := by
  have hfermat : (6 : ZMod 929523437269663) ^ (929523437269663 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (6 : ZMod 929523437269663) ^ ((929523437269663 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (6 : ZMod 929523437269663) ^ ((929523437269663 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (6 : ZMod 929523437269663) ^ ((929523437269663 - 1) / 154920572878277) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 929523437269663 (6 : ZMod 929523437269663)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (154920572878277, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (154920572878277, 1)] : List FactorBlock).map factorBlockValue).prod = 929523437269663 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · norm_num
      · norm_num
      · exact prime_lucas_154920572878277) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
theorem prime_lucas_938162514282182389 : Nat.Prime 938162514282182389 := by
  have hfermat : (2 : ZMod 938162514282182389) ^ (938162514282182389 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (2 : ZMod 938162514282182389) ^ ((938162514282182389 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (2 : ZMod 938162514282182389) ^ ((938162514282182389 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (2 : ZMod 938162514282182389) ^ ((938162514282182389 - 1) / 26060069841171733) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 938162514282182389 (2 : ZMod 938162514282182389)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 2), (26060069841171733, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 2), (26060069841171733, 1)] : List FactorBlock).map factorBlockValue).prod = 938162514282182389 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · norm_num
      · norm_num
      · exact prime_lucas_26060069841171733) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
theorem prime_lucas_9723880320550629899 : Nat.Prime 9723880320550629899 := by
  have hfermat : (2 : ZMod 9723880320550629899) ^ (9723880320550629899 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (2 : ZMod 9723880320550629899) ^ ((9723880320550629899 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (2 : ZMod 9723880320550629899) ^ ((9723880320550629899 - 1) / 7) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (2 : ZMod 9723880320550629899) ^ ((9723880320550629899 - 1) / 17) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (2 : ZMod 9723880320550629899) ^ ((9723880320550629899 - 1) / 50475101) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_4 : (2 : ZMod 9723880320550629899) ^ ((9723880320550629899 - 1) / 809441471) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 9723880320550629899 (2 : ZMod 9723880320550629899)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (7, 1), (17, 1), (50475101, 1), (809441471, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (7, 1), (17, 1), (50475101, 1), (809441471, 1)] : List FactorBlock).map factorBlockValue).prod = 9723880320550629899 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · exact prime_lucas_50475101
      · exact prime_lucas_809441471) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4

end TotientTailPeriodKiller
end Erdos249257
