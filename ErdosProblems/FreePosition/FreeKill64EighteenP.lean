import Erdos249257.DiagonalPincerCertificatesT64

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

private def eighteenPFastPow {M : Type*} [Monoid M] (a : M) (n : ℕ) : M :=
  Nat.binaryRec 1 (fun b _ r => if b then r * r * a else r * r) n

private theorem eighteenPFastPow_eq_pow {M : Type*} [Monoid M] (a : M) (n : ℕ) :
    eighteenPFastPow a n = a ^ n := by
  induction n using Nat.binaryRec with
  | zero => simp [eighteenPFastPow, Nat.binaryRec_zero]
  | bit b n ih =>
      rw [eighteenPFastPow, Nat.binaryRec_eq b n (by left; simp)]
      change (if b then eighteenPFastPow a n * eighteenPFastPow a n * a
        else eighteenPFastPow a n * eighteenPFastPow a n) = _
      rw [ih]
      cases b <;> simp [Nat.bit, two_mul, pow_add]

private theorem prime_eighteenP_2 : Nat.Prime 2 := by norm_num
private theorem prime_eighteenP_313 : Nat.Prime 313 := by norm_num
private theorem prime_eighteenP_15107 : Nat.Prime 15107 := by norm_num
private theorem prime_eighteenP_3 : Nat.Prime 3 := by norm_num
private theorem prime_eighteenP_5101 : Nat.Prime 5101 := by norm_num
private theorem prime_eighteenP_7 : Nat.Prime 7 := by norm_num
private theorem prime_eighteenP_11 : Nat.Prime 11 := by norm_num
private theorem prime_eighteenP_53 : Nat.Prime 53 := by norm_num
private theorem prime_eighteenP_6949 : Nat.Prime 6949 := by norm_num
private theorem prime_eighteenP_140659 : Nat.Prime 140659 := by norm_num
private theorem prime_eighteenP_71800742784079 : Nat.Prime 71800742784079 := by
  apply lucas_primality 71800742784079 (3 : ZMod 71800742784079)
  · rw [← eighteenPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 2), (7, 1), (11, 1), (53, 1), (6949, 1), (140659, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 2), (7, 1), (11, 1), (53, 1), (6949, 1), (140659, 1)] : List FactorBlock).map factorBlockValue).prod = 71800742784079 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eighteenP_2
      · exact prime_eighteenP_3
      · exact prime_eighteenP_7
      · exact prime_eighteenP_11
      · exact prime_eighteenP_53
      · exact prime_eighteenP_6949
      · exact prime_eighteenP_140659
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 71800742784079) ^ 35900371392039 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (3 : ZMod 71800742784079) ^ 23933580928026 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (3 : ZMod 71800742784079) ^ 10257248969154 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (3 : ZMod 71800742784079) ^ 6527340253098 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (3 : ZMod 71800742784079) ^ 1354730995926 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (3 : ZMod 71800742784079) ^ 10332528822 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (3 : ZMod 71800742784079) ^ 510459642 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide

private theorem prime_eighteenP_281284292307138799873 : Nat.Prime 281284292307138799873 := by
  apply lucas_primality 281284292307138799873 (7 : ZMod 281284292307138799873)
  · rw [← eighteenPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 8), (3, 1), (5101, 1), (71800742784079, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 8), (3, 1), (5101, 1), (71800742784079, 1)] : List FactorBlock).map factorBlockValue).prod = 281284292307138799873 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eighteenP_2
      · exact prime_eighteenP_3
      · exact prime_eighteenP_5101
      · exact prime_eighteenP_71800742784079
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 281284292307138799873) ^ 140642146153569399936 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (7 : ZMod 281284292307138799873) ^ 93761430769046266624 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (7 : ZMod 281284292307138799873) ^ 55142970458172672 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (7 : ZMod 281284292307138799873) ^ 3917568 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide

private theorem prime_eighteenP_8498723607767891699362823 : Nat.Prime 8498723607767891699362823 := by
  apply lucas_primality 8498723607767891699362823 (5 : ZMod 8498723607767891699362823)
  · rw [← eighteenPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (15107, 1), (281284292307138799873, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (15107, 1), (281284292307138799873, 1)] : List FactorBlock).map factorBlockValue).prod = 8498723607767891699362823 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eighteenP_2
      · exact prime_eighteenP_15107
      · exact prime_eighteenP_281284292307138799873
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 8498723607767891699362823) ^ 4249361803883945849681411 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (5 : ZMod 8498723607767891699362823) ^ 562568584614277599746 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (5 : ZMod 8498723607767891699362823) ^ 30214 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide

private theorem prime_eighteenP_193 : Nat.Prime 193 := by norm_num
private theorem prime_eighteenP_557 : Nat.Prime 557 := by norm_num
private theorem prime_eighteenP_28711 : Nat.Prime 28711 := by norm_num
private theorem prime_eighteenP_19 : Nat.Prime 19 := by norm_num
private theorem prime_eighteenP_31 : Nat.Prime 31 := by norm_num
private theorem prime_eighteenP_53441 : Nat.Prime 53441 := by norm_num
private theorem prime_eighteenP_9803393 : Nat.Prime 9803393 := by norm_num
private theorem prime_eighteenP_492491989531733773 : Nat.Prime 492491989531733773 := by
  apply lucas_primality 492491989531733773 (6 : ZMod 492491989531733773)
  · rw [← eighteenPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (7, 1), (19, 2), (31, 1), (53441, 1), (9803393, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (7, 1), (19, 2), (31, 1), (53441, 1), (9803393, 1)] : List FactorBlock).map factorBlockValue).prod = 492491989531733773 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eighteenP_2
      · exact prime_eighteenP_3
      · exact prime_eighteenP_7
      · exact prime_eighteenP_19
      · exact prime_eighteenP_31
      · exact prime_eighteenP_53441
      · exact prime_eighteenP_9803393
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 492491989531733773) ^ 246245994765866886 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (6 : ZMod 492491989531733773) ^ 164163996510577924 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (6 : ZMod 492491989531733773) ^ 70355998504533396 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (6 : ZMod 492491989531733773) ^ 25920631027985988 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (6 : ZMod 492491989531733773) ^ 15886838371991412 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (6 : ZMod 492491989531733773) ^ 9215620769292 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (6 : ZMod 492491989531733773) ^ 50236891404 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide

private theorem prime_eighteenP_15751890387750407709255743 : Nat.Prime 15751890387750407709255743 := by
  apply lucas_primality 15751890387750407709255743 (5 : ZMod 15751890387750407709255743)
  · rw [← eighteenPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (557, 1), (28711, 1), (492491989531733773, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (557, 1), (28711, 1), (492491989531733773, 1)] : List FactorBlock).map factorBlockValue).prod = 15751890387750407709255743 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eighteenP_2
      · exact prime_eighteenP_557
      · exact prime_eighteenP_28711
      · exact prime_eighteenP_492491989531733773
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 15751890387750407709255743) ^ 7875945193875203854627871 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (5 : ZMod 15751890387750407709255743) ^ 28279875022891216713206 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (5 : ZMod 15751890387750407709255743) ^ 548636076338351423122 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (5 : ZMod 15751890387750407709255743) ^ 31984054 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide

private theorem prime_eighteenP_3923 : Nat.Prime 3923 := by norm_num
private theorem prime_eighteenP_8197093 : Nat.Prime 8197093 := by norm_num
private theorem prime_eighteenP_5 : Nat.Prime 5 := by norm_num
private theorem prime_eighteenP_149 : Nat.Prime 149 := by norm_num
private theorem prime_eighteenP_929 : Nat.Prime 929 := by norm_num
private theorem prime_eighteenP_1796567 : Nat.Prime 1796567 := by norm_num
private theorem prime_eighteenP_110295707065568641 : Nat.Prime 110295707065568641 := by
  apply lucas_primality 110295707065568641 (26 : ZMod 110295707065568641)
  · rw [← eighteenPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 7), (3, 2), (5, 1), (7, 1), (11, 1), (149, 1), (929, 1), (1796567, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 7), (3, 2), (5, 1), (7, 1), (11, 1), (149, 1), (929, 1), (1796567, 1)] : List FactorBlock).map factorBlockValue).prod = 110295707065568641 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eighteenP_2
      · exact prime_eighteenP_3
      · exact prime_eighteenP_5
      · exact prime_eighteenP_7
      · exact prime_eighteenP_11
      · exact prime_eighteenP_149
      · exact prime_eighteenP_929
      · exact prime_eighteenP_1796567
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (26 : ZMod 110295707065568641) ^ 55147853532784320 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (26 : ZMod 110295707065568641) ^ 36765235688522880 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (26 : ZMod 110295707065568641) ^ 22059141413113728 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (26 : ZMod 110295707065568641) ^ 15756529580795520 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (26 : ZMod 110295707065568641) ^ 10026882460506240 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (26 : ZMod 110295707065568641) ^ 740239644735360 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (26 : ZMod 110295707065568641) ^ 118725195980160 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (26 : ZMod 110295707065568641) ^ 61392481920 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide

private theorem prime_eighteenP_35393 : Nat.Prime 35393 := by norm_num
private theorem prime_eighteenP_17 : Nat.Prime 17 := by norm_num
private theorem prime_eighteenP_89 : Nat.Prime 89 := by norm_num
private theorem prime_eighteenP_293 : Nat.Prime 293 := by norm_num
private theorem prime_eighteenP_92867 : Nat.Prime 92867 := by norm_num
private theorem prime_eighteenP_23 : Nat.Prime 23 := by norm_num
private theorem prime_eighteenP_37 : Nat.Prime 37 := by norm_num
private theorem prime_eighteenP_59 : Nat.Prime 59 := by norm_num
private theorem prime_eighteenP_230861 : Nat.Prime 230861 := by norm_num
private theorem prime_eighteenP_486834597859 : Nat.Prime 486834597859 := by
  apply lucas_primality 486834597859 (3 : ZMod 486834597859)
  · rw [← eighteenPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (7, 1), (23, 1), (37, 1), (59, 1), (230861, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (7, 1), (23, 1), (37, 1), (59, 1), (230861, 1)] : List FactorBlock).map factorBlockValue).prod = 486834597859 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eighteenP_2
      · exact prime_eighteenP_3
      · exact prime_eighteenP_7
      · exact prime_eighteenP_23
      · exact prime_eighteenP_37
      · exact prime_eighteenP_59
      · exact prime_eighteenP_230861
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 486834597859) ^ 243417298929 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (3 : ZMod 486834597859) ^ 162278199286 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (3 : ZMod 486834597859) ^ 69547799694 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (3 : ZMod 486834597859) ^ 21166721646 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (3 : ZMod 486834597859) ^ 13157691834 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (3 : ZMod 486834597859) ^ 8251433862 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (3 : ZMod 486834597859) ^ 2108778 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide

private theorem prime_eighteenP_120254309687513354704063 : Nat.Prime 120254309687513354704063 := by
  apply lucas_primality 120254309687513354704063 (3 : ZMod 120254309687513354704063)
  · rw [← eighteenPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (17, 1), (89, 1), (293, 1), (92867, 1), (486834597859, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (17, 1), (89, 1), (293, 1), (92867, 1), (486834597859, 1)] : List FactorBlock).map factorBlockValue).prod = 120254309687513354704063 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eighteenP_2
      · exact prime_eighteenP_3
      · exact prime_eighteenP_17
      · exact prime_eighteenP_89
      · exact prime_eighteenP_293
      · exact prime_eighteenP_92867
      · exact prime_eighteenP_486834597859
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 120254309687513354704063) ^ 60127154843756677352031 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (3 : ZMod 120254309687513354704063) ^ 40084769895837784901354 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (3 : ZMod 120254309687513354704063) ^ 7073782922794903217886 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (3 : ZMod 120254309687513354704063) ^ 1351172018960824210158 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (3 : ZMod 120254309687513354704063) ^ 410424265145096773734 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (3 : ZMod 120254309687513354704063) ^ 1294908952453652586 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (3 : ZMod 120254309687513354704063) ^ 247012661418 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide

private theorem prime_eighteenP_79 : Nat.Prime 79 := by norm_num
private theorem prime_eighteenP_189067 : Nat.Prime 189067 := by norm_num
private theorem prime_eighteenP_2202311 : Nat.Prime 2202311 := by norm_num
private theorem prime_eighteenP_43 : Nat.Prime 43 := by norm_num
private theorem prime_eighteenP_47 : Nat.Prime 47 := by norm_num
private theorem prime_eighteenP_877 : Nat.Prime 877 := by norm_num
private theorem prime_eighteenP_13751 : Nat.Prime 13751 := by norm_num
private theorem prime_eighteenP_161735950924213 : Nat.Prime 161735950924213 := by
  apply lucas_primality 161735950924213 (2 : ZMod 161735950924213)
  · rw [← eighteenPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (7, 1), (43, 1), (47, 1), (79, 1), (877, 1), (13751, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (7, 1), (43, 1), (47, 1), (79, 1), (877, 1), (13751, 1)] : List FactorBlock).map factorBlockValue).prod = 161735950924213 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eighteenP_2
      · exact prime_eighteenP_3
      · exact prime_eighteenP_7
      · exact prime_eighteenP_43
      · exact prime_eighteenP_47
      · exact prime_eighteenP_79
      · exact prime_eighteenP_877
      · exact prime_eighteenP_13751
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 161735950924213) ^ 80867975462106 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (2 : ZMod 161735950924213) ^ 53911983641404 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (2 : ZMod 161735950924213) ^ 23105135846316 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (2 : ZMod 161735950924213) ^ 3761301184284 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (2 : ZMod 161735950924213) ^ 3441190445196 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (2 : ZMod 161735950924213) ^ 2047290518028 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (2 : ZMod 161735950924213) ^ 184419556356 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (2 : ZMod 161735950924213) ^ 11761759212 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide

private theorem prime_eighteenP_71 : Nat.Prime 71 := by norm_num
private theorem prime_eighteenP_11633 : Nat.Prime 11633 := by norm_num
private theorem prime_eighteenP_109 : Nat.Prime 109 := by norm_num
private theorem prime_eighteenP_173 : Nat.Prime 173 := by norm_num
private theorem prime_eighteenP_311 : Nat.Prime 311 := by norm_num
private theorem prime_eighteenP_13 : Nat.Prime 13 := by norm_num
private theorem prime_eighteenP_2169877 : Nat.Prime 2169877 := by norm_num
private theorem prime_eighteenP_789835229 : Nat.Prime 789835229 := by
  apply lucas_primality 789835229 (10 : ZMod 789835229)
  · rw [← eighteenPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (7, 1), (13, 1), (2169877, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (7, 1), (13, 1), (2169877, 1)] : List FactorBlock).map factorBlockValue).prod = 789835229 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eighteenP_2
      · exact prime_eighteenP_7
      · exact prime_eighteenP_13
      · exact prime_eighteenP_2169877
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (10 : ZMod 789835229) ^ 394917614 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (10 : ZMod 789835229) ^ 112833604 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (10 : ZMod 789835229) ^ 60756556 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (10 : ZMod 789835229) ^ 364 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide

private theorem prime_eighteenP_86881875191 : Nat.Prime 86881875191 := by
  apply lucas_primality 86881875191 (11 : ZMod 86881875191)
  · rw [← eighteenPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 1), (11, 1), (789835229, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 1), (11, 1), (789835229, 1)] : List FactorBlock).map factorBlockValue).prod = 86881875191 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eighteenP_2
      · exact prime_eighteenP_5
      · exact prime_eighteenP_11
      · exact prime_eighteenP_789835229
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 86881875191) ^ 43440937595 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (11 : ZMod 86881875191) ^ 17376375038 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (11 : ZMod 86881875191) ^ 7898352290 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (11 : ZMod 86881875191) ^ 110 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide

private theorem prime_eighteenP_8588487709947216218393 : Nat.Prime 8588487709947216218393 := by
  apply lucas_primality 8588487709947216218393 (5 : ZMod 8588487709947216218393)
  · rw [← eighteenPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (7, 2), (43, 1), (109, 1), (173, 1), (311, 1), (86881875191, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (7, 2), (43, 1), (109, 1), (173, 1), (311, 1), (86881875191, 1)] : List FactorBlock).map factorBlockValue).prod = 8588487709947216218393 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eighteenP_2
      · exact prime_eighteenP_7
      · exact prime_eighteenP_43
      · exact prime_eighteenP_109
      · exact prime_eighteenP_173
      · exact prime_eighteenP_311
      · exact prime_eighteenP_86881875191
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 8588487709947216218393) ^ 4294243854973608109196 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (5 : ZMod 8588487709947216218393) ^ 1226926815706745174056 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (5 : ZMod 8588487709947216218393) ^ 199732272324353865544 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (5 : ZMod 8588487709947216218393) ^ 78793465228873543288 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (5 : ZMod 8588487709947216218393) ^ 49644437629752694904 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (5 : ZMod 8588487709947216218393) ^ 27615716109155036072 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (5 : ZMod 8588487709947216218393) ^ 98852467112 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide

private theorem prime_eighteenP_97 : Nat.Prime 97 := by norm_num
private theorem prime_eighteenP_36749 : Nat.Prime 36749 := by norm_num
private theorem prime_eighteenP_8917369 : Nat.Prime 8917369 := by norm_num
private theorem prime_eighteenP_160512643 : Nat.Prime 160512643 := by
  apply lucas_primality 160512643 (2 : ZMod 160512643)
  · rw [← eighteenPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 2), (8917369, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 2), (8917369, 1)] : List FactorBlock).map factorBlockValue).prod = 160512643 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eighteenP_2
      · exact prime_eighteenP_3
      · exact prime_eighteenP_8917369
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 160512643) ^ 80256321 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (2 : ZMod 160512643) ^ 53504214 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (2 : ZMod 160512643) ^ 18 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide

private theorem prime_eighteenP_73 : Nat.Prime 73 := by norm_num
private theorem prime_eighteenP_2939 : Nat.Prime 2939 := by norm_num
private theorem prime_eighteenP_722317 : Nat.Prime 722317 := by norm_num
private theorem prime_eighteenP_18596513447881 : Nat.Prime 18596513447881 := by
  apply lucas_primality 18596513447881 (13 : ZMod 18596513447881)
  · rw [← eighteenPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (3, 1), (5, 1), (73, 1), (2939, 1), (722317, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (3, 1), (5, 1), (73, 1), (2939, 1), (722317, 1)] : List FactorBlock).map factorBlockValue).prod = 18596513447881 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eighteenP_2
      · exact prime_eighteenP_3
      · exact prime_eighteenP_5
      · exact prime_eighteenP_73
      · exact prime_eighteenP_2939
      · exact prime_eighteenP_722317
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 18596513447881) ^ 9298256723940 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (13 : ZMod 18596513447881) ^ 6198837815960 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (13 : ZMod 18596513447881) ^ 3719302689576 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (13 : ZMod 18596513447881) ^ 254746759560 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (13 : ZMod 18596513447881) ^ 6327496920 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (13 : ZMod 18596513447881) ^ 25745640 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide

private theorem prime_eighteenP_986981 : Nat.Prime 986981 := by norm_num
private theorem prime_eighteenP_1151 : Nat.Prime 1151 := by norm_num
private theorem prime_eighteenP_14731 : Nat.Prime 14731 := by norm_num
private theorem prime_eighteenP_48313 : Nat.Prime 48313 := by norm_num
private theorem prime_eighteenP_3655739 : Nat.Prime 3655739 := by norm_num
private theorem prime_eighteenP_1096721701 : Nat.Prime 1096721701 := by
  apply lucas_primality 1096721701 (2 : ZMod 1096721701)
  · rw [← eighteenPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (5, 2), (3655739, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (5, 2), (3655739, 1)] : List FactorBlock).map factorBlockValue).prod = 1096721701 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eighteenP_2
      · exact prime_eighteenP_3
      · exact prime_eighteenP_5
      · exact prime_eighteenP_3655739
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1096721701) ^ 548360850 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (2 : ZMod 1096721701) ^ 365573900 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (2 : ZMod 1096721701) ^ 219344340 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (2 : ZMod 1096721701) ^ 300 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide

private theorem prime_eighteenP_3122142087303295613 : Nat.Prime 3122142087303295613 := by
  apply lucas_primality 3122142087303295613 (2 : ZMod 3122142087303295613)
  · rw [← eighteenPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (14731, 1), (48313, 1), (1096721701, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (14731, 1), (48313, 1), (1096721701, 1)] : List FactorBlock).map factorBlockValue).prod = 3122142087303295613 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eighteenP_2
      · exact prime_eighteenP_14731
      · exact prime_eighteenP_48313
      · exact prime_eighteenP_1096721701
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 3122142087303295613) ^ 1561071043651647806 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (2 : ZMod 3122142087303295613) ^ 211943662161652 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (2 : ZMod 3122142087303295613) ^ 64623229509724 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (2 : ZMod 3122142087303295613) ^ 2846795212 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide

private theorem prime_eighteenP_21561513254916559503379 : Nat.Prime 21561513254916559503379 := by
  apply lucas_primality 21561513254916559503379 (10 : ZMod 21561513254916559503379)
  · rw [← eighteenPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (1151, 1), (3122142087303295613, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (1151, 1), (3122142087303295613, 1)] : List FactorBlock).map factorBlockValue).prod = 21561513254916559503379 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eighteenP_2
      · exact prime_eighteenP_3
      · exact prime_eighteenP_1151
      · exact prime_eighteenP_3122142087303295613
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (10 : ZMod 21561513254916559503379) ^ 10780756627458279751689 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (10 : ZMod 21561513254916559503379) ^ 7187171084972186501126 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (10 : ZMod 21561513254916559503379) ^ 18732852523819773678 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (10 : ZMod 21561513254916559503379) ^ 6906 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide

private theorem prime_eighteenP_29 : Nat.Prime 29 := by norm_num
private theorem prime_eighteenP_41 : Nat.Prime 41 := by norm_num
private theorem prime_eighteenP_61 : Nat.Prime 61 := by norm_num
private theorem prime_eighteenP_26417 : Nat.Prime 26417 := by norm_num
private theorem prime_eighteenP_39157 : Nat.Prime 39157 := by norm_num
private theorem prime_eighteenP_137 : Nat.Prime 137 := by norm_num
private theorem prime_eighteenP_1693 : Nat.Prime 1693 := by norm_num
private theorem prime_eighteenP_67819 : Nat.Prime 67819 := by norm_num
private theorem prime_eighteenP_3593063 : Nat.Prime 3593063 := by norm_num
private theorem prime_eighteenP_20572881415656670829 : Nat.Prime 20572881415656670829 := by
  apply lucas_primality 20572881415656670829 (2 : ZMod 20572881415656670829)
  · rw [← eighteenPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (7, 1), (13, 1), (137, 1), (1693, 1), (67819, 1), (3593063, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (7, 1), (13, 1), (137, 1), (1693, 1), (67819, 1), (3593063, 1)] : List FactorBlock).map factorBlockValue).prod = 20572881415656670829 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eighteenP_2
      · exact prime_eighteenP_7
      · exact prime_eighteenP_13
      · exact prime_eighteenP_137
      · exact prime_eighteenP_1693
      · exact prime_eighteenP_67819
      · exact prime_eighteenP_3593063
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 20572881415656670829) ^ 10286440707828335414 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (2 : ZMod 20572881415656670829) ^ 2938983059379524404 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (2 : ZMod 20572881415656670829) ^ 1582529339665897756 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (2 : ZMod 20572881415656670829) ^ 150167017632530444 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (2 : ZMod 20572881415656670829) ^ 12151731491823196 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (2 : ZMod 20572881415656670829) ^ 303349819603012 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (2 : ZMod 20572881415656670829) ^ 5725722431156 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide

private theorem prime_eighteenP_3616901 : Nat.Prime 3616901 := by norm_num
private theorem prime_eighteenP_5004841 : Nat.Prime 5004841 := by norm_num
private theorem prime_eighteenP_11968729 : Nat.Prime 11968729 := by norm_num
private theorem prime_eighteenP_287249497 : Nat.Prime 287249497 := by
  apply lucas_primality 287249497 (5 : ZMod 287249497)
  · rw [← eighteenPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (3, 1), (11968729, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (3, 1), (11968729, 1)] : List FactorBlock).map factorBlockValue).prod = 287249497 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eighteenP_2
      · exact prime_eighteenP_3
      · exact prime_eighteenP_11968729
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 287249497) ^ 143624748 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (5 : ZMod 287249497) ^ 95749832 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (5 : ZMod 287249497) ^ 24 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide

private theorem prime_eighteenP_93596301651291302272987 : Nat.Prime 93596301651291302272987 := by
  apply lucas_primality 93596301651291302272987 (2 : ZMod 93596301651291302272987)
  · rw [← eighteenPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 2), (3616901, 1), (5004841, 1), (287249497, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 2), (3616901, 1), (5004841, 1), (287249497, 1)] : List FactorBlock).map factorBlockValue).prod = 93596301651291302272987 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eighteenP_2
      · exact prime_eighteenP_3
      · exact prime_eighteenP_3616901
      · exact prime_eighteenP_5004841
      · exact prime_eighteenP_287249497
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 93596301651291302272987) ^ 46798150825645651136493 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (2 : ZMod 93596301651291302272987) ^ 31198767217097100757662 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (2 : ZMod 93596301651291302272987) ^ 25877485076669586 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (2 : ZMod 93596301651291302272987) ^ 18701153873078346 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (2 : ZMod 93596301651291302272987) ^ 325836259519338 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide

private theorem prime_eighteenP_36315365040701025281918957 : Nat.Prime 36315365040701025281918957 := by
  apply lucas_primality 36315365040701025281918957 (2 : ZMod 36315365040701025281918957)
  · rw [← eighteenPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (97, 1), (93596301651291302272987, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (97, 1), (93596301651291302272987, 1)] : List FactorBlock).map factorBlockValue).prod = 36315365040701025281918957 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eighteenP_2
      · exact prime_eighteenP_97
      · exact prime_eighteenP_93596301651291302272987
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 36315365040701025281918957) ^ 18157682520350512640959478 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (2 : ZMod 36315365040701025281918957) ^ 374385206605165209091948 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (2 : ZMod 36315365040701025281918957) ^ 388 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide

private theorem prime_eighteenP_115903 : Nat.Prime 115903 := by norm_num
private theorem prime_eighteenP_131 : Nat.Prime 131 := by norm_num
private theorem prime_eighteenP_9833 : Nat.Prime 9833 := by norm_num
private theorem prime_eighteenP_32244294937 : Nat.Prime 32244294937 := by
  apply lucas_primality 32244294937 (10 : ZMod 32244294937)
  · rw [← eighteenPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (3, 1), (7, 1), (131, 1), (149, 1), (9833, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (3, 1), (7, 1), (131, 1), (149, 1), (9833, 1)] : List FactorBlock).map factorBlockValue).prod = 32244294937 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eighteenP_2
      · exact prime_eighteenP_3
      · exact prime_eighteenP_7
      · exact prime_eighteenP_131
      · exact prime_eighteenP_149
      · exact prime_eighteenP_9833
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 32244294937) ^ 16122147468 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (10 : ZMod 32244294937) ^ 10748098312 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (10 : ZMod 32244294937) ^ 4606327848 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (10 : ZMod 32244294937) ^ 246139656 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (10 : ZMod 32244294937) ^ 216404664 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (10 : ZMod 32244294937) ^ 3279192 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide

private theorem prime_eighteenP_457 : Nat.Prime 457 := by norm_num
private theorem prime_eighteenP_1433 : Nat.Prime 1433 := by norm_num
private theorem prime_eighteenP_8783 : Nat.Prime 8783 := by norm_num
private theorem prime_eighteenP_1898100541591 : Nat.Prime 1898100541591 := by
  apply lucas_primality 1898100541591 (3 : ZMod 1898100541591)
  · rw [← eighteenPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (5, 1), (11, 1), (457, 1), (1433, 1), (8783, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (5, 1), (11, 1), (457, 1), (1433, 1), (8783, 1)] : List FactorBlock).map factorBlockValue).prod = 1898100541591 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eighteenP_2
      · exact prime_eighteenP_3
      · exact prime_eighteenP_5
      · exact prime_eighteenP_11
      · exact prime_eighteenP_457
      · exact prime_eighteenP_1433
      · exact prime_eighteenP_8783
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1898100541591) ^ 949050270795 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (3 : ZMod 1898100541591) ^ 632700180530 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (3 : ZMod 1898100541591) ^ 379620108318 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (3 : ZMod 1898100541591) ^ 172554594690 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (3 : ZMod 1898100541591) ^ 4153392870 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (3 : ZMod 1898100541591) ^ 1324564230 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (3 : ZMod 1898100541591) ^ 216110730 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide

private theorem prime_eighteenP_2663 : Nat.Prime 2663 := by norm_num
private theorem prime_eighteenP_9063547 : Nat.Prime 9063547 := by norm_num
private theorem prime_eighteenP_151 : Nat.Prime 151 := by norm_num
private theorem prime_eighteenP_211 : Nat.Prime 211 := by norm_num
private theorem prime_eighteenP_26126021 : Nat.Prime 26126021 := by
  apply lucas_primality 26126021 (3 : ZMod 26126021)
  · rw [← eighteenPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (5, 1), (41, 1), (151, 1), (211, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (5, 1), (41, 1), (151, 1), (211, 1)] : List FactorBlock).map factorBlockValue).prod = 26126021 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eighteenP_2
      · exact prime_eighteenP_5
      · exact prime_eighteenP_41
      · exact prime_eighteenP_151
      · exact prime_eighteenP_211
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 26126021) ^ 13063010 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (3 : ZMod 26126021) ^ 5225204 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (3 : ZMod 26126021) ^ 637220 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (3 : ZMod 26126021) ^ 173020 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (3 : ZMod 26126021) ^ 123820 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide

private theorem prime_eighteenP_397 : Nat.Prime 397 := by norm_num
private theorem prime_eighteenP_1213 : Nat.Prime 1213 := by norm_num
private theorem prime_eighteenP_8436948721 : Nat.Prime 8436948721 := by
  apply lucas_primality 8436948721 (7 : ZMod 8436948721)
  · rw [← eighteenPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 4), (3, 1), (5, 1), (73, 1), (397, 1), (1213, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 4), (3, 1), (5, 1), (73, 1), (397, 1), (1213, 1)] : List FactorBlock).map factorBlockValue).prod = 8436948721 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eighteenP_2
      · exact prime_eighteenP_3
      · exact prime_eighteenP_5
      · exact prime_eighteenP_73
      · exact prime_eighteenP_397
      · exact prime_eighteenP_1213
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 8436948721) ^ 4218474360 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (7 : ZMod 8436948721) ^ 2812316240 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (7 : ZMod 8436948721) ^ 1687389744 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (7 : ZMod 8436948721) ^ 115574640 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (7 : ZMod 8436948721) ^ 21251760 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (7 : ZMod 8436948721) ^ 6955440 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide

private theorem prime_eighteenP_4256160782770160163040901761 : Nat.Prime 4256160782770160163040901761 := by
  apply lucas_primality 4256160782770160163040901761 (83 : ZMod 4256160782770160163040901761)
  · rw [← eighteenPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 7), (3, 5), (5, 1), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 7), (3, 5), (5, 1), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod = 4256160782770160163040901761 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eighteenP_2
      · exact prime_eighteenP_3
      · exact prime_eighteenP_5
      · exact prime_eighteenP_7
      · exact prime_eighteenP_11
      · exact prime_eighteenP_13
      · exact prime_eighteenP_17
      · exact prime_eighteenP_19
      · exact prime_eighteenP_23
      · exact prime_eighteenP_29
      · exact prime_eighteenP_31
      · exact prime_eighteenP_37
      · exact prime_eighteenP_41
      · exact prime_eighteenP_43
      · exact prime_eighteenP_47
      · exact prime_eighteenP_53
      · exact prime_eighteenP_59
      · exact prime_eighteenP_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (83 : ZMod 4256160782770160163040901761) ^ 2128080391385080081520450880 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (83 : ZMod 4256160782770160163040901761) ^ 1418720260923386721013633920 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (83 : ZMod 4256160782770160163040901761) ^ 851232156554032032608180352 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (83 : ZMod 4256160782770160163040901761) ^ 608022968967165737577271680 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (83 : ZMod 4256160782770160163040901761) ^ 386923707524560014821900160 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (83 : ZMod 4256160782770160163040901761) ^ 327396983290012320233915520 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (83 : ZMod 4256160782770160163040901761) ^ 250362398986480009590641280 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (83 : ZMod 4256160782770160163040901761) ^ 224008462251061061212679040 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (83 : ZMod 4256160782770160163040901761) ^ 185050468816093920132213120 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (83 : ZMod 4256160782770160163040901761) ^ 146764164923108971139341440 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (83 : ZMod 4256160782770160163040901761) ^ 137295509121618069775512960 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (83 : ZMod 4256160782770160163040901761) ^ 115031372507301626028132480 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (83 : ZMod 4256160782770160163040901761) ^ 103808799579760003976607360 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (83 : ZMod 4256160782770160163040901761) ^ 98980483320236282861416320 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (83 : ZMod 4256160782770160163040901761) ^ 90556612399365109851934080 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (83 : ZMod 4256160782770160163040901761) ^ 80304920429625663453601920 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (83 : ZMod 4256160782770160163040901761) ^ 72138318352036612932896640 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (83 : ZMod 4256160782770160163040901761) ^ 69773127586396068246572160 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide

private theorem prime_eighteenP_114593 : Nat.Prime 114593 := by norm_num
private theorem prime_eighteenP_42857783 : Nat.Prime 42857783 := by
  apply lucas_primality 42857783 (5 : ZMod 42857783)
  · rw [← eighteenPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (11, 1), (17, 1), (114593, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (11, 1), (17, 1), (114593, 1)] : List FactorBlock).map factorBlockValue).prod = 42857783 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eighteenP_2
      · exact prime_eighteenP_11
      · exact prime_eighteenP_17
      · exact prime_eighteenP_114593
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 42857783) ^ 21428891 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (5 : ZMod 42857783) ^ 3896162 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (5 : ZMod 42857783) ^ 2521046 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (5 : ZMod 42857783) ^ 374 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide

private theorem prime_eighteenP_30429025931 : Nat.Prime 30429025931 := by
  apply lucas_primality 30429025931 (2 : ZMod 30429025931)
  · rw [← eighteenPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 1), (71, 1), (42857783, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 1), (71, 1), (42857783, 1)] : List FactorBlock).map factorBlockValue).prod = 30429025931 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eighteenP_2
      · exact prime_eighteenP_5
      · exact prime_eighteenP_71
      · exact prime_eighteenP_42857783
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 30429025931) ^ 15214512965 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (2 : ZMod 30429025931) ^ 6085805186 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (2 : ZMod 30429025931) ^ 428577830 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (2 : ZMod 30429025931) ^ 710 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide

private theorem prime_eighteenP_81047 : Nat.Prime 81047 := by norm_num
private theorem prime_eighteenP_14999741 : Nat.Prime 14999741 := by norm_num
private theorem prime_eighteenP_11655978276633277 : Nat.Prime 11655978276633277 := by
  apply lucas_primality 11655978276633277 (2 : ZMod 11655978276633277)
  · rw [← eighteenPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (17, 1), (47, 1), (81047, 1), (14999741, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (17, 1), (47, 1), (81047, 1), (14999741, 1)] : List FactorBlock).map factorBlockValue).prod = 11655978276633277 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eighteenP_2
      · exact prime_eighteenP_3
      · exact prime_eighteenP_17
      · exact prime_eighteenP_47
      · exact prime_eighteenP_81047
      · exact prime_eighteenP_14999741
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 11655978276633277) ^ 5827989138316638 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (2 : ZMod 11655978276633277) ^ 3885326092211092 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (2 : ZMod 11655978276633277) ^ 685645780978428 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (2 : ZMod 11655978276633277) ^ 247999537800708 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (2 : ZMod 11655978276633277) ^ 143817516708 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (2 : ZMod 11655978276633277) ^ 777078636 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide

private theorem prime_eighteenP_116559782766332771 : Nat.Prime 116559782766332771 := by
  apply lucas_primality 116559782766332771 (2 : ZMod 116559782766332771)
  · rw [← eighteenPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 1), (11655978276633277, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 1), (11655978276633277, 1)] : List FactorBlock).map factorBlockValue).prod = 116559782766332771 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eighteenP_2
      · exact prime_eighteenP_5
      · exact prime_eighteenP_11655978276633277
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 116559782766332771) ^ 58279891383166385 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (2 : ZMod 116559782766332771) ^ 23311956553266554 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (2 : ZMod 116559782766332771) ^ 10 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide

private theorem prime_eighteenP_4177 : Nat.Prime 4177 := by norm_num
private theorem prime_eighteenP_17047 : Nat.Prime 17047 := by norm_num
private theorem prime_eighteenP_2431189 : Nat.Prime 2431189 := by norm_num
private theorem prime_eighteenP_5024269 : Nat.Prime 5024269 := by norm_num
private theorem prime_eighteenP_87849902605848473 : Nat.Prime 87849902605848473 := by
  apply lucas_primality 87849902605848473 (3 : ZMod 87849902605848473)
  · rw [← eighteenPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (29, 1), (31, 1), (2431189, 1), (5024269, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (29, 1), (31, 1), (2431189, 1), (5024269, 1)] : List FactorBlock).map factorBlockValue).prod = 87849902605848473 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eighteenP_2
      · exact prime_eighteenP_29
      · exact prime_eighteenP_31
      · exact prime_eighteenP_2431189
      · exact prime_eighteenP_5024269
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 87849902605848473) ^ 43924951302924236 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (3 : ZMod 87849902605848473) ^ 3029306986408568 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (3 : ZMod 87849902605848473) ^ 2833867825995112 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (3 : ZMod 87849902605848473) ^ 36134542648 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (3 : ZMod 87849902605848473) ^ 17485111288 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide

private theorem prime_eighteenP_42695052666442357879 : Nat.Prime 42695052666442357879 := by
  apply lucas_primality 42695052666442357879 (3 : ZMod 42695052666442357879)
  · rw [← eighteenPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 5), (87849902605848473, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 5), (87849902605848473, 1)] : List FactorBlock).map factorBlockValue).prod = 42695052666442357879 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eighteenP_2
      · exact prime_eighteenP_3
      · exact prime_eighteenP_87849902605848473
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 42695052666442357879) ^ 21347526333221178939 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (3 : ZMod 42695052666442357879) ^ 14231684222147452626 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (3 : ZMod 42695052666442357879) ^ 486 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide

private theorem prime_eighteenP_3137 : Nat.Prime 3137 := by norm_num
private theorem prime_eighteenP_19309 : Nat.Prime 19309 := by norm_num
private theorem prime_eighteenP_821 : Nat.Prime 821 := by norm_num
private theorem prime_eighteenP_223 : Nat.Prime 223 := by norm_num
private theorem prime_eighteenP_5437 : Nat.Prime 5437 := by norm_num
private theorem prime_eighteenP_14347 : Nat.Prime 14347 := by norm_num
private theorem prime_eighteenP_312018557 : Nat.Prime 312018557 := by
  apply lucas_primality 312018557 (2 : ZMod 312018557)
  · rw [← eighteenPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (5437, 1), (14347, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (5437, 1), (14347, 1)] : List FactorBlock).map factorBlockValue).prod = 312018557 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eighteenP_2
      · exact prime_eighteenP_5437
      · exact prime_eighteenP_14347
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 312018557) ^ 156009278 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (2 : ZMod 312018557) ^ 57388 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (2 : ZMod 312018557) ^ 21748 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide

private theorem prime_eighteenP_4368259799 : Nat.Prime 4368259799 := by
  apply lucas_primality 4368259799 (7 : ZMod 4368259799)
  · rw [← eighteenPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (7, 1), (312018557, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (7, 1), (312018557, 1)] : List FactorBlock).map factorBlockValue).prod = 4368259799 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eighteenP_2
      · exact prime_eighteenP_7
      · exact prime_eighteenP_312018557
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 4368259799) ^ 2184129899 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (7 : ZMod 4368259799) ^ 624037114 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (7 : ZMod 4368259799) ^ 14 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide

private theorem prime_eighteenP_52419117589 : Nat.Prime 52419117589 := by
  apply lucas_primality 52419117589 (2 : ZMod 52419117589)
  · rw [← eighteenPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (4368259799, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (4368259799, 1)] : List FactorBlock).map factorBlockValue).prod = 52419117589 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eighteenP_2
      · exact prime_eighteenP_3
      · exact prime_eighteenP_4368259799
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 52419117589) ^ 26209558794 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (2 : ZMod 52419117589) ^ 17473039196 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (2 : ZMod 52419117589) ^ 12 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide

private theorem prime_eighteenP_13372745926364969 : Nat.Prime 13372745926364969 := by
  apply lucas_primality 13372745926364969 (3 : ZMod 13372745926364969)
  · rw [← eighteenPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (11, 1), (13, 1), (223, 1), (52419117589, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (11, 1), (13, 1), (223, 1), (52419117589, 1)] : List FactorBlock).map factorBlockValue).prod = 13372745926364969 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eighteenP_2
      · exact prime_eighteenP_11
      · exact prime_eighteenP_13
      · exact prime_eighteenP_223
      · exact prime_eighteenP_52419117589
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 13372745926364969) ^ 6686372963182484 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (3 : ZMod 13372745926364969) ^ 1215704175124088 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (3 : ZMod 13372745926364969) ^ 1028672763566536 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (3 : ZMod 13372745926364969) ^ 59967470521816 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (3 : ZMod 13372745926364969) ^ 255112 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide

private theorem prime_eighteenP_43916097622182558197 : Nat.Prime 43916097622182558197 := by
  apply lucas_primality 43916097622182558197 (2 : ZMod 43916097622182558197)
  · rw [← eighteenPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (821, 1), (13372745926364969, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (821, 1), (13372745926364969, 1)] : List FactorBlock).map factorBlockValue).prod = 43916097622182558197 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eighteenP_2
      · exact prime_eighteenP_821
      · exact prime_eighteenP_13372745926364969
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 43916097622182558197) ^ 21958048811091279098 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (2 : ZMod 43916097622182558197) ^ 53490983705459876 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (2 : ZMod 43916097622182558197) ^ 3284 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide

private theorem prime_eighteenP_210193 : Nat.Prime 210193 := by norm_num
private theorem prime_eighteenP_439 : Nat.Prime 439 := by norm_num
private theorem prime_eighteenP_853 : Nat.Prime 853 := by norm_num
private theorem prime_eighteenP_479 : Nat.Prime 479 := by norm_num
private theorem prime_eighteenP_6343 : Nat.Prime 6343 := by norm_num
private theorem prime_eighteenP_44960719007 : Nat.Prime 44960719007 := by
  apply lucas_primality 44960719007 (5 : ZMod 44960719007)
  · rw [← eighteenPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (7, 2), (151, 1), (479, 1), (6343, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (7, 2), (151, 1), (479, 1), (6343, 1)] : List FactorBlock).map factorBlockValue).prod = 44960719007 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eighteenP_2
      · exact prime_eighteenP_7
      · exact prime_eighteenP_151
      · exact prime_eighteenP_479
      · exact prime_eighteenP_6343
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 44960719007) ^ 22480359503 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (5 : ZMod 44960719007) ^ 6422959858 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (5 : ZMod 44960719007) ^ 297753106 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (5 : ZMod 44960719007) ^ 93863714 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (5 : ZMod 44960719007) ^ 7088242 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide

private theorem prime_eighteenP_1348821570211 : Nat.Prime 1348821570211 := by
  apply lucas_primality 1348821570211 (2 : ZMod 1348821570211)
  · rw [← eighteenPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (5, 1), (44960719007, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (5, 1), (44960719007, 1)] : List FactorBlock).map factorBlockValue).prod = 1348821570211 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eighteenP_2
      · exact prime_eighteenP_3
      · exact prime_eighteenP_5
      · exact prime_eighteenP_44960719007
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1348821570211) ^ 674410785105 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (2 : ZMod 1348821570211) ^ 449607190070 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (2 : ZMod 1348821570211) ^ 269764314042 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (2 : ZMod 1348821570211) ^ 30 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide

private theorem prime_eighteenP_8081426670915240593 : Nat.Prime 8081426670915240593 := by
  apply lucas_primality 8081426670915240593 (3 : ZMod 8081426670915240593)
  · rw [← eighteenPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 4), (439, 1), (853, 1), (1348821570211, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 4), (439, 1), (853, 1), (1348821570211, 1)] : List FactorBlock).map factorBlockValue).prod = 8081426670915240593 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eighteenP_2
      · exact prime_eighteenP_439
      · exact prime_eighteenP_853
      · exact prime_eighteenP_1348821570211
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 8081426670915240593) ^ 4040713335457620296 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (3 : ZMod 8081426670915240593) ^ 18408716790239728 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (3 : ZMod 8081426670915240593) ^ 9474122709162064 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (3 : ZMod 8081426670915240593) ^ 5991472 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide

private theorem prime_eighteenP_11249345925914014905457 : Nat.Prime 11249345925914014905457 := by
  apply lucas_primality 11249345925914014905457 (5 : ZMod 11249345925914014905457)
  · rw [← eighteenPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 4), (3, 1), (29, 1), (8081426670915240593, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 4), (3, 1), (29, 1), (8081426670915240593, 1)] : List FactorBlock).map factorBlockValue).prod = 11249345925914014905457 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eighteenP_2
      · exact prime_eighteenP_3
      · exact prime_eighteenP_29
      · exact prime_eighteenP_8081426670915240593
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 11249345925914014905457) ^ 5624672962957007452728 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (5 : ZMod 11249345925914014905457) ^ 3749781975304671635152 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (5 : ZMod 11249345925914014905457) ^ 387908480203931548464 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (5 : ZMod 11249345925914014905457) ^ 1392 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide

private theorem prime_eighteenP_3181 : Nat.Prime 3181 := by norm_num
private theorem prime_eighteenP_73571 : Nat.Prime 73571 := by norm_num
private theorem prime_eighteenP_455881 : Nat.Prime 455881 := by norm_num
private theorem prime_eighteenP_7524701 : Nat.Prime 7524701 := by norm_num
private theorem prime_eighteenP_8487862729 : Nat.Prime 8487862729 := by
  apply lucas_primality 8487862729 (7 : ZMod 8487862729)
  · rw [← eighteenPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (3, 1), (47, 1), (7524701, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (3, 1), (47, 1), (7524701, 1)] : List FactorBlock).map factorBlockValue).prod = 8487862729 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eighteenP_2
      · exact prime_eighteenP_3
      · exact prime_eighteenP_47
      · exact prime_eighteenP_7524701
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 8487862729) ^ 4243931364 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (7 : ZMod 8487862729) ^ 2829287576 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (7 : ZMod 8487862729) ^ 180592824 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (7 : ZMod 8487862729) ^ 1128 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide

private theorem prime_eighteenP_19946477413151 : Nat.Prime 19946477413151 := by
  apply lucas_primality 19946477413151 (11 : ZMod 19946477413151)
  · rw [← eighteenPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 2), (47, 1), (8487862729, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 2), (47, 1), (8487862729, 1)] : List FactorBlock).map factorBlockValue).prod = 19946477413151 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eighteenP_2
      · exact prime_eighteenP_5
      · exact prime_eighteenP_47
      · exact prime_eighteenP_8487862729
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 19946477413151) ^ 9973238706575 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (11 : ZMod 19946477413151) ^ 3989295482630 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (11 : ZMod 19946477413151) ^ 424393136450 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (11 : ZMod 19946477413151) ^ 2350 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide

private theorem prime_eighteenP_150791 : Nat.Prime 150791 := by norm_num
private theorem prime_eighteenP_26171 : Nat.Prime 26171 := by norm_num
private theorem prime_eighteenP_2503121 : Nat.Prime 2503121 := by norm_num
private theorem prime_eighteenP_5760217 : Nat.Prime 5760217 := by norm_num
private theorem prime_eighteenP_576021701 : Nat.Prime 576021701 := by
  apply lucas_primality 576021701 (2 : ZMod 576021701)
  · rw [← eighteenPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (5, 2), (5760217, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (5, 2), (5760217, 1)] : List FactorBlock).map factorBlockValue).prod = 576021701 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eighteenP_2
      · exact prime_eighteenP_5
      · exact prime_eighteenP_5760217
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 576021701) ^ 288010850 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (2 : ZMod 576021701) ^ 115204340 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (2 : ZMod 576021701) ^ 100 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide

private theorem prime_eighteenP_75469418233448948783 : Nat.Prime 75469418233448948783 := by
  apply lucas_primality 75469418233448948783 (5 : ZMod 75469418233448948783)
  · rw [← eighteenPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (26171, 1), (2503121, 1), (576021701, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (26171, 1), (2503121, 1), (576021701, 1)] : List FactorBlock).map factorBlockValue).prod = 75469418233448948783 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eighteenP_2
      · exact prime_eighteenP_26171
      · exact prime_eighteenP_2503121
      · exact prime_eighteenP_576021701
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 75469418233448948783) ^ 37734709116724474391 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (5 : ZMod 75469418233448948783) ^ 2883704032457642 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (5 : ZMod 75469418233448948783) ^ 30150127873742 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (5 : ZMod 75469418233448948783) ^ 131018359382 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide

private theorem prime_eighteenP_12829801099686321293111 : Nat.Prime 12829801099686321293111 := by
  apply lucas_primality 12829801099686321293111 (14 : ZMod 12829801099686321293111)
  · rw [← eighteenPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 1), (17, 1), (75469418233448948783, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 1), (17, 1), (75469418233448948783, 1)] : List FactorBlock).map factorBlockValue).prod = 12829801099686321293111 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eighteenP_2
      · exact prime_eighteenP_5
      · exact prime_eighteenP_17
      · exact prime_eighteenP_75469418233448948783
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (14 : ZMod 12829801099686321293111) ^ 6414900549843160646555 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (14 : ZMod 12829801099686321293111) ^ 2565960219937264258622 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (14 : ZMod 12829801099686321293111) ^ 754694182334489487830 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (14 : ZMod 12829801099686321293111) ^ 170 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide

private theorem prime_eighteenP_8233 : Nat.Prime 8233 := by norm_num
private theorem prime_eighteenP_93811 : Nat.Prime 93811 := by norm_num
private theorem prime_eighteenP_8274073 : Nat.Prime 8274073 := by norm_num
private theorem prime_eighteenP_1429 : Nat.Prime 1429 := by norm_num
private theorem prime_eighteenP_217223 : Nat.Prime 217223 := by norm_num
private theorem prime_eighteenP_277508030299 : Nat.Prime 277508030299 := by
  apply lucas_primality 277508030299 (3 : ZMod 277508030299)
  · rw [← eighteenPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (149, 1), (1429, 1), (217223, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (149, 1), (1429, 1), (217223, 1)] : List FactorBlock).map factorBlockValue).prod = 277508030299 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eighteenP_2
      · exact prime_eighteenP_3
      · exact prime_eighteenP_149
      · exact prime_eighteenP_1429
      · exact prime_eighteenP_217223
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 277508030299) ^ 138754015149 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (3 : ZMod 277508030299) ^ 92502676766 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (3 : ZMod 277508030299) ^ 1862470002 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (3 : ZMod 277508030299) ^ 194197362 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (3 : ZMod 277508030299) ^ 1277526 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide

private theorem prime_eighteenP_10897001 : Nat.Prime 10897001 := by norm_num
private theorem prime_eighteenP_421 : Nat.Prime 421 := by norm_num
private theorem prime_eighteenP_127 : Nat.Prime 127 := by norm_num
private theorem prime_eighteenP_14143 : Nat.Prime 14143 := by norm_num
private theorem prime_eighteenP_76679 : Nat.Prime 76679 := by norm_num
private theorem prime_eighteenP_104948605941079 : Nat.Prime 104948605941079 := by
  apply lucas_primality 104948605941079 (3 : ZMod 104948605941079)
  · rw [← eighteenPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (127, 2), (14143, 1), (76679, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (127, 2), (14143, 1), (76679, 1)] : List FactorBlock).map factorBlockValue).prod = 104948605941079 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eighteenP_2
      · exact prime_eighteenP_3
      · exact prime_eighteenP_127
      · exact prime_eighteenP_14143
      · exact prime_eighteenP_76679
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 104948605941079) ^ 52474302970539 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (3 : ZMod 104948605941079) ^ 34982868647026 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (3 : ZMod 104948605941079) ^ 826366975914 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (3 : ZMod 104948605941079) ^ 7420533546 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (3 : ZMod 104948605941079) ^ 1368674682 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide

private theorem prime_eighteenP_150223434544060480601 : Nat.Prime 150223434544060480601 := by
  apply lucas_primality 150223434544060480601 (3 : ZMod 150223434544060480601)
  · rw [← eighteenPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (5, 2), (17, 1), (421, 1), (104948605941079, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (5, 2), (17, 1), (421, 1), (104948605941079, 1)] : List FactorBlock).map factorBlockValue).prod = 150223434544060480601 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eighteenP_2
      · exact prime_eighteenP_5
      · exact prime_eighteenP_17
      · exact prime_eighteenP_421
      · exact prime_eighteenP_104948605941079
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 150223434544060480601) ^ 75111717272030240300 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (3 : ZMod 150223434544060480601) ^ 30044686908812096120 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (3 : ZMod 150223434544060480601) ^ 8836672620238851800 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (3 : ZMod 150223434544060480601) ^ 356825260199668600 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (3 : ZMod 150223434544060480601) ^ 1431400 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide

private theorem prime_eighteenP_67 : Nat.Prime 67 := by norm_num
private theorem prime_eighteenP_12583 : Nat.Prime 12583 := by norm_num
private theorem prime_eighteenP_277259 : Nat.Prime 277259 := by norm_num
private theorem prime_eighteenP_2674733 : Nat.Prime 2674733 := by norm_num
private theorem prime_eighteenP_239 : Nat.Prime 239 := by norm_num
private theorem prime_eighteenP_283 : Nat.Prime 283 := by norm_num
private theorem prime_eighteenP_1997 : Nat.Prime 1997 := by norm_num
private theorem prime_eighteenP_2431279603 : Nat.Prime 2431279603 := by
  apply lucas_primality 2431279603 (2 : ZMod 2431279603)
  · rw [← eighteenPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 2), (239, 1), (283, 1), (1997, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 2), (239, 1), (283, 1), (1997, 1)] : List FactorBlock).map factorBlockValue).prod = 2431279603 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eighteenP_2
      · exact prime_eighteenP_3
      · exact prime_eighteenP_239
      · exact prime_eighteenP_283
      · exact prime_eighteenP_1997
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 2431279603) ^ 1215639801 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (2 : ZMod 2431279603) ^ 810426534 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (2 : ZMod 2431279603) ^ 10172718 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (2 : ZMod 2431279603) ^ 8591094 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (2 : ZMod 2431279603) ^ 1217466 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide

private theorem prime_eighteenP_1049 : Nat.Prime 1049 := by norm_num
private theorem prime_eighteenP_139537 : Nat.Prime 139537 := by norm_num
private theorem prime_eighteenP_5879 : Nat.Prime 5879 := by norm_num
private theorem prime_eighteenP_175593973 : Nat.Prime 175593973 := by
  apply lucas_primality 175593973 (5 : ZMod 175593973)
  · rw [← eighteenPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (19, 1), (131, 1), (5879, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (19, 1), (131, 1), (5879, 1)] : List FactorBlock).map factorBlockValue).prod = 175593973 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eighteenP_2
      · exact prime_eighteenP_3
      · exact prime_eighteenP_19
      · exact prime_eighteenP_131
      · exact prime_eighteenP_5879
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 175593973) ^ 87796986 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (5 : ZMod 175593973) ^ 58531324 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (5 : ZMod 175593973) ^ 9241788 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (5 : ZMod 175593973) ^ 1340412 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (5 : ZMod 175593973) ^ 29868 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide

private theorem prime_eighteenP_229 : Nat.Prime 229 := by norm_num
private theorem prime_eighteenP_372958561 : Nat.Prime 372958561 := by
  apply lucas_primality 372958561 (11 : ZMod 372958561)
  · rw [← eighteenPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 5), (3, 3), (5, 1), (13, 1), (29, 1), (229, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 5), (3, 3), (5, 1), (13, 1), (29, 1), (229, 1)] : List FactorBlock).map factorBlockValue).prod = 372958561 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eighteenP_2
      · exact prime_eighteenP_3
      · exact prime_eighteenP_5
      · exact prime_eighteenP_13
      · exact prime_eighteenP_29
      · exact prime_eighteenP_229
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 372958561) ^ 186479280 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (11 : ZMod 372958561) ^ 124319520 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (11 : ZMod 372958561) ^ 74591712 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (11 : ZMod 372958561) ^ 28689120 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (11 : ZMod 372958561) ^ 12860640 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (11 : ZMod 372958561) ^ 1628640 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide

private theorem prime_eighteenP_55197867029 : Nat.Prime 55197867029 := by
  apply lucas_primality 55197867029 (2 : ZMod 55197867029)
  · rw [← eighteenPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (37, 1), (372958561, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (37, 1), (372958561, 1)] : List FactorBlock).map factorBlockValue).prod = 55197867029 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eighteenP_2
      · exact prime_eighteenP_37
      · exact prime_eighteenP_372958561
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 55197867029) ^ 27598933514 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (2 : ZMod 55197867029) ^ 1491834244 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (2 : ZMod 55197867029) ^ 148 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide

private theorem prime_eighteenP_919 : Nat.Prime 919 := by norm_num
private theorem prime_eighteenP_11257 : Nat.Prime 11257 := by norm_num
private theorem prime_eighteenP_425291 : Nat.Prime 425291 := by norm_num
private theorem prime_eighteenP_443 : Nat.Prime 443 := by norm_num
private theorem prime_eighteenP_292231 : Nat.Prime 292231 := by norm_num
private theorem prime_eighteenP_4610820719 : Nat.Prime 4610820719 := by
  apply lucas_primality 4610820719 (13 : ZMod 4610820719)
  · rw [← eighteenPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (7, 3), (23, 1), (292231, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (7, 3), (23, 1), (292231, 1)] : List FactorBlock).map factorBlockValue).prod = 4610820719 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eighteenP_2
      · exact prime_eighteenP_7
      · exact prime_eighteenP_23
      · exact prime_eighteenP_292231
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (13 : ZMod 4610820719) ^ 2305410359 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (13 : ZMod 4610820719) ^ 658688674 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (13 : ZMod 4610820719) ^ 200470466 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (13 : ZMod 4610820719) ^ 15778 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide

private theorem prime_eighteenP_302303849620517 : Nat.Prime 302303849620517 := by
  apply lucas_primality 302303849620517 (2 : ZMod 302303849620517)
  · rw [← eighteenPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (37, 1), (443, 1), (4610820719, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (37, 1), (443, 1), (4610820719, 1)] : List FactorBlock).map factorBlockValue).prod = 302303849620517 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eighteenP_2
      · exact prime_eighteenP_37
      · exact prime_eighteenP_443
      · exact prime_eighteenP_4610820719
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 302303849620517) ^ 151151924810258 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (2 : ZMod 302303849620517) ^ 8170374314068 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (2 : ZMod 302303849620517) ^ 682401466412 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (2 : ZMod 302303849620517) ^ 65564 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide

private theorem prime_eighteenP_963499 : Nat.Prime 963499 := by norm_num
private theorem prime_eighteenP_101 : Nat.Prime 101 := by norm_num
private theorem prime_eighteenP_1146931 : Nat.Prime 1146931 := by norm_num
private theorem prime_eighteenP_55052689 : Nat.Prime 55052689 := by
  apply lucas_primality 55052689 (7 : ZMod 55052689)
  · rw [← eighteenPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 4), (3, 1), (1146931, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 4), (3, 1), (1146931, 1)] : List FactorBlock).map factorBlockValue).prod = 55052689 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eighteenP_2
      · exact prime_eighteenP_3
      · exact prime_eighteenP_1146931
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 55052689) ^ 27526344 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (7 : ZMod 55052689) ^ 18350896 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (7 : ZMod 55052689) ^ 48 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide

private theorem prime_eighteenP_11120643179 : Nat.Prime 11120643179 := by
  apply lucas_primality 11120643179 (2 : ZMod 11120643179)
  · rw [← eighteenPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (101, 1), (55052689, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (101, 1), (55052689, 1)] : List FactorBlock).map factorBlockValue).prod = 11120643179 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eighteenP_2
      · exact prime_eighteenP_101
      · exact prime_eighteenP_55052689
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 11120643179) ^ 5560321589 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (2 : ZMod 11120643179) ^ 110105378 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (2 : ZMod 11120643179) ^ 202 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide

private theorem prime_eighteenP_6914711 : Nat.Prime 6914711 := by norm_num
private theorem prime_eighteenP_19471826177 : Nat.Prime 19471826177 := by
  apply lucas_primality 19471826177 (3 : ZMod 19471826177)
  · rw [← eighteenPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 8), (11, 1), (6914711, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 8), (11, 1), (6914711, 1)] : List FactorBlock).map factorBlockValue).prod = 19471826177 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eighteenP_2
      · exact prime_eighteenP_11
      · exact prime_eighteenP_6914711
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 19471826177) ^ 9735913088 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (3 : ZMod 19471826177) ^ 1770166016 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (3 : ZMod 19471826177) ^ 2816 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide

private theorem prime_eighteenP_1299235385747572180099 : Nat.Prime 1299235385747572180099 := by
  apply lucas_primality 1299235385747572180099 (2 : ZMod 1299235385747572180099)
  · rw [← eighteenPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (11120643179, 1), (19471826177, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (11120643179, 1), (19471826177, 1)] : List FactorBlock).map factorBlockValue).prod = 1299235385747572180099 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eighteenP_2
      · exact prime_eighteenP_3
      · exact prime_eighteenP_11120643179
      · exact prime_eighteenP_19471826177
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1299235385747572180099) ^ 649617692873786090049 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (2 : ZMod 1299235385747572180099) ^ 433078461915857393366 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (2 : ZMod 1299235385747572180099) ^ 116830957062 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (2 : ZMod 1299235385747572180099) ^ 66723859074 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide

private theorem prime_eighteenP_103 : Nat.Prime 103 := by norm_num
private theorem prime_eighteenP_5009 : Nat.Prime 5009 := by norm_num
private theorem prime_eighteenP_107 : Nat.Prime 107 := by norm_num
private theorem prime_eighteenP_61717 : Nat.Prime 61717 := by norm_num
private theorem prime_eighteenP_35279 : Nat.Prime 35279 := by norm_num
private theorem prime_eighteenP_7190123 : Nat.Prime 7190123 := by norm_num
private theorem prime_eighteenP_1521962095903 : Nat.Prime 1521962095903 := by
  apply lucas_primality 1521962095903 (3 : ZMod 1521962095903)
  · rw [← eighteenPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (35279, 1), (7190123, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (35279, 1), (7190123, 1)] : List FactorBlock).map factorBlockValue).prod = 1521962095903 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eighteenP_2
      · exact prime_eighteenP_3
      · exact prime_eighteenP_35279
      · exact prime_eighteenP_7190123
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1521962095903) ^ 760981047951 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (3 : ZMod 1521962095903) ^ 507320698634 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (3 : ZMod 1521962095903) ^ 43140738 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (3 : ZMod 1521962095903) ^ 211674 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide

private theorem prime_eighteenP_563585608037072707 : Nat.Prime 563585608037072707 := by
  apply lucas_primality 563585608037072707 (3 : ZMod 563585608037072707)
  · rw [← eighteenPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (61717, 1), (1521962095903, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (61717, 1), (1521962095903, 1)] : List FactorBlock).map factorBlockValue).prod = 563585608037072707 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eighteenP_2
      · exact prime_eighteenP_3
      · exact prime_eighteenP_61717
      · exact prime_eighteenP_1521962095903
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 563585608037072707) ^ 281792804018536353 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (3 : ZMod 563585608037072707) ^ 187861869345690902 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (3 : ZMod 563585608037072707) ^ 9131772575418 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (3 : ZMod 563585608037072707) ^ 370302 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide

private theorem prime_eighteenP_2291539082278737626663 : Nat.Prime 2291539082278737626663 := by
  apply lucas_primality 2291539082278737626663 (10 : ZMod 2291539082278737626663)
  · rw [← eighteenPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (19, 1), (107, 1), (563585608037072707, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (19, 1), (107, 1), (563585608037072707, 1)] : List FactorBlock).map factorBlockValue).prod = 2291539082278737626663 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eighteenP_2
      · exact prime_eighteenP_19
      · exact prime_eighteenP_107
      · exact prime_eighteenP_563585608037072707
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (10 : ZMod 2291539082278737626663) ^ 1145769541139368813331 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (10 : ZMod 2291539082278737626663) ^ 120607320119933559298 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (10 : ZMod 2291539082278737626663) ^ 21416253105408762866 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (10 : ZMod 2291539082278737626663) ^ 4066 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide

private theorem prime_eighteenP_8713 : Nat.Prime 8713 := by norm_num
private theorem prime_eighteenP_712477 : Nat.Prime 712477 := by norm_num
private theorem prime_eighteenP_13229 : Nat.Prime 13229 := by norm_num
private theorem prime_eighteenP_23415331 : Nat.Prime 23415331 := by
  apply lucas_primality 23415331 (2 : ZMod 23415331)
  · rw [← eighteenPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (5, 1), (59, 1), (13229, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (5, 1), (59, 1), (13229, 1)] : List FactorBlock).map factorBlockValue).prod = 23415331 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eighteenP_2
      · exact prime_eighteenP_3
      · exact prime_eighteenP_5
      · exact prime_eighteenP_59
      · exact prime_eighteenP_13229
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 23415331) ^ 11707665 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (2 : ZMod 23415331) ^ 7805110 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (2 : ZMod 23415331) ^ 4683066 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (2 : ZMod 23415331) ^ 396870 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (2 : ZMod 23415331) ^ 1770 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide

private theorem prime_eighteenP_2383 : Nat.Prime 2383 := by norm_num
private theorem prime_eighteenP_8291 : Nat.Prime 8291 := by norm_num
private theorem prime_eighteenP_7705406671 : Nat.Prime 7705406671 := by
  apply lucas_primality 7705406671 (6 : ZMod 7705406671)
  · rw [← eighteenPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (5, 1), (13, 1), (2383, 1), (8291, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (5, 1), (13, 1), (2383, 1), (8291, 1)] : List FactorBlock).map factorBlockValue).prod = 7705406671 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eighteenP_2
      · exact prime_eighteenP_3
      · exact prime_eighteenP_5
      · exact prime_eighteenP_13
      · exact prime_eighteenP_2383
      · exact prime_eighteenP_8291
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 7705406671) ^ 3852703335 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (6 : ZMod 7705406671) ^ 2568468890 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (6 : ZMod 7705406671) ^ 1541081334 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (6 : ZMod 7705406671) ^ 592723590 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (6 : ZMod 7705406671) ^ 3233490 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (6 : ZMod 7705406671) ^ 929370 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide

private theorem prime_eighteenP_139 : Nat.Prime 139 := by norm_num
private theorem prime_eighteenP_577 : Nat.Prime 577 := by norm_num
private theorem prime_eighteenP_2303321 : Nat.Prime 2303321 := by norm_num
private theorem prime_eighteenP_463 : Nat.Prime 463 := by norm_num
private theorem prime_eighteenP_34057 : Nat.Prime 34057 := by norm_num
private theorem prime_eighteenP_20025517 : Nat.Prime 20025517 := by
  apply lucas_primality 20025517 (2 : ZMod 20025517)
  · rw [← eighteenPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (7, 2), (34057, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (7, 2), (34057, 1)] : List FactorBlock).map factorBlockValue).prod = 20025517 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eighteenP_2
      · exact prime_eighteenP_3
      · exact prime_eighteenP_7
      · exact prime_eighteenP_34057
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 20025517) ^ 10012758 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (2 : ZMod 20025517) ^ 6675172 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (2 : ZMod 20025517) ^ 2860788 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (2 : ZMod 20025517) ^ 588 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide

private theorem prime_eighteenP_2879936805405053 : Nat.Prime 2879936805405053 := by
  apply lucas_primality 2879936805405053 (2 : ZMod 2879936805405053)
  · rw [← eighteenPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (19, 1), (61, 1), (67, 1), (463, 1), (20025517, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (19, 1), (61, 1), (67, 1), (463, 1), (20025517, 1)] : List FactorBlock).map factorBlockValue).prod = 2879936805405053 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eighteenP_2
      · exact prime_eighteenP_19
      · exact prime_eighteenP_61
      · exact prime_eighteenP_67
      · exact prime_eighteenP_463
      · exact prime_eighteenP_20025517
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 2879936805405053) ^ 1439968402702526 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (2 : ZMod 2879936805405053) ^ 151575621337108 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (2 : ZMod 2879936805405053) ^ 47212078777132 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (2 : ZMod 2879936805405053) ^ 42984131423956 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (2 : ZMod 2879936805405053) ^ 6220165886404 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (2 : ZMod 2879936805405053) ^ 143813356 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide

private theorem prime_eighteenP_5759873610810107 : Nat.Prime 5759873610810107 := by
  apply lucas_primality 5759873610810107 (2 : ZMod 5759873610810107)
  · rw [← eighteenPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (2879936805405053, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (2879936805405053, 1)] : List FactorBlock).map factorBlockValue).prod = 5759873610810107 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_eighteenP_2
      · exact prime_eighteenP_2879936805405053
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 5759873610810107) ^ 2879936805405053 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (2 : ZMod 5759873610810107) ^ 2 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide

private theorem prime_eighteenP_331 : Nat.Prime 331 := by norm_num
private theorem prime_eighteenP_7129 : Nat.Prime 7129 := by norm_num
private theorem prime_eighteenP_199 : Nat.Prime 199 := by norm_num
private theorem prime_eighteenP_5449 : Nat.Prime 5449 := by norm_num
private theorem prime_eighteenP_8089 : Nat.Prime 8089 := by norm_num
private theorem prime_eighteenP_4121269 : Nat.Prime 4121269 := by norm_num
private theorem prime_eighteenP_123638071 : Nat.Prime 123638071 := by
  apply lucas_primality 123638071 (7 : ZMod 123638071)
  · rw [← eighteenPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (5, 1), (4121269, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (5, 1), (4121269, 1)] : List FactorBlock).map factorBlockValue).prod = 123638071 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eighteenP_2
      · exact prime_eighteenP_3
      · exact prime_eighteenP_5
      · exact prime_eighteenP_4121269
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 123638071) ^ 61819035 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (7 : ZMod 123638071) ^ 41212690 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (7 : ZMod 123638071) ^ 24727614 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (7 : ZMod 123638071) ^ 30 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide

private theorem prime_eighteenP_741828427 : Nat.Prime 741828427 := by
  apply lucas_primality 741828427 (2 : ZMod 741828427)
  · rw [← eighteenPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (123638071, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (123638071, 1)] : List FactorBlock).map factorBlockValue).prod = 741828427 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eighteenP_2
      · exact prime_eighteenP_3
      · exact prime_eighteenP_123638071
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 741828427) ^ 370914213 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (2 : ZMod 741828427) ^ 247276142 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (2 : ZMod 741828427) ^ 6 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide

private theorem prime_eighteenP_429449525106920937499 : Nat.Prime 429449525106920937499 := by
  apply lucas_primality 429449525106920937499 (2 : ZMod 429449525106920937499)
  · rw [← eighteenPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (11, 1), (199, 1), (5449, 1), (8089, 1), (741828427, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (11, 1), (199, 1), (5449, 1), (8089, 1), (741828427, 1)] : List FactorBlock).map factorBlockValue).prod = 429449525106920937499 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eighteenP_2
      · exact prime_eighteenP_3
      · exact prime_eighteenP_11
      · exact prime_eighteenP_199
      · exact prime_eighteenP_5449
      · exact prime_eighteenP_8089
      · exact prime_eighteenP_741828427
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 429449525106920937499) ^ 214724762553460468749 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (2 : ZMod 429449525106920937499) ^ 143149841702306979166 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (2 : ZMod 429449525106920937499) ^ 39040865918810994318 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (2 : ZMod 429449525106920937499) ^ 2158037814607642902 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (2 : ZMod 429449525106920937499) ^ 78812539017603402 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (2 : ZMod 429449525106920937499) ^ 53090558178627882 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (2 : ZMod 429449525106920937499) ^ 578906805774 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide

private theorem prime_eighteenP_60793 : Nat.Prime 60793 := by norm_num
private theorem prime_eighteenP_33749 : Nat.Prime 33749 := by norm_num
private theorem prime_eighteenP_347 : Nat.Prime 347 := by norm_num
private theorem prime_eighteenP_109481 : Nat.Prime 109481 := by norm_num
private theorem prime_eighteenP_5205667 : Nat.Prime 5205667 := by norm_num
private theorem prime_eighteenP_791051220811877 : Nat.Prime 791051220811877 := by
  apply lucas_primality 791051220811877 (2 : ZMod 791051220811877)
  · rw [← eighteenPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (347, 1), (109481, 1), (5205667, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (347, 1), (109481, 1), (5205667, 1)] : List FactorBlock).map factorBlockValue).prod = 791051220811877 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eighteenP_2
      · exact prime_eighteenP_347
      · exact prime_eighteenP_109481
      · exact prime_eighteenP_5205667
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 791051220811877) ^ 395525610405938 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (2 : ZMod 791051220811877) ^ 2279686515308 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (2 : ZMod 791051220811877) ^ 7225465796 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (2 : ZMod 791051220811877) ^ 151959628 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide

private theorem prime_eighteenP_106788750604720147493 : Nat.Prime 106788750604720147493 := by
  apply lucas_primality 106788750604720147493 (2 : ZMod 106788750604720147493)
  · rw [← eighteenPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (33749, 1), (791051220811877, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (33749, 1), (791051220811877, 1)] : List FactorBlock).map factorBlockValue).prod = 106788750604720147493 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eighteenP_2
      · exact prime_eighteenP_33749
      · exact prime_eighteenP_791051220811877
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 106788750604720147493) ^ 53394375302360073746 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (2 : ZMod 106788750604720147493) ^ 3164204883247508 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (2 : ZMod 106788750604720147493) ^ 134996 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide

private theorem prime_eighteenP_328103 : Nat.Prime 328103 := by norm_num
private theorem prime_eighteenP_1289 : Nat.Prime 1289 := by norm_num
private theorem prime_eighteenP_11821 : Nat.Prime 11821 := by norm_num
private theorem prime_eighteenP_8699 : Nat.Prime 8699 := by norm_num
private theorem prime_eighteenP_68713 : Nat.Prime 68713 := by norm_num
private theorem prime_eighteenP_158997346943 : Nat.Prime 158997346943 := by
  apply lucas_primality 158997346943 (5 : ZMod 158997346943)
  · rw [← eighteenPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (7, 1), (19, 1), (8699, 1), (68713, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (7, 1), (19, 1), (8699, 1), (68713, 1)] : List FactorBlock).map factorBlockValue).prod = 158997346943 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eighteenP_2
      · exact prime_eighteenP_7
      · exact prime_eighteenP_19
      · exact prime_eighteenP_8699
      · exact prime_eighteenP_68713
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 158997346943) ^ 79498673471 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (5 : ZMod 158997346943) ^ 22713906706 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (5 : ZMod 158997346943) ^ 8368281418 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (5 : ZMod 158997346943) ^ 18277658 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (5 : ZMod 158997346943) ^ 2313934 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide

private theorem prime_eighteenP_1093873445440084147 : Nat.Prime 1093873445440084147 := by
  apply lucas_primality 1093873445440084147 (5 : ZMod 1093873445440084147)
  · rw [← eighteenPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (97, 1), (11821, 1), (158997346943, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (97, 1), (11821, 1), (158997346943, 1)] : List FactorBlock).map factorBlockValue).prod = 1093873445440084147 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eighteenP_2
      · exact prime_eighteenP_3
      · exact prime_eighteenP_97
      · exact prime_eighteenP_11821
      · exact prime_eighteenP_158997346943
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 1093873445440084147) ^ 546936722720042073 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (5 : ZMod 1093873445440084147) ^ 364624481813361382 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (5 : ZMod 1093873445440084147) ^ 11277045829279218 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (5 : ZMod 1093873445440084147) ^ 92536455920826 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (5 : ZMod 1093873445440084147) ^ 6879822 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide

private theorem prime_eighteenP_2820005742344536930967 : Nat.Prime 2820005742344536930967 := by
  apply lucas_primality 2820005742344536930967 (5 : ZMod 2820005742344536930967)
  · rw [← eighteenPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (1289, 1), (1093873445440084147, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (1289, 1), (1093873445440084147, 1)] : List FactorBlock).map factorBlockValue).prod = 2820005742344536930967 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eighteenP_2
      · exact prime_eighteenP_1289
      · exact prime_eighteenP_1093873445440084147
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 2820005742344536930967) ^ 1410002871172268465483 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (5 : ZMod 2820005742344536930967) ^ 2187746890880168294 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (5 : ZMod 2820005742344536930967) ^ 2578 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide

private theorem prime_eighteenP_769 : Nat.Prime 769 := by norm_num
private theorem prime_eighteenP_2143 : Nat.Prime 2143 := by norm_num
private theorem prime_eighteenP_8597 : Nat.Prime 8597 := by norm_num
private theorem prime_eighteenP_9792301 : Nat.Prime 9792301 := by norm_num
private theorem prime_eighteenP_161017 : Nat.Prime 161017 := by norm_num
private theorem prime_eighteenP_6391408799 : Nat.Prime 6391408799 := by
  apply lucas_primality 6391408799 (23 : ZMod 6391408799)
  · rw [← eighteenPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (89, 1), (223, 1), (161017, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (89, 1), (223, 1), (161017, 1)] : List FactorBlock).map factorBlockValue).prod = 6391408799 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eighteenP_2
      · exact prime_eighteenP_89
      · exact prime_eighteenP_223
      · exact prime_eighteenP_161017
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (23 : ZMod 6391408799) ^ 3195704399 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (23 : ZMod 6391408799) ^ 71813582 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (23 : ZMod 6391408799) ^ 28661026 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (23 : ZMod 6391408799) ^ 39694 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide

private theorem prime_eighteenP_24421 : Nat.Prime 24421 := by norm_num
private theorem prime_eighteenP_2273 : Nat.Prime 2273 := by norm_num
private theorem prime_eighteenP_3307 : Nat.Prime 3307 := by norm_num
private theorem prime_eighteenP_1399 : Nat.Prime 1399 := by norm_num
private theorem prime_eighteenP_385607 : Nat.Prime 385607 := by norm_num
private theorem prime_eighteenP_1078928387 : Nat.Prime 1078928387 := by
  apply lucas_primality 1078928387 (2 : ZMod 1078928387)
  · rw [← eighteenPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (1399, 1), (385607, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (1399, 1), (385607, 1)] : List FactorBlock).map factorBlockValue).prod = 1078928387 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eighteenP_2
      · exact prime_eighteenP_1399
      · exact prime_eighteenP_385607
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 1078928387) ^ 539464193 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (2 : ZMod 1078928387) ^ 771214 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (2 : ZMod 1078928387) ^ 2798 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide

private theorem prime_eighteenP_28544129406473 : Nat.Prime 28544129406473 := by
  apply lucas_primality 28544129406473 (3 : ZMod 28544129406473)
  · rw [← eighteenPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (3307, 1), (1078928387, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (3307, 1), (1078928387, 1)] : List FactorBlock).map factorBlockValue).prod = 28544129406473 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eighteenP_2
      · exact prime_eighteenP_3307
      · exact prime_eighteenP_1078928387
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 28544129406473) ^ 14272064703236 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (3 : ZMod 28544129406473) ^ 8631427096 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (3 : ZMod 28544129406473) ^ 26456 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide

private theorem prime_eighteenP_3139854234712031 : Nat.Prime 3139854234712031 := by
  apply lucas_primality 3139854234712031 (7 : ZMod 3139854234712031)
  · rw [← eighteenPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 1), (11, 1), (28544129406473, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 1), (11, 1), (28544129406473, 1)] : List FactorBlock).map factorBlockValue).prod = 3139854234712031 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eighteenP_2
      · exact prime_eighteenP_5
      · exact prime_eighteenP_11
      · exact prime_eighteenP_28544129406473
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 3139854234712031) ^ 1569927117356015 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (7 : ZMod 3139854234712031) ^ 627970846942406 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (7 : ZMod 3139854234712031) ^ 285441294064730 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (7 : ZMod 3139854234712031) ^ 110 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide

private theorem prime_eighteenP_34856564291144180525293 : Nat.Prime 34856564291144180525293 := by
  apply lucas_primality 34856564291144180525293 (5 : ZMod 34856564291144180525293)
  · rw [← eighteenPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (11, 1), (37, 1), (2273, 1), (3139854234712031, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (11, 1), (37, 1), (2273, 1), (3139854234712031, 1)] : List FactorBlock).map factorBlockValue).prod = 34856564291144180525293 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eighteenP_2
      · exact prime_eighteenP_3
      · exact prime_eighteenP_11
      · exact prime_eighteenP_37
      · exact prime_eighteenP_2273
      · exact prime_eighteenP_3139854234712031
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 34856564291144180525293) ^ 17428282145572090262646 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (5 : ZMod 34856564291144180525293) ^ 11618854763714726841764 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (5 : ZMod 34856564291144180525293) ^ 3168778571922198229572 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (5 : ZMod 34856564291144180525293) ^ 942069305166058933116 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (5 : ZMod 34856564291144180525293) ^ 15335048082333559404 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (5 : ZMod 34856564291144180525293) ^ 11101332 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide

private theorem prime_eighteenP_11489 : Nat.Prime 11489 := by norm_num
private theorem prime_eighteenP_7723 : Nat.Prime 7723 := by norm_num
private theorem prime_eighteenP_21580023643 : Nat.Prime 21580023643 := by
  apply lucas_primality 21580023643 (2 : ZMod 21580023643)
  · rw [← eighteenPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (19, 1), (127, 1), (193, 1), (7723, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (19, 1), (127, 1), (193, 1), (7723, 1)] : List FactorBlock).map factorBlockValue).prod = 21580023643 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eighteenP_2
      · exact prime_eighteenP_3
      · exact prime_eighteenP_19
      · exact prime_eighteenP_127
      · exact prime_eighteenP_193
      · exact prime_eighteenP_7723
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 21580023643) ^ 10790011821 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (2 : ZMod 21580023643) ^ 7193341214 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (2 : ZMod 21580023643) ^ 1135790718 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (2 : ZMod 21580023643) ^ 169921446 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (2 : ZMod 21580023643) ^ 111813594 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (2 : ZMod 21580023643) ^ 2794254 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide

private theorem prime_eighteenP_167 : Nat.Prime 167 := by norm_num
private theorem prime_eighteenP_18679 : Nat.Prime 18679 := by norm_num
private theorem prime_eighteenP_77218987 : Nat.Prime 77218987 := by
  apply lucas_primality 77218987 (5 : ZMod 77218987)
  · rw [← eighteenPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (13, 1), (53, 1), (18679, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (13, 1), (53, 1), (18679, 1)] : List FactorBlock).map factorBlockValue).prod = 77218987 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eighteenP_2
      · exact prime_eighteenP_3
      · exact prime_eighteenP_13
      · exact prime_eighteenP_53
      · exact prime_eighteenP_18679
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 77218987) ^ 38609493 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (5 : ZMod 77218987) ^ 25739662 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (5 : ZMod 77218987) ^ 5939922 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (5 : ZMod 77218987) ^ 1456962 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (5 : ZMod 77218987) ^ 4134 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide

private theorem prime_eighteenP_103164566633 : Nat.Prime 103164566633 := by
  apply lucas_primality 103164566633 (3 : ZMod 103164566633)
  · rw [← eighteenPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (167, 1), (77218987, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (167, 1), (77218987, 1)] : List FactorBlock).map factorBlockValue).prod = 103164566633 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eighteenP_2
      · exact prime_eighteenP_167
      · exact prime_eighteenP_77218987
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 103164566633) ^ 51582283316 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (3 : ZMod 103164566633) ^ 617751896 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (3 : ZMod 103164566633) ^ 1336 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide

private theorem prime_eighteenP_71241401185919644928609 : Nat.Prime 71241401185919644928609 := by
  apply lucas_primality 71241401185919644928609 (3 : ZMod 71241401185919644928609)
  · rw [← eighteenPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 5), (21580023643, 1), (103164566633, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 5), (21580023643, 1), (103164566633, 1)] : List FactorBlock).map factorBlockValue).prod = 71241401185919644928609 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eighteenP_2
      · exact prime_eighteenP_21580023643
      · exact prime_eighteenP_103164566633
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 71241401185919644928609) ^ 35620700592959822464304 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (3 : ZMod 71241401185919644928609) ^ 3301266132256 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (3 : ZMod 71241401185919644928609) ^ 690560756576 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide

private theorem prime_eighteenP_1483 : Nat.Prime 1483 := by norm_num
private theorem prime_eighteenP_2072201 : Nat.Prime 2072201 := by norm_num
private theorem prime_eighteenP_2567179 : Nat.Prime 2567179 := by norm_num
private theorem prime_eighteenP_191 : Nat.Prime 191 := by norm_num
private theorem prime_eighteenP_383 : Nat.Prime 383 := by norm_num
private theorem prime_eighteenP_811 : Nat.Prime 811 := by norm_num
private theorem prime_eighteenP_237308333 : Nat.Prime 237308333 := by
  apply lucas_primality 237308333 (2 : ZMod 237308333)
  · rw [← eighteenPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (191, 1), (383, 1), (811, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (191, 1), (383, 1), (811, 1)] : List FactorBlock).map factorBlockValue).prod = 237308333 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eighteenP_2
      · exact prime_eighteenP_191
      · exact prime_eighteenP_383
      · exact prime_eighteenP_811
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 237308333) ^ 118654166 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (2 : ZMod 237308333) ^ 1242452 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (2 : ZMod 237308333) ^ 619604 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (2 : ZMod 237308333) ^ 292612 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide

private theorem prime_eighteenP_277 : Nat.Prime 277 := by norm_num
private theorem prime_eighteenP_76543 : Nat.Prime 76543 := by norm_num
private theorem prime_eighteenP_6810796141 : Nat.Prime 6810796141 := by
  apply lucas_primality 6810796141 (2 : ZMod 6810796141)
  · rw [← eighteenPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (5, 1), (1483, 1), (76543, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (5, 1), (1483, 1), (76543, 1)] : List FactorBlock).map factorBlockValue).prod = 6810796141 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eighteenP_2
      · exact prime_eighteenP_3
      · exact prime_eighteenP_5
      · exact prime_eighteenP_1483
      · exact prime_eighteenP_76543
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 6810796141) ^ 3405398070 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (2 : ZMod 6810796141) ^ 2270265380 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (2 : ZMod 6810796141) ^ 1362159228 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (2 : ZMod 6810796141) ^ 4592580 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (2 : ZMod 6810796141) ^ 88980 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide

private theorem prime_eighteenP_55291 : Nat.Prime 55291 := by norm_num
private theorem prime_eighteenP_756933791 : Nat.Prime 756933791 := by
  apply lucas_primality 756933791 (11 : ZMod 756933791)
  · rw [← eighteenPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 1), (37, 2), (55291, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 1), (37, 2), (55291, 1)] : List FactorBlock).map factorBlockValue).prod = 756933791 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eighteenP_2
      · exact prime_eighteenP_5
      · exact prime_eighteenP_37
      · exact prime_eighteenP_55291
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 756933791) ^ 378466895 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (11 : ZMod 756933791) ^ 151386758 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (11 : ZMod 756933791) ^ 20457670 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (11 : ZMod 756933791) ^ 13690 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide

private theorem prime_eighteenP_1513867583 : Nat.Prime 1513867583 := by
  apply lucas_primality 1513867583 (5 : ZMod 1513867583)
  · rw [← eighteenPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (756933791, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (756933791, 1)] : List FactorBlock).map factorBlockValue).prod = 1513867583 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_eighteenP_2
      · exact prime_eighteenP_756933791
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 1513867583) ^ 756933791 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (5 : ZMod 1513867583) ^ 2 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide

private theorem prime_eighteenP_108998465977 : Nat.Prime 108998465977 := by
  apply lucas_primality 108998465977 (5 : ZMod 108998465977)
  · rw [← eighteenPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (3, 2), (1513867583, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (3, 2), (1513867583, 1)] : List FactorBlock).map factorBlockValue).prod = 108998465977 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eighteenP_2
      · exact prime_eighteenP_3
      · exact prime_eighteenP_1513867583
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 108998465977) ^ 54499232988 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (5 : ZMod 108998465977) ^ 36332821992 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (5 : ZMod 108998465977) ^ 72 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide

private theorem prime_eighteenP_402858330250993 : Nat.Prime 402858330250993 := by
  apply lucas_primality 402858330250993 (5 : ZMod 402858330250993)
  · rw [← eighteenPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 4), (3, 1), (7, 1), (11, 1), (108998465977, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 4), (3, 1), (7, 1), (11, 1), (108998465977, 1)] : List FactorBlock).map factorBlockValue).prod = 402858330250993 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eighteenP_2
      · exact prime_eighteenP_3
      · exact prime_eighteenP_7
      · exact prime_eighteenP_11
      · exact prime_eighteenP_108998465977
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 402858330250993) ^ 201429165125496 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (5 : ZMod 402858330250993) ^ 134286110083664 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (5 : ZMod 402858330250993) ^ 57551190035856 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (5 : ZMod 402858330250993) ^ 36623484568272 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (5 : ZMod 402858330250993) ^ 3696 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide

private theorem prime_eighteenP_6131 : Nat.Prime 6131 := by norm_num
private theorem prime_eighteenP_344429 : Nat.Prime 344429 := by norm_num
private theorem prime_eighteenP_126749873 : Nat.Prime 126749873 := by
  apply lucas_primality 126749873 (3 : ZMod 126749873)
  · rw [← eighteenPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 4), (23, 1), (344429, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 4), (23, 1), (344429, 1)] : List FactorBlock).map factorBlockValue).prod = 126749873 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eighteenP_2
      · exact prime_eighteenP_23
      · exact prime_eighteenP_344429
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 126749873) ^ 63374936 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (3 : ZMod 126749873) ^ 5510864 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (3 : ZMod 126749873) ^ 368 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide

private theorem prime_eighteenP_5701 : Nat.Prime 5701 := by norm_num
private theorem prime_eighteenP_43541 : Nat.Prime 43541 := by norm_num
private theorem prime_eighteenP_634031 : Nat.Prime 634031 := by norm_num
private theorem prime_eighteenP_944302595030827 : Nat.Prime 944302595030827 := by
  apply lucas_primality 944302595030827 (2 : ZMod 944302595030827)
  · rw [← eighteenPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (5701, 1), (43541, 1), (634031, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (5701, 1), (43541, 1), (634031, 1)] : List FactorBlock).map factorBlockValue).prod = 944302595030827 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eighteenP_2
      · exact prime_eighteenP_3
      · exact prime_eighteenP_5701
      · exact prime_eighteenP_43541
      · exact prime_eighteenP_634031
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 944302595030827) ^ 472151297515413 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (2 : ZMod 944302595030827) ^ 314767531676942 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (2 : ZMod 944302595030827) ^ 165638062626 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (2 : ZMod 944302595030827) ^ 21687664386 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (2 : ZMod 944302595030827) ^ 1489363446 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide

private theorem prime_eighteenP_281 : Nat.Prime 281 := by norm_num
private theorem prime_eighteenP_739 : Nat.Prime 739 := by norm_num
private theorem prime_eighteenP_8443 : Nat.Prime 8443 := by norm_num
private theorem prime_eighteenP_84294913 : Nat.Prime 84294913 := by
  apply lucas_primality 84294913 (14 : ZMod 84294913)
  · rw [← eighteenPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 8), (3, 1), (13, 1), (8443, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 8), (3, 1), (13, 1), (8443, 1)] : List FactorBlock).map factorBlockValue).prod = 84294913 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eighteenP_2
      · exact prime_eighteenP_3
      · exact prime_eighteenP_13
      · exact prime_eighteenP_8443
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (14 : ZMod 84294913) ^ 42147456 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (14 : ZMod 84294913) ^ 28098304 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (14 : ZMod 84294913) ^ 6484224 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (14 : ZMod 84294913) ^ 9984 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide

private theorem prime_eighteenP_3540386347 : Nat.Prime 3540386347 := by
  apply lucas_primality 3540386347 (11 : ZMod 3540386347)
  · rw [← eighteenPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (7, 1), (84294913, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (7, 1), (84294913, 1)] : List FactorBlock).map factorBlockValue).prod = 3540386347 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eighteenP_2
      · exact prime_eighteenP_3
      · exact prime_eighteenP_7
      · exact prime_eighteenP_84294913
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 3540386347) ^ 1770193173 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (11 : ZMod 3540386347) ^ 1180128782 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (11 : ZMod 3540386347) ^ 505769478 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (11 : ZMod 3540386347) ^ 42 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide

private theorem prime_eighteenP_1509031 : Nat.Prime 1509031 := by norm_num
private theorem prime_eighteenP_9277522589 : Nat.Prime 9277522589 := by
  apply lucas_primality 9277522589 (2 : ZMod 9277522589)
  · rw [← eighteenPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (29, 1), (53, 1), (1509031, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (29, 1), (53, 1), (1509031, 1)] : List FactorBlock).map factorBlockValue).prod = 9277522589 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eighteenP_2
      · exact prime_eighteenP_29
      · exact prime_eighteenP_53
      · exact prime_eighteenP_1509031
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 9277522589) ^ 4638761294 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (2 : ZMod 9277522589) ^ 319914572 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (2 : ZMod 9277522589) ^ 175047596 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (2 : ZMod 9277522589) ^ 6148 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide

private theorem prime_eighteenP_964862349257 : Nat.Prime 964862349257 := by
  apply lucas_primality 964862349257 (5 : ZMod 964862349257)
  · rw [← eighteenPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (13, 1), (9277522589, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (13, 1), (9277522589, 1)] : List FactorBlock).map factorBlockValue).prod = 964862349257 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eighteenP_2
      · exact prime_eighteenP_13
      · exact prime_eighteenP_9277522589
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 964862349257) ^ 482431174628 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (5 : ZMod 964862349257) ^ 74220180712 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (5 : ZMod 964862349257) ^ 104 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide

private theorem prime_eighteenP_686477545608090348877564801 : Nat.Prime 686477545608090348877564801 := by
  apply lucas_primality 686477545608090348877564801 (83 : ZMod 686477545608090348877564801)
  · rw [← eighteenPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 7), (3, 5), (5, 2), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 7), (3, 5), (5, 2), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod = 686477545608090348877564801 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eighteenP_2
      · exact prime_eighteenP_3
      · exact prime_eighteenP_5
      · exact prime_eighteenP_7
      · exact prime_eighteenP_11
      · exact prime_eighteenP_13
      · exact prime_eighteenP_17
      · exact prime_eighteenP_19
      · exact prime_eighteenP_23
      · exact prime_eighteenP_29
      · exact prime_eighteenP_37
      · exact prime_eighteenP_41
      · exact prime_eighteenP_43
      · exact prime_eighteenP_47
      · exact prime_eighteenP_53
      · exact prime_eighteenP_59
      · exact prime_eighteenP_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (83 : ZMod 686477545608090348877564801) ^ 343238772804045174438782400 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (83 : ZMod 686477545608090348877564801) ^ 228825848536030116292521600 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (83 : ZMod 686477545608090348877564801) ^ 137295509121618069775512960 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (83 : ZMod 686477545608090348877564801) ^ 98068220801155764125366400 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (83 : ZMod 686477545608090348877564801) ^ 62407049600735486261596800 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (83 : ZMod 686477545608090348877564801) ^ 52805965046776180682889600 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (83 : ZMod 686477545608090348877564801) ^ 40381032094593549933974400 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (83 : ZMod 686477545608090348877564801) ^ 36130397137267913098819200 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (83 : ZMod 686477545608090348877564801) ^ 29846849809047406472937600 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (83 : ZMod 686477545608090348877564801) ^ 23671639503727253409571200 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (83 : ZMod 686477545608090348877564801) ^ 18553447178597036456150400 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (83 : ZMod 686477545608090348877564801) ^ 16743354770929032899452800 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (83 : ZMod 686477545608090348877564801) ^ 15964594083909077880873600 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (83 : ZMod 686477545608090348877564801) ^ 14605905225704049976118400 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (83 : ZMod 686477545608090348877564801) ^ 12952406520907365073161600 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (83 : ZMod 686477545608090348877564801) ^ 11635212637425260150467200 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (83 : ZMod 686477545608090348877564801) ^ 11253730255870333588156800 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide

private theorem prime_eighteenP_25913 : Nat.Prime 25913 := by norm_num
private theorem prime_eighteenP_644701 : Nat.Prime 644701 := by norm_num
private theorem prime_eighteenP_1731666887 : Nat.Prime 1731666887 := by
  apply lucas_primality 1731666887 (5 : ZMod 1731666887)
  · rw [← eighteenPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (17, 1), (79, 1), (644701, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (17, 1), (79, 1), (644701, 1)] : List FactorBlock).map factorBlockValue).prod = 1731666887 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eighteenP_2
      · exact prime_eighteenP_17
      · exact prime_eighteenP_79
      · exact prime_eighteenP_644701
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 1731666887) ^ 865833443 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (5 : ZMod 1731666887) ^ 101862758 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (5 : ZMod 1731666887) ^ 21919834 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (5 : ZMod 1731666887) ^ 2686 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide

private theorem prime_eighteenP_9281 : Nat.Prime 9281 := by norm_num
private theorem prime_eighteenP_7603997 : Nat.Prime 7603997 := by norm_num
private theorem prime_eighteenP_14820266192971 : Nat.Prime 14820266192971 := by
  apply lucas_primality 14820266192971 (3 : ZMod 14820266192971)
  · rw [← eighteenPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (5, 1), (7, 1), (9281, 1), (7603997, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (5, 1), (7, 1), (9281, 1), (7603997, 1)] : List FactorBlock).map factorBlockValue).prod = 14820266192971 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eighteenP_2
      · exact prime_eighteenP_3
      · exact prime_eighteenP_5
      · exact prime_eighteenP_7
      · exact prime_eighteenP_9281
      · exact prime_eighteenP_7603997
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 14820266192971) ^ 7410133096485 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (3 : ZMod 14820266192971) ^ 4940088730990 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (3 : ZMod 14820266192971) ^ 2964053238594 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (3 : ZMod 14820266192971) ^ 2117180884710 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (3 : ZMod 14820266192971) ^ 1596839370 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (3 : ZMod 14820266192971) ^ 1949010 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide

private theorem prime_eighteenP_97327 : Nat.Prime 97327 := by norm_num
private theorem prime_eighteenP_208223 : Nat.Prime 208223 := by norm_num
private theorem prime_eighteenP_4129087 : Nat.Prime 4129087 := by norm_num
private theorem prime_eighteenP_1929523 : Nat.Prime 1929523 := by norm_num
private theorem prime_eighteenP_7706514863 : Nat.Prime 7706514863 := by
  apply lucas_primality 7706514863 (5 : ZMod 7706514863)
  · rw [← eighteenPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (1997, 1), (1929523, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (1997, 1), (1929523, 1)] : List FactorBlock).map factorBlockValue).prod = 7706514863 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eighteenP_2
      · exact prime_eighteenP_1997
      · exact prime_eighteenP_1929523
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 7706514863) ^ 3853257431 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (5 : ZMod 7706514863) ^ 3859046 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (5 : ZMod 7706514863) ^ 3994 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide

private theorem prime_eighteenP_625905997466200023976603201 : Nat.Prime 625905997466200023976603201 := by
  apply lucas_primality 625905997466200023976603201 (79 : ZMod 625905997466200023976603201)
  · rw [← eighteenPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 6), (3, 5), (5, 2), (7, 2), (11, 1), (13, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 6), (3, 5), (5, 2), (7, 2), (11, 1), (13, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod = 625905997466200023976603201 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eighteenP_2
      · exact prime_eighteenP_3
      · exact prime_eighteenP_5
      · exact prime_eighteenP_7
      · exact prime_eighteenP_11
      · exact prime_eighteenP_13
      · exact prime_eighteenP_19
      · exact prime_eighteenP_23
      · exact prime_eighteenP_29
      · exact prime_eighteenP_31
      · exact prime_eighteenP_37
      · exact prime_eighteenP_41
      · exact prime_eighteenP_43
      · exact prime_eighteenP_47
      · exact prime_eighteenP_53
      · exact prime_eighteenP_59
      · exact prime_eighteenP_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (79 : ZMod 625905997466200023976603201) ^ 312952998733100011988301600 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (79 : ZMod 625905997466200023976603201) ^ 208635332488733341325534400 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (79 : ZMod 625905997466200023976603201) ^ 125181199493240004795320640 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (79 : ZMod 625905997466200023976603201) ^ 89415142495171431996657600 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (79 : ZMod 625905997466200023976603201) ^ 56900545224200002179691200 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (79 : ZMod 625905997466200023976603201) ^ 48146615189707694152046400 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (79 : ZMod 625905997466200023976603201) ^ 32942420919273685472452800 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (79 : ZMod 625905997466200023976603201) ^ 27213304237660870607678400 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (79 : ZMod 625905997466200023976603201) ^ 21582965429868966344020800 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (79 : ZMod 625905997466200023976603201) ^ 20190516047296774966987200 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (79 : ZMod 625905997466200023976603201) ^ 16916378309897297945313600 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (79 : ZMod 625905997466200023976603201) ^ 15265999938200000584795200 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (79 : ZMod 625905997466200023976603201) ^ 14555953429446512185502400 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (79 : ZMod 625905997466200023976603201) ^ 13317148882259574978225600 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (79 : ZMod 625905997466200023976603201) ^ 11809547122003774037294400 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (79 : ZMod 625905997466200023976603201) ^ 10608576228240678372484800 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (79 : ZMod 625905997466200023976603201) ^ 10260754056822951212731200 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide

private theorem prime_eighteenP_33493 : Nat.Prime 33493 := by norm_num
private theorem prime_eighteenP_50587 : Nat.Prime 50587 := by norm_num
private theorem prime_eighteenP_197 : Nat.Prime 197 := by norm_num
private theorem prime_eighteenP_613 : Nat.Prime 613 := by norm_num
private theorem prime_eighteenP_3301 : Nat.Prime 3301 := by norm_num
private theorem prime_eighteenP_1784738467 : Nat.Prime 1784738467 := by
  apply lucas_primality 1784738467 (3 : ZMod 1784738467)
  · rw [← eighteenPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 2), (7, 2), (613, 1), (3301, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 2), (7, 2), (613, 1), (3301, 1)] : List FactorBlock).map factorBlockValue).prod = 1784738467 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eighteenP_2
      · exact prime_eighteenP_3
      · exact prime_eighteenP_7
      · exact prime_eighteenP_613
      · exact prime_eighteenP_3301
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1784738467) ^ 892369233 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (3 : ZMod 1784738467) ^ 594912822 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (3 : ZMod 1784738467) ^ 254962638 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (3 : ZMod 1784738467) ^ 2911482 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (3 : ZMod 1784738467) ^ 540666 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide

private theorem prime_eighteenP_28555815473 : Nat.Prime 28555815473 := by
  apply lucas_primality 28555815473 (3 : ZMod 28555815473)
  · rw [← eighteenPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 4), (1784738467, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 4), (1784738467, 1)] : List FactorBlock).map factorBlockValue).prod = 28555815473 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_eighteenP_2
      · exact prime_eighteenP_1784738467
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 28555815473) ^ 14277907736 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (3 : ZMod 28555815473) ^ 16 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide

private theorem prime_eighteenP_67505947778173 : Nat.Prime 67505947778173 := by
  apply lucas_primality 67505947778173 (2 : ZMod 67505947778173)
  · rw [← eighteenPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (197, 1), (28555815473, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (197, 1), (28555815473, 1)] : List FactorBlock).map factorBlockValue).prod = 67505947778173 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eighteenP_2
      · exact prime_eighteenP_3
      · exact prime_eighteenP_197
      · exact prime_eighteenP_28555815473
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 67505947778173) ^ 33752973889086 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (2 : ZMod 67505947778173) ^ 22501982592724 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (2 : ZMod 67505947778173) ^ 342669785676 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (2 : ZMod 67505947778173) ^ 2364 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide

private theorem prime_eighteenP_18153732689432590021117 : Nat.Prime 18153732689432590021117 := by
  apply lucas_primality 18153732689432590021117 (2 : ZMod 18153732689432590021117)
  · rw [← eighteenPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (443, 1), (50587, 1), (67505947778173, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (443, 1), (50587, 1), (67505947778173, 1)] : List FactorBlock).map factorBlockValue).prod = 18153732689432590021117 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eighteenP_2
      · exact prime_eighteenP_3
      · exact prime_eighteenP_443
      · exact prime_eighteenP_50587
      · exact prime_eighteenP_67505947778173
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 18153732689432590021117) ^ 9076866344716295010558 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (2 : ZMod 18153732689432590021117) ^ 6051244229810863340372 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (2 : ZMod 18153732689432590021117) ^ 40979080563053250612 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (2 : ZMod 18153732689432590021117) ^ 358861618388767668 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (2 : ZMod 18153732689432590021117) ^ 268920492 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide

private theorem prime_eighteenP_113 : Nat.Prime 113 := by norm_num
private theorem prime_eighteenP_37309 : Nat.Prime 37309 := by norm_num
private theorem prime_eighteenP_1222615931 : Nat.Prime 1222615931 := by
  apply lucas_primality 1222615931 (2 : ZMod 1222615931)
  · rw [← eighteenPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 1), (29, 1), (113, 1), (37309, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 1), (29, 1), (113, 1), (37309, 1)] : List FactorBlock).map factorBlockValue).prod = 1222615931 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eighteenP_2
      · exact prime_eighteenP_5
      · exact prime_eighteenP_29
      · exact prime_eighteenP_113
      · exact prime_eighteenP_37309
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1222615931) ^ 611307965 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (2 : ZMod 1222615931) ^ 244523186 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (2 : ZMod 1222615931) ^ 42159170 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (2 : ZMod 1222615931) ^ 10819610 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (2 : ZMod 1222615931) ^ 32770 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide

private theorem prime_eighteenP_2531 : Nat.Prime 2531 := by norm_num
private theorem prime_eighteenP_6763 : Nat.Prime 6763 := by norm_num
private theorem prime_eighteenP_462094662389 : Nat.Prime 462094662389 := by
  apply lucas_primality 462094662389 (2 : ZMod 462094662389)
  · rw [← eighteenPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (17, 1), (397, 1), (2531, 1), (6763, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (17, 1), (397, 1), (2531, 1), (6763, 1)] : List FactorBlock).map factorBlockValue).prod = 462094662389 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eighteenP_2
      · exact prime_eighteenP_17
      · exact prime_eighteenP_397
      · exact prime_eighteenP_2531
      · exact prime_eighteenP_6763
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 462094662389) ^ 231047331194 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (2 : ZMod 462094662389) ^ 27182038964 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (2 : ZMod 462094662389) ^ 1163966404 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (2 : ZMod 462094662389) ^ 182573948 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (2 : ZMod 462094662389) ^ 68326876 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide

private theorem prime_eighteenP_1667237541899513 : Nat.Prime 1667237541899513 := by
  apply lucas_primality 1667237541899513 (3 : ZMod 1667237541899513)
  · rw [← eighteenPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (11, 1), (41, 1), (462094662389, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (11, 1), (41, 1), (462094662389, 1)] : List FactorBlock).map factorBlockValue).prod = 1667237541899513 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eighteenP_2
      · exact prime_eighteenP_11
      · exact prime_eighteenP_41
      · exact prime_eighteenP_462094662389
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1667237541899513) ^ 833618770949756 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (3 : ZMod 1667237541899513) ^ 151567049263592 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (3 : ZMod 1667237541899513) ^ 40664330290232 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (3 : ZMod 1667237541899513) ^ 3608 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide

private theorem prime_eighteenP_483498887150858771 : Nat.Prime 483498887150858771 := by
  apply lucas_primality 483498887150858771 (2 : ZMod 483498887150858771)
  · rw [← eighteenPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 1), (29, 1), (1667237541899513, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 1), (29, 1), (1667237541899513, 1)] : List FactorBlock).map factorBlockValue).prod = 483498887150858771 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eighteenP_2
      · exact prime_eighteenP_5
      · exact prime_eighteenP_29
      · exact prime_eighteenP_1667237541899513
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 483498887150858771) ^ 241749443575429385 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (2 : ZMod 483498887150858771) ^ 96699777430171754 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (2 : ZMod 483498887150858771) ^ 16672375418995130 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (2 : ZMod 483498887150858771) ^ 290 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide

private theorem prime_eighteenP_28463 : Nat.Prime 28463 := by norm_num
private theorem prime_eighteenP_100103 : Nat.Prime 100103 := by norm_num
private theorem prime_eighteenP_546353 : Nat.Prime 546353 := by norm_num
private theorem prime_eighteenP_5119 : Nat.Prime 5119 := by norm_num
private theorem prime_eighteenP_6449 : Nat.Prime 6449 := by norm_num
private theorem prime_eighteenP_369475127753 : Nat.Prime 369475127753 := by
  apply lucas_primality 369475127753 (3 : ZMod 369475127753)
  · rw [← eighteenPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (1399, 1), (5119, 1), (6449, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (1399, 1), (5119, 1), (6449, 1)] : List FactorBlock).map factorBlockValue).prod = 369475127753 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eighteenP_2
      · exact prime_eighteenP_1399
      · exact prime_eighteenP_5119
      · exact prime_eighteenP_6449
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 369475127753) ^ 184737563876 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (3 : ZMod 369475127753) ^ 264099448 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (3 : ZMod 369475127753) ^ 72177208 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (3 : ZMod 369475127753) ^ 57291848 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide

private theorem prime_eighteenP_3691 : Nat.Prime 3691 := by norm_num
private theorem prime_eighteenP_401987 : Nat.Prime 401987 := by norm_num
private theorem prime_eighteenP_86843 : Nat.Prime 86843 := by norm_num
private theorem prime_eighteenP_171877 : Nat.Prime 171877 := by norm_num
private theorem prime_eighteenP_3074820748067 : Nat.Prime 3074820748067 := by
  apply lucas_primality 3074820748067 (2 : ZMod 3074820748067)
  · rw [← eighteenPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (103, 1), (86843, 1), (171877, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (103, 1), (86843, 1), (171877, 1)] : List FactorBlock).map factorBlockValue).prod = 3074820748067 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eighteenP_2
      · exact prime_eighteenP_103
      · exact prime_eighteenP_86843
      · exact prime_eighteenP_171877
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 3074820748067) ^ 1537410374033 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (2 : ZMod 3074820748067) ^ 29852628622 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (2 : ZMod 3074820748067) ^ 35406662 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (2 : ZMod 3074820748067) ^ 17889658 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide

private theorem prime_eighteenP_43047490472939 : Nat.Prime 43047490472939 := by
  apply lucas_primality 43047490472939 (7 : ZMod 43047490472939)
  · rw [← eighteenPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (7, 1), (3074820748067, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (7, 1), (3074820748067, 1)] : List FactorBlock).map factorBlockValue).prod = 43047490472939 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eighteenP_2
      · exact prime_eighteenP_7
      · exact prime_eighteenP_3074820748067
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 43047490472939) ^ 21523745236469 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (7 : ZMod 43047490472939) ^ 6149641496134 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (7 : ZMod 43047490472939) ^ 14 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide

private theorem prime_eighteenP_377440396466729153 : Nat.Prime 377440396466729153 := by
  apply lucas_primality 377440396466729153 (3 : ZMod 377440396466729153)
  · rw [← eighteenPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 6), (137, 1), (43047490472939, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 6), (137, 1), (43047490472939, 1)] : List FactorBlock).map factorBlockValue).prod = 377440396466729153 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eighteenP_2
      · exact prime_eighteenP_137
      · exact prime_eighteenP_43047490472939
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 377440396466729153) ^ 188720198233364576 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (3 : ZMod 377440396466729153) ^ 2755039390268096 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (3 : ZMod 377440396466729153) ^ 8768 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide

private theorem prime_eighteenP_545661638816687200389859201 : Nat.Prime 545661638816687200389859201 := by
  apply lucas_primality 545661638816687200389859201 (13 : ZMod 545661638816687200389859201)
  · rw [← eighteenPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 7), (3, 4), (5, 2), (7, 2), (11, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 7), (3, 4), (5, 2), (7, 2), (11, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod = 545661638816687200389859201 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eighteenP_2
      · exact prime_eighteenP_3
      · exact prime_eighteenP_5
      · exact prime_eighteenP_7
      · exact prime_eighteenP_11
      · exact prime_eighteenP_17
      · exact prime_eighteenP_19
      · exact prime_eighteenP_23
      · exact prime_eighteenP_29
      · exact prime_eighteenP_31
      · exact prime_eighteenP_37
      · exact prime_eighteenP_41
      · exact prime_eighteenP_43
      · exact prime_eighteenP_47
      · exact prime_eighteenP_53
      · exact prime_eighteenP_59
      · exact prime_eighteenP_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 545661638816687200389859201) ^ 272830819408343600194929600 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (13 : ZMod 545661638816687200389859201) ^ 181887212938895733463286400 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (13 : ZMod 545661638816687200389859201) ^ 109132327763337440077971840 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (13 : ZMod 545661638816687200389859201) ^ 77951662688098171484265600 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (13 : ZMod 545661638816687200389859201) ^ 49605603528789745489987200 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (13 : ZMod 545661638816687200389859201) ^ 32097743459805129434697600 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (13 : ZMod 545661638816687200389859201) ^ 28719033621930905283676800 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (13 : ZMod 545661638816687200389859201) ^ 23724419078986400016950400 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (13 : ZMod 545661638816687200389859201) ^ 18815918579885765530684800 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (13 : ZMod 545661638816687200389859201) ^ 17601988348925393560963200 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (13 : ZMod 545661638816687200389859201) ^ 14747611859910464875401600 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (13 : ZMod 545661638816687200389859201) ^ 13308820458943590253411200 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (13 : ZMod 545661638816687200389859201) ^ 12689805553876446520694400 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (13 : ZMod 545661638816687200389859201) ^ 11609822102482706391273600 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (13 : ZMod 545661638816687200389859201) ^ 10295502619182777365846400 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (13 : ZMod 545661638816687200389859201) ^ 9248502352825206786268800 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (13 : ZMod 545661638816687200389859201) ^ 8945272767486675416227200 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide

private theorem prime_eighteenP_11953 : Nat.Prime 11953 := by norm_num
private theorem prime_eighteenP_339907 : Nat.Prime 339907 := by norm_num
private theorem prime_eighteenP_26921 : Nat.Prime 26921 := by norm_num
private theorem prime_eighteenP_96293 : Nat.Prime 96293 := by norm_num
private theorem prime_eighteenP_115327 : Nat.Prime 115327 := by norm_num
private theorem prime_eighteenP_1793775758729587 : Nat.Prime 1793775758729587 := by
  apply lucas_primality 1793775758729587 (2 : ZMod 1793775758729587)
  · rw [← eighteenPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (26921, 1), (96293, 1), (115327, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (26921, 1), (96293, 1), (115327, 1)] : List FactorBlock).map factorBlockValue).prod = 1793775758729587 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eighteenP_2
      · exact prime_eighteenP_3
      · exact prime_eighteenP_26921
      · exact prime_eighteenP_96293
      · exact prime_eighteenP_115327
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1793775758729587) ^ 896887879364793 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (2 : ZMod 1793775758729587) ^ 597925252909862 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (2 : ZMod 1793775758729587) ^ 66631096866 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (2 : ZMod 1793775758729587) ^ 18628309002 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (2 : ZMod 1793775758729587) ^ 15553823118 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide

private theorem prime_eighteenP_37223 : Nat.Prime 37223 := by norm_num
private theorem prime_eighteenP_312401611 : Nat.Prime 312401611 := by
  apply lucas_primality 312401611 (10 : ZMod 312401611)
  · rw [← eighteenPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 4), (5, 1), (19, 1), (53, 1), (383, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 4), (5, 1), (19, 1), (53, 1), (383, 1)] : List FactorBlock).map factorBlockValue).prod = 312401611 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eighteenP_2
      · exact prime_eighteenP_3
      · exact prime_eighteenP_5
      · exact prime_eighteenP_19
      · exact prime_eighteenP_53
      · exact prime_eighteenP_383
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 312401611) ^ 156200805 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (10 : ZMod 312401611) ^ 104133870 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (10 : ZMod 312401611) ^ 62480322 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (10 : ZMod 312401611) ^ 16442190 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (10 : ZMod 312401611) ^ 5894370 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (10 : ZMod 312401611) ^ 815670 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide

private theorem prime_eighteenP_3623 : Nat.Prime 3623 := by norm_num
private theorem prime_eighteenP_34313 : Nat.Prime 34313 := by norm_num
private theorem prime_eighteenP_603181227149 : Nat.Prime 603181227149 := by
  apply lucas_primality 603181227149 (2 : ZMod 603181227149)
  · rw [← eighteenPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (1213, 1), (3623, 1), (34313, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (1213, 1), (3623, 1), (34313, 1)] : List FactorBlock).map factorBlockValue).prod = 603181227149 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eighteenP_2
      · exact prime_eighteenP_1213
      · exact prime_eighteenP_3623
      · exact prime_eighteenP_34313
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 603181227149) ^ 301590613574 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (2 : ZMod 603181227149) ^ 497263996 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (2 : ZMod 603181227149) ^ 166486676 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (2 : ZMod 603181227149) ^ 17578796 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide

private theorem prime_eighteenP_13944174244386535740887 : Nat.Prime 13944174244386535740887 := by
  apply lucas_primality 13944174244386535740887 (5 : ZMod 13944174244386535740887)
  · rw [← eighteenPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (37, 1), (312401611, 1), (603181227149, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (37, 1), (312401611, 1), (603181227149, 1)] : List FactorBlock).map factorBlockValue).prod = 13944174244386535740887 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eighteenP_2
      · exact prime_eighteenP_37
      · exact prime_eighteenP_312401611
      · exact prime_eighteenP_603181227149
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 13944174244386535740887) ^ 6972087122193267870443 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (5 : ZMod 13944174244386535740887) ^ 376869574172609074078 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (5 : ZMod 13944174244386535740887) ^ 44635410809026 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (5 : ZMod 13944174244386535740887) ^ 23117719214 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide

private theorem prime_eighteenP_727 : Nat.Prime 727 := by norm_num
private theorem prime_eighteenP_517267 : Nat.Prime 517267 := by norm_num
private theorem prime_eighteenP_40346827 : Nat.Prime 40346827 := by
  apply lucas_primality 40346827 (2 : ZMod 40346827)
  · rw [← eighteenPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (13, 1), (517267, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (13, 1), (517267, 1)] : List FactorBlock).map factorBlockValue).prod = 40346827 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eighteenP_2
      · exact prime_eighteenP_3
      · exact prime_eighteenP_13
      · exact prime_eighteenP_517267
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 40346827) ^ 20173413 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (2 : ZMod 40346827) ^ 13448942 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (2 : ZMod 40346827) ^ 3103602 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (2 : ZMod 40346827) ^ 78 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide

private theorem prime_eighteenP_4159 : Nat.Prime 4159 := by norm_num
private theorem prime_eighteenP_16453 : Nat.Prime 16453 := by norm_num
private theorem prime_eighteenP_910838081 : Nat.Prime 910838081 := by
  apply lucas_primality 910838081 (3 : ZMod 910838081)
  · rw [← eighteenPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 6), (5, 1), (173, 1), (16453, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 6), (5, 1), (173, 1), (16453, 1)] : List FactorBlock).map factorBlockValue).prod = 910838081 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eighteenP_2
      · exact prime_eighteenP_5
      · exact prime_eighteenP_173
      · exact prime_eighteenP_16453
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 910838081) ^ 455419040 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (3 : ZMod 910838081) ^ 182167616 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (3 : ZMod 910838081) ^ 5264960 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (3 : ZMod 910838081) ^ 55360 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide

private theorem prime_eighteenP_75763511577581 : Nat.Prime 75763511577581 := by
  apply lucas_primality 75763511577581 (3 : ZMod 75763511577581)
  · rw [← eighteenPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (5, 1), (4159, 1), (910838081, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (5, 1), (4159, 1), (910838081, 1)] : List FactorBlock).map factorBlockValue).prod = 75763511577581 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eighteenP_2
      · exact prime_eighteenP_5
      · exact prime_eighteenP_4159
      · exact prime_eighteenP_910838081
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 75763511577581) ^ 37881755788790 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (3 : ZMod 75763511577581) ^ 15152702315516 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (3 : ZMod 75763511577581) ^ 18216761620 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (3 : ZMod 75763511577581) ^ 83180 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide

private theorem prime_eighteenP_17274080639688469 : Nat.Prime 17274080639688469 := by
  apply lucas_primality 17274080639688469 (2 : ZMod 17274080639688469)
  · rw [← eighteenPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (19, 1), (75763511577581, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (19, 1), (75763511577581, 1)] : List FactorBlock).map factorBlockValue).prod = 17274080639688469 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eighteenP_2
      · exact prime_eighteenP_3
      · exact prime_eighteenP_19
      · exact prime_eighteenP_75763511577581
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 17274080639688469) ^ 8637040319844234 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (2 : ZMod 17274080639688469) ^ 5758026879896156 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (2 : ZMod 17274080639688469) ^ 909162138930972 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (2 : ZMod 17274080639688469) ^ 228 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide

private theorem prime_eighteenP_257 : Nat.Prime 257 := by norm_num
private theorem prime_eighteenP_2801 : Nat.Prime 2801 := by norm_num
private theorem prime_eighteenP_7829 : Nat.Prime 7829 := by norm_num
private theorem prime_eighteenP_353 : Nat.Prime 353 := by norm_num
private theorem prime_eighteenP_1319 : Nat.Prime 1319 := by norm_num
private theorem prime_eighteenP_169369 : Nat.Prime 169369 := by norm_num
private theorem prime_eighteenP_164287931 : Nat.Prime 164287931 := by
  apply lucas_primality 164287931 (2 : ZMod 164287931)
  · rw [← eighteenPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 1), (97, 1), (169369, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 1), (97, 1), (169369, 1)] : List FactorBlock).map factorBlockValue).prod = 164287931 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eighteenP_2
      · exact prime_eighteenP_5
      · exact prime_eighteenP_97
      · exact prime_eighteenP_169369
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 164287931) ^ 82143965 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (2 : ZMod 164287931) ^ 32857586 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (2 : ZMod 164287931) ^ 1693690 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (2 : ZMod 164287931) ^ 970 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide

private theorem prime_eighteenP_87814665071106317 : Nat.Prime 87814665071106317 := by
  apply lucas_primality 87814665071106317 (2 : ZMod 87814665071106317)
  · rw [← eighteenPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (7, 1), (41, 1), (353, 1), (1319, 1), (164287931, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (7, 1), (41, 1), (353, 1), (1319, 1), (164287931, 1)] : List FactorBlock).map factorBlockValue).prod = 87814665071106317 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eighteenP_2
      · exact prime_eighteenP_7
      · exact prime_eighteenP_41
      · exact prime_eighteenP_353
      · exact prime_eighteenP_1319
      · exact prime_eighteenP_164287931
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 87814665071106317) ^ 43907332535553158 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (2 : ZMod 87814665071106317) ^ 12544952153015188 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (2 : ZMod 87814665071106317) ^ 2141821099295276 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (2 : ZMod 87814665071106317) ^ 248766756575372 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (2 : ZMod 87814665071106317) ^ 66576698310164 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (2 : ZMod 87814665071106317) ^ 534516836 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide

private theorem prime_eighteenP_1277 : Nat.Prime 1277 := by norm_num
private theorem prime_eighteenP_23539 : Nat.Prime 23539 := by norm_num
private theorem prime_eighteenP_8521 : Nat.Prime 8521 := by norm_num
private theorem prime_eighteenP_1192327 : Nat.Prime 1192327 := by norm_num
private theorem prime_eighteenP_101598183671 : Nat.Prime 101598183671 := by
  apply lucas_primality 101598183671 (17 : ZMod 101598183671)
  · rw [← eighteenPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 1), (8521, 1), (1192327, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 1), (8521, 1), (1192327, 1)] : List FactorBlock).map factorBlockValue).prod = 101598183671 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eighteenP_2
      · exact prime_eighteenP_5
      · exact prime_eighteenP_8521
      · exact prime_eighteenP_1192327
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (17 : ZMod 101598183671) ^ 50799091835 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (17 : ZMod 101598183671) ^ 20319636734 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (17 : ZMod 101598183671) ^ 11923270 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (17 : ZMod 101598183671) ^ 85210 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide

private theorem prime_eighteenP_203196367343 : Nat.Prime 203196367343 := by
  apply lucas_primality 203196367343 (5 : ZMod 203196367343)
  · rw [← eighteenPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (101598183671, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (101598183671, 1)] : List FactorBlock).map factorBlockValue).prod = 203196367343 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_eighteenP_2
      · exact prime_eighteenP_101598183671
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 203196367343) ^ 101598183671 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (5 : ZMod 203196367343) ^ 2 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide

private theorem prime_eighteenP_1211050349364281 : Nat.Prime 1211050349364281 := by
  apply lucas_primality 1211050349364281 (3 : ZMod 1211050349364281)
  · rw [← eighteenPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (5, 1), (149, 1), (203196367343, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (5, 1), (149, 1), (203196367343, 1)] : List FactorBlock).map factorBlockValue).prod = 1211050349364281 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eighteenP_2
      · exact prime_eighteenP_5
      · exact prime_eighteenP_149
      · exact prime_eighteenP_203196367343
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1211050349364281) ^ 605525174682140 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (3 : ZMod 1211050349364281) ^ 242210069872856 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (3 : ZMod 1211050349364281) ^ 8127854693720 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (3 : ZMod 1211050349364281) ^ 5960 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide

private theorem prime_eighteenP_16090014941653837367 : Nat.Prime 16090014941653837367 := by
  apply lucas_primality 16090014941653837367 (5 : ZMod 16090014941653837367)
  · rw [← eighteenPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (7, 1), (13, 1), (73, 1), (1211050349364281, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (7, 1), (13, 1), (73, 1), (1211050349364281, 1)] : List FactorBlock).map factorBlockValue).prod = 16090014941653837367 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eighteenP_2
      · exact prime_eighteenP_7
      · exact prime_eighteenP_13
      · exact prime_eighteenP_73
      · exact prime_eighteenP_1211050349364281
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 16090014941653837367) ^ 8045007470826918683 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (5 : ZMod 16090014941653837367) ^ 2298573563093405338 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (5 : ZMod 16090014941653837367) ^ 1237693457050295182 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (5 : ZMod 16090014941653837367) ^ 220411163584299142 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (5 : ZMod 16090014941653837367) ^ 13286 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide

private theorem prime_eighteenP_4327 : Nat.Prime 4327 := by norm_num
private theorem prime_eighteenP_1214459 : Nat.Prime 1214459 := by norm_num
private theorem prime_eighteenP_983 : Nat.Prime 983 := by norm_num
private theorem prime_eighteenP_6079 : Nat.Prime 6079 := by norm_num
private theorem prime_eighteenP_35853943 : Nat.Prime 35853943 := by
  apply lucas_primality 35853943 (3 : ZMod 35853943)
  · rw [← eighteenPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (983, 1), (6079, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (983, 1), (6079, 1)] : List FactorBlock).map factorBlockValue).prod = 35853943 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eighteenP_2
      · exact prime_eighteenP_3
      · exact prime_eighteenP_983
      · exact prime_eighteenP_6079
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 35853943) ^ 17926971 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (3 : ZMod 35853943) ^ 11951314 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (3 : ZMod 35853943) ^ 36474 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (3 : ZMod 35853943) ^ 5898 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide

private theorem prime_eighteenP_376537177183483 : Nat.Prime 376537177183483 := by
  apply lucas_primality 376537177183483 (2 : ZMod 376537177183483)
  · rw [← eighteenPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 7), (7, 4), (35853943, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 7), (7, 4), (35853943, 1)] : List FactorBlock).map factorBlockValue).prod = 376537177183483 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eighteenP_2
      · exact prime_eighteenP_3
      · exact prime_eighteenP_7
      · exact prime_eighteenP_35853943
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 376537177183483) ^ 188268588591741 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (2 : ZMod 376537177183483) ^ 125512392394494 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (2 : ZMod 376537177183483) ^ 53791025311926 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (2 : ZMod 376537177183483) ^ 10501974 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide

private theorem prime_eighteenP_12941 : Nat.Prime 12941 := by norm_num
private theorem prime_eighteenP_83 : Nat.Prime 83 := by norm_num
private theorem prime_eighteenP_17389 : Nat.Prime 17389 := by norm_num
private theorem prime_eighteenP_25214051 : Nat.Prime 25214051 := by
  apply lucas_primality 25214051 (6 : ZMod 25214051)
  · rw [← eighteenPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 2), (29, 1), (17389, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 2), (29, 1), (17389, 1)] : List FactorBlock).map factorBlockValue).prod = 25214051 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eighteenP_2
      · exact prime_eighteenP_5
      · exact prime_eighteenP_29
      · exact prime_eighteenP_17389
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 25214051) ^ 12607025 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (6 : ZMod 25214051) ^ 5042810 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (6 : ZMod 25214051) ^ 869450 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (6 : ZMod 25214051) ^ 1450 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide

private theorem prime_eighteenP_2773545611 : Nat.Prime 2773545611 := by
  apply lucas_primality 2773545611 (2 : ZMod 2773545611)
  · rw [← eighteenPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 1), (11, 1), (25214051, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 1), (11, 1), (25214051, 1)] : List FactorBlock).map factorBlockValue).prod = 2773545611 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eighteenP_2
      · exact prime_eighteenP_5
      · exact prime_eighteenP_11
      · exact prime_eighteenP_25214051
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 2773545611) ^ 1386772805 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (2 : ZMod 2773545611) ^ 554709122 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (2 : ZMod 2773545611) ^ 252140510 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (2 : ZMod 2773545611) ^ 110 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide

private theorem prime_eighteenP_11970622857077 : Nat.Prime 11970622857077 := by
  apply lucas_primality 11970622857077 (2 : ZMod 11970622857077)
  · rw [← eighteenPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (13, 1), (83, 1), (2773545611, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (13, 1), (83, 1), (2773545611, 1)] : List FactorBlock).map factorBlockValue).prod = 11970622857077 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eighteenP_2
      · exact prime_eighteenP_13
      · exact prime_eighteenP_83
      · exact prime_eighteenP_2773545611
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 11970622857077) ^ 5985311428538 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (2 : ZMod 11970622857077) ^ 920817142852 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (2 : ZMod 11970622857077) ^ 144224371772 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (2 : ZMod 11970622857077) ^ 4316 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide

private theorem prime_eighteenP_55113911370054181597633 : Nat.Prime 55113911370054181597633 := by
  apply lucas_primality 55113911370054181597633 (5 : ZMod 55113911370054181597633)
  · rw [← eighteenPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 6), (3, 1), (17, 1), (109, 1), (12941, 1), (11970622857077, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 6), (3, 1), (17, 1), (109, 1), (12941, 1), (11970622857077, 1)] : List FactorBlock).map factorBlockValue).prod = 55113911370054181597633 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eighteenP_2
      · exact prime_eighteenP_3
      · exact prime_eighteenP_17
      · exact prime_eighteenP_109
      · exact prime_eighteenP_12941
      · exact prime_eighteenP_11970622857077
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 55113911370054181597633) ^ 27556955685027090798816 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (5 : ZMod 55113911370054181597633) ^ 18371303790018060532544 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (5 : ZMod 55113911370054181597633) ^ 3241994786473775388096 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (5 : ZMod 55113911370054181597633) ^ 505632214404166803648 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (5 : ZMod 55113911370054181597633) ^ 4258860317599426752 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (5 : ZMod 55113911370054181597633) ^ 4604097216 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide

private theorem prime_eighteenP_330683468220325089585799 : Nat.Prime 330683468220325089585799 := by
  apply lucas_primality 330683468220325089585799 (6 : ZMod 330683468220325089585799)
  · rw [← eighteenPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (55113911370054181597633, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (55113911370054181597633, 1)] : List FactorBlock).map factorBlockValue).prod = 330683468220325089585799 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eighteenP_2
      · exact prime_eighteenP_3
      · exact prime_eighteenP_55113911370054181597633
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (6 : ZMod 330683468220325089585799) ^ 165341734110162544792899 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (6 : ZMod 330683468220325089585799) ^ 110227822740108363195266 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (6 : ZMod 330683468220325089585799) ^ 6 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide

private theorem prime_eighteenP_4691 : Nat.Prime 4691 := by norm_num
private theorem prime_eighteenP_4885104199 : Nat.Prime 4885104199 := by
  apply lucas_primality 4885104199 (3 : ZMod 4885104199)
  · rw [← eighteenPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (13, 3), (79, 1), (4691, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (13, 3), (79, 1), (4691, 1)] : List FactorBlock).map factorBlockValue).prod = 4885104199 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eighteenP_2
      · exact prime_eighteenP_3
      · exact prime_eighteenP_13
      · exact prime_eighteenP_79
      · exact prime_eighteenP_4691
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 4885104199) ^ 2442552099 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (3 : ZMod 4885104199) ^ 1628368066 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (3 : ZMod 4885104199) ^ 375777246 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (3 : ZMod 4885104199) ^ 61836762 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (3 : ZMod 4885104199) ^ 1041378 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide

private theorem prime_eighteenP_117242500777 : Nat.Prime 117242500777 := by
  apply lucas_primality 117242500777 (5 : ZMod 117242500777)
  · rw [← eighteenPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (3, 1), (4885104199, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (3, 1), (4885104199, 1)] : List FactorBlock).map factorBlockValue).prod = 117242500777 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eighteenP_2
      · exact prime_eighteenP_3
      · exact prime_eighteenP_4885104199
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 117242500777) ^ 58621250388 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (5 : ZMod 117242500777) ^ 39080833592 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (5 : ZMod 117242500777) ^ 24 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide

private theorem prime_eighteenP_7517 : Nat.Prime 7517 := by norm_num
private theorem prime_eighteenP_76303 : Nat.Prime 76303 := by norm_num
private theorem prime_eighteenP_1147139303 : Nat.Prime 1147139303 := by
  apply lucas_primality 1147139303 (5 : ZMod 1147139303)
  · rw [← eighteenPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (7517, 1), (76303, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (7517, 1), (76303, 1)] : List FactorBlock).map factorBlockValue).prod = 1147139303 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eighteenP_2
      · exact prime_eighteenP_7517
      · exact prime_eighteenP_76303
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 1147139303) ^ 573569651 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (5 : ZMod 1147139303) ^ 152606 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (5 : ZMod 1147139303) ^ 15034 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide

private theorem prime_eighteenP_22323330836381 : Nat.Prime 22323330836381 := by
  apply lucas_primality 22323330836381 (2 : ZMod 22323330836381)
  · rw [← eighteenPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (5, 1), (7, 1), (139, 1), (1147139303, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (5, 1), (7, 1), (139, 1), (1147139303, 1)] : List FactorBlock).map factorBlockValue).prod = 22323330836381 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eighteenP_2
      · exact prime_eighteenP_5
      · exact prime_eighteenP_7
      · exact prime_eighteenP_139
      · exact prime_eighteenP_1147139303
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 22323330836381) ^ 11161665418190 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (2 : ZMod 22323330836381) ^ 4464666167276 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (2 : ZMod 22323330836381) ^ 3189047262340 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (2 : ZMod 22323330836381) ^ 160599502420 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (2 : ZMod 22323330836381) ^ 19460 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide

private theorem prime_eighteenP_373 : Nat.Prime 373 := by norm_num
private theorem prime_eighteenP_55249 : Nat.Prime 55249 := by norm_num
private theorem prime_eighteenP_157429 : Nat.Prime 157429 := by norm_num
private theorem prime_eighteenP_773027 : Nat.Prime 773027 := by norm_num
private theorem prime_eighteenP_17678041 : Nat.Prime 17678041 := by norm_num
private theorem prime_eighteenP_176780411 : Nat.Prime 176780411 := by
  apply lucas_primality 176780411 (2 : ZMod 176780411)
  · rw [← eighteenPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 1), (17678041, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 1), (17678041, 1)] : List FactorBlock).map factorBlockValue).prod = 176780411 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eighteenP_2
      · exact prime_eighteenP_5
      · exact prime_eighteenP_17678041
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 176780411) ^ 88390205 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (2 : ZMod 176780411) ^ 35356082 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (2 : ZMod 176780411) ^ 10 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide

private theorem prime_eighteenP_434302120690832669698051201 : Nat.Prime 434302120690832669698051201 := by
  apply lucas_primality 434302120690832669698051201 (14 : ZMod 434302120690832669698051201)
  · rw [← eighteenPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 7), (3, 5), (5, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 7), (3, 5), (5, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod = 434302120690832669698051201 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eighteenP_2
      · exact prime_eighteenP_3
      · exact prime_eighteenP_5
      · exact prime_eighteenP_11
      · exact prime_eighteenP_13
      · exact prime_eighteenP_17
      · exact prime_eighteenP_19
      · exact prime_eighteenP_23
      · exact prime_eighteenP_29
      · exact prime_eighteenP_31
      · exact prime_eighteenP_37
      · exact prime_eighteenP_41
      · exact prime_eighteenP_43
      · exact prime_eighteenP_47
      · exact prime_eighteenP_53
      · exact prime_eighteenP_59
      · exact prime_eighteenP_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (14 : ZMod 434302120690832669698051201) ^ 217151060345416334849025600 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (14 : ZMod 434302120690832669698051201) ^ 144767373563610889899350400 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (14 : ZMod 434302120690832669698051201) ^ 86860424138166533939610240 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (14 : ZMod 434302120690832669698051201) ^ 39482010971893879063459200 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (14 : ZMod 434302120690832669698051201) ^ 33407855437756359207542400 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (14 : ZMod 434302120690832669698051201) ^ 25547183570048980570473600 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (14 : ZMod 434302120690832669698051201) ^ 22858006352149087878844800 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (14 : ZMod 434302120690832669698051201) ^ 18882700899601420421654400 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (14 : ZMod 434302120690832669698051201) ^ 14975935196235609299932800 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (14 : ZMod 434302120690832669698051201) ^ 14009745828736537732195200 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (14 : ZMod 434302120690832669698051201) ^ 11737895153806288370217600 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (14 : ZMod 434302120690832669698051201) ^ 10592734650995918773123200 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (14 : ZMod 434302120690832669698051201) ^ 10100049318391457434838400 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (14 : ZMod 434302120690832669698051201) ^ 9240470652996439780809600 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (14 : ZMod 434302120690832669698051201) ^ 8194379635676088107510400 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (14 : ZMod 434302120690832669698051201) ^ 7361052893064960503356800 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (14 : ZMod 434302120690832669698051201) ^ 7119706896571027372099200 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide

private theorem prime_eighteenP_12759209 : Nat.Prime 12759209 := by norm_num
private theorem prime_eighteenP_79181 : Nat.Prime 79181 := by norm_num
private theorem prime_eighteenP_181957939 : Nat.Prime 181957939 := by
  apply lucas_primality 181957939 (2 : ZMod 181957939)
  · rw [← eighteenPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (383, 1), (79181, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (383, 1), (79181, 1)] : List FactorBlock).map factorBlockValue).prod = 181957939 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eighteenP_2
      · exact prime_eighteenP_3
      · exact prime_eighteenP_383
      · exact prime_eighteenP_79181
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 181957939) ^ 90978969 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (2 : ZMod 181957939) ^ 60652646 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (2 : ZMod 181957939) ^ 475086 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (2 : ZMod 181957939) ^ 2298 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide

private theorem prime_eighteenP_1831 : Nat.Prime 1831 := by norm_num
private theorem prime_eighteenP_5479 : Nat.Prime 5479 := by norm_num
private theorem prime_eighteenP_9137 : Nat.Prime 9137 := by norm_num
private theorem prime_eighteenP_183325663427 : Nat.Prime 183325663427 := by
  apply lucas_primality 183325663427 (2 : ZMod 183325663427)
  · rw [← eighteenPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (1831, 1), (5479, 1), (9137, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (1831, 1), (5479, 1), (9137, 1)] : List FactorBlock).map factorBlockValue).prod = 183325663427 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eighteenP_2
      · exact prime_eighteenP_1831
      · exact prime_eighteenP_5479
      · exact prime_eighteenP_9137
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 183325663427) ^ 91662831713 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (2 : ZMod 183325663427) ^ 100123246 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (2 : ZMod 183325663427) ^ 33459694 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (2 : ZMod 183325663427) ^ 20064098 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide

private theorem prime_eighteenP_1567 : Nat.Prime 1567 := by norm_num
private theorem prime_eighteenP_4969 : Nat.Prime 4969 := by norm_num
private theorem prime_eighteenP_10103311 : Nat.Prime 10103311 := by norm_num
private theorem prime_eighteenP_32429 : Nat.Prime 32429 := by norm_num
private theorem prime_eighteenP_38287 : Nat.Prime 38287 := by norm_num
private theorem prime_eighteenP_7449654739 : Nat.Prime 7449654739 := by
  apply lucas_primality 7449654739 (2 : ZMod 7449654739)
  · rw [← eighteenPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (32429, 1), (38287, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (32429, 1), (38287, 1)] : List FactorBlock).map factorBlockValue).prod = 7449654739 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eighteenP_2
      · exact prime_eighteenP_3
      · exact prime_eighteenP_32429
      · exact prime_eighteenP_38287
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 7449654739) ^ 3724827369 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (2 : ZMod 7449654739) ^ 2483218246 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (2 : ZMod 7449654739) ^ 229722 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (2 : ZMod 7449654739) ^ 194574 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide

private theorem prime_eighteenP_29798618957 : Nat.Prime 29798618957 := by
  apply lucas_primality 29798618957 (2 : ZMod 29798618957)
  · rw [← eighteenPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (7449654739, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (7449654739, 1)] : List FactorBlock).map factorBlockValue).prod = 29798618957 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_eighteenP_2
      · exact prime_eighteenP_7449654739
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 29798618957) ^ 14899309478 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (2 : ZMod 29798618957) ^ 4 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide

private theorem prime_eighteenP_2991981134619696139127 : Nat.Prime 2991981134619696139127 := by
  apply lucas_primality 2991981134619696139127 (5 : ZMod 2991981134619696139127)
  · rw [← eighteenPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (4969, 1), (10103311, 1), (29798618957, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (4969, 1), (10103311, 1), (29798618957, 1)] : List FactorBlock).map factorBlockValue).prod = 2991981134619696139127 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eighteenP_2
      · exact prime_eighteenP_4969
      · exact prime_eighteenP_10103311
      · exact prime_eighteenP_29798618957
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 2991981134619696139127) ^ 1495990567309848069563 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (5 : ZMod 2991981134619696139127) ^ 602129429386133254 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (5 : ZMod 2991981134619696139127) ^ 296138675194666 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (5 : ZMod 2991981134619696139127) ^ 100406704718 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide

private theorem prime_eighteenP_571 : Nat.Prime 571 := by norm_num
private theorem prime_eighteenP_11213231 : Nat.Prime 11213231 := by norm_num
private theorem prime_eighteenP_12829519 : Nat.Prime 12829519 := by norm_num
private theorem prime_eighteenP_433 : Nat.Prime 433 := by norm_num
private theorem prime_eighteenP_6043 : Nat.Prime 6043 := by norm_num
private theorem prime_eighteenP_2491021289 : Nat.Prime 2491021289 := by
  apply lucas_primality 2491021289 (3 : ZMod 2491021289)
  · rw [← eighteenPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (7, 1), (17, 1), (433, 1), (6043, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (7, 1), (17, 1), (433, 1), (6043, 1)] : List FactorBlock).map factorBlockValue).prod = 2491021289 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eighteenP_2
      · exact prime_eighteenP_7
      · exact prime_eighteenP_17
      · exact prime_eighteenP_433
      · exact prime_eighteenP_6043
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 2491021289) ^ 1245510644 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (3 : ZMod 2491021289) ^ 355860184 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (3 : ZMod 2491021289) ^ 146530664 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (3 : ZMod 2491021289) ^ 5752936 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (3 : ZMod 2491021289) ^ 412216 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide

private theorem prime_eighteenP_4982042579 : Nat.Prime 4982042579 := by
  apply lucas_primality 4982042579 (2 : ZMod 4982042579)
  · rw [← eighteenPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (2491021289, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (2491021289, 1)] : List FactorBlock).map factorBlockValue).prod = 4982042579 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_eighteenP_2
      · exact prime_eighteenP_2491021289
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 4982042579) ^ 2491021289 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (2 : ZMod 4982042579) ^ 2 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide

private theorem prime_eighteenP_241 : Nat.Prime 241 := by norm_num
private theorem prime_eighteenP_263 : Nat.Prime 263 := by norm_num
private theorem prime_eighteenP_5369209 : Nat.Prime 5369209 := by norm_num
private theorem prime_eighteenP_21476837 : Nat.Prime 21476837 := by
  apply lucas_primality 21476837 (2 : ZMod 21476837)
  · rw [← eighteenPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (5369209, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (5369209, 1)] : List FactorBlock).map factorBlockValue).prod = 21476837 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_eighteenP_2
      · exact prime_eighteenP_5369209
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 21476837) ^ 10738418 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (2 : ZMod 21476837) ^ 4 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide

private theorem prime_eighteenP_816119807 : Nat.Prime 816119807 := by
  apply lucas_primality 816119807 (5 : ZMod 816119807)
  · rw [← eighteenPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (19, 1), (21476837, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (19, 1), (21476837, 1)] : List FactorBlock).map factorBlockValue).prod = 816119807 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eighteenP_2
      · exact prime_eighteenP_19
      · exact prime_eighteenP_21476837
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 816119807) ^ 408059903 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (5 : ZMod 816119807) ^ 42953674 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (5 : ZMod 816119807) ^ 38 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide

private theorem prime_eighteenP_5851 : Nat.Prime 5851 := by norm_num
private theorem prime_eighteenP_11055391 : Nat.Prime 11055391 := by norm_num
private theorem prime_eighteenP_7762211128921 : Nat.Prime 7762211128921 := by
  apply lucas_primality 7762211128921 (17 : ZMod 7762211128921)
  · rw [← eighteenPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (3, 1), (5, 1), (5851, 1), (11055391, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (3, 1), (5, 1), (5851, 1), (11055391, 1)] : List FactorBlock).map factorBlockValue).prod = 7762211128921 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eighteenP_2
      · exact prime_eighteenP_3
      · exact prime_eighteenP_5
      · exact prime_eighteenP_5851
      · exact prime_eighteenP_11055391
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (17 : ZMod 7762211128921) ^ 3881105564460 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (17 : ZMod 7762211128921) ^ 2587403709640 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (17 : ZMod 7762211128921) ^ 1552442225784 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (17 : ZMod 7762211128921) ^ 1326646920 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (17 : ZMod 7762211128921) ^ 702120 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide

private theorem prime_eighteenP_394088961367607422503787201 : Nat.Prime 394088961367607422503787201 := by
  apply lucas_primality 394088961367607422503787201 (103 : ZMod 394088961367607422503787201)
  · rw [← eighteenPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 6), (3, 2), (5, 2), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 6), (3, 2), (5, 2), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod = 394088961367607422503787201 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eighteenP_2
      · exact prime_eighteenP_3
      · exact prime_eighteenP_5
      · exact prime_eighteenP_7
      · exact prime_eighteenP_11
      · exact prime_eighteenP_13
      · exact prime_eighteenP_17
      · exact prime_eighteenP_19
      · exact prime_eighteenP_23
      · exact prime_eighteenP_29
      · exact prime_eighteenP_31
      · exact prime_eighteenP_37
      · exact prime_eighteenP_41
      · exact prime_eighteenP_43
      · exact prime_eighteenP_47
      · exact prime_eighteenP_53
      · exact prime_eighteenP_59
      · exact prime_eighteenP_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (103 : ZMod 394088961367607422503787201) ^ 197044480683803711251893600 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 131362987122535807501262400 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 78817792273521484500757440 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 56298423052515346071969600 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 35826269215237038409435200 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 30314535489815955577214400 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 23181703609859260147281600 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 20741524282505653815988800 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 17134302668156844456686400 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 13589274529917497327716800 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 12712547140890562016251200 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 10651053009935335743345600 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 9611925887014815183019200 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 9164859566688544709390400 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 8384871518459732393697600 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 7435640780520894764222400 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 6679473921484871567860800 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 6460474776518154467275200 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide

private theorem prime_eighteenP_523 : Nat.Prime 523 := by norm_num
private theorem prime_eighteenP_59743 : Nat.Prime 59743 := by norm_num
private theorem prime_eighteenP_79147 : Nat.Prime 79147 := by norm_num
private theorem prime_eighteenP_3604807 : Nat.Prime 3604807 := by norm_num
private theorem prime_eighteenP_1141238638517 : Nat.Prime 1141238638517 := by
  apply lucas_primality 1141238638517 (2 : ZMod 1141238638517)
  · rw [← eighteenPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (79147, 1), (3604807, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (79147, 1), (3604807, 1)] : List FactorBlock).map factorBlockValue).prod = 1141238638517 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eighteenP_2
      · exact prime_eighteenP_79147
      · exact prime_eighteenP_3604807
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 1141238638517) ^ 570619319258 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (2 : ZMod 1141238638517) ^ 14419228 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (2 : ZMod 1141238638517) ^ 316588 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide

private theorem prime_eighteenP_194010568547891 : Nat.Prime 194010568547891 := by
  apply lucas_primality 194010568547891 (2 : ZMod 194010568547891)
  · rw [← eighteenPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 1), (17, 1), (1141238638517, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 1), (17, 1), (1141238638517, 1)] : List FactorBlock).map factorBlockValue).prod = 194010568547891 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eighteenP_2
      · exact prime_eighteenP_5
      · exact prime_eighteenP_17
      · exact prime_eighteenP_1141238638517
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 194010568547891) ^ 97005284273945 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (2 : ZMod 194010568547891) ^ 38802113709578 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (2 : ZMod 194010568547891) ^ 11412386385170 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (2 : ZMod 194010568547891) ^ 170 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide

private theorem prime_eighteenP_12383306569274786749 : Nat.Prime 12383306569274786749 := by
  apply lucas_primality 12383306569274786749 (2 : ZMod 12383306569274786749)
  · rw [← eighteenPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 4), (197, 1), (194010568547891, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 4), (197, 1), (194010568547891, 1)] : List FactorBlock).map factorBlockValue).prod = 12383306569274786749 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eighteenP_2
      · exact prime_eighteenP_3
      · exact prime_eighteenP_197
      · exact prime_eighteenP_194010568547891
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 12383306569274786749) ^ 6191653284637393374 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (2 : ZMod 12383306569274786749) ^ 4127768856424928916 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (2 : ZMod 12383306569274786749) ^ 62859424209516684 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (2 : ZMod 12383306569274786749) ^ 63828 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide

private theorem prime_eighteenP_20719 : Nat.Prime 20719 := by norm_num
private theorem prime_eighteenP_12986333 : Nat.Prime 12986333 := by norm_num
private theorem prime_eighteenP_10589 : Nat.Prime 10589 := by norm_num
private theorem prime_eighteenP_98880083 : Nat.Prime 98880083 := by
  apply lucas_primality 98880083 (6 : ZMod 98880083)
  · rw [← eighteenPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (7, 1), (23, 1), (29, 1), (10589, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (7, 1), (23, 1), (29, 1), (10589, 1)] : List FactorBlock).map factorBlockValue).prod = 98880083 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eighteenP_2
      · exact prime_eighteenP_7
      · exact prime_eighteenP_23
      · exact prime_eighteenP_29
      · exact prime_eighteenP_10589
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 98880083) ^ 49440041 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (6 : ZMod 98880083) ^ 14125726 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (6 : ZMod 98880083) ^ 4299134 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (6 : ZMod 98880083) ^ 3409658 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (6 : ZMod 98880083) ^ 9338 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide

private theorem prime_eighteenP_1018963687663171715671 : Nat.Prime 1018963687663171715671 := by
  apply lucas_primality 1018963687663171715671 (3 : ZMod 1018963687663171715671)
  · rw [← eighteenPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 3), (5, 1), (2939, 1), (12986333, 1), (98880083, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 3), (5, 1), (2939, 1), (12986333, 1), (98880083, 1)] : List FactorBlock).map factorBlockValue).prod = 1018963687663171715671 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eighteenP_2
      · exact prime_eighteenP_3
      · exact prime_eighteenP_5
      · exact prime_eighteenP_2939
      · exact prime_eighteenP_12986333
      · exact prime_eighteenP_98880083
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1018963687663171715671) ^ 509481843831585857835 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (3 : ZMod 1018963687663171715671) ^ 339654562554390571890 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (3 : ZMod 1018963687663171715671) ^ 203792737532634343134 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (3 : ZMod 1018963687663171715671) ^ 346704214924522530 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (3 : ZMod 1018963687663171715671) ^ 78464312262990 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (3 : ZMod 1018963687663171715671) ^ 10305044825490 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide

private theorem prime_eighteenP_18341346377937090882079 : Nat.Prime 18341346377937090882079 := by
  apply lucas_primality 18341346377937090882079 (3 : ZMod 18341346377937090882079)
  · rw [← eighteenPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 2), (1018963687663171715671, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 2), (1018963687663171715671, 1)] : List FactorBlock).map factorBlockValue).prod = 18341346377937090882079 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eighteenP_2
      · exact prime_eighteenP_3
      · exact prime_eighteenP_1018963687663171715671
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 18341346377937090882079) ^ 9170673188968545441039 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (3 : ZMod 18341346377937090882079) ^ 6113782125979030294026 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (3 : ZMod 18341346377937090882079) ^ 18 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide

private theorem prime_eighteenP_2712337 : Nat.Prime 2712337 := by norm_num
private theorem prime_eighteenP_2442113 : Nat.Prime 2442113 := by norm_num
private theorem prime_eighteenP_21683 : Nat.Prime 21683 := by norm_num
private theorem prime_eighteenP_106750482823 : Nat.Prime 106750482823 := by
  apply lucas_primality 106750482823 (3 : ZMod 106750482823)
  · rw [← eighteenPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 3), (17, 1), (31, 1), (173, 1), (21683, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 3), (17, 1), (31, 1), (173, 1), (21683, 1)] : List FactorBlock).map factorBlockValue).prod = 106750482823 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eighteenP_2
      · exact prime_eighteenP_3
      · exact prime_eighteenP_17
      · exact prime_eighteenP_31
      · exact prime_eighteenP_173
      · exact prime_eighteenP_21683
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 106750482823) ^ 53375241411 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (3 : ZMod 106750482823) ^ 35583494274 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (3 : ZMod 106750482823) ^ 6279440166 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (3 : ZMod 106750482823) ^ 3443563962 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (3 : ZMod 106750482823) ^ 617054814 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (3 : ZMod 106750482823) ^ 4923234 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide

private theorem prime_eighteenP_137647879701195599473 : Nat.Prime 137647879701195599473 := by
  apply lucas_primality 137647879701195599473 (5 : ZMod 137647879701195599473)
  · rw [← eighteenPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 4), (3, 1), (11, 1), (2442113, 1), (106750482823, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 4), (3, 1), (11, 1), (2442113, 1), (106750482823, 1)] : List FactorBlock).map factorBlockValue).prod = 137647879701195599473 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eighteenP_2
      · exact prime_eighteenP_3
      · exact prime_eighteenP_11
      · exact prime_eighteenP_2442113
      · exact prime_eighteenP_106750482823
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 137647879701195599473) ^ 68823939850597799736 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (5 : ZMod 137647879701195599473) ^ 45882626567065199824 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (5 : ZMod 137647879701195599473) ^ 12513443609199599952 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (5 : ZMod 137647879701195599473) ^ 56364254930544 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (5 : ZMod 137647879701195599473) ^ 1289435664 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide

private theorem prime_eighteenP_2284423 : Nat.Prime 2284423 := by norm_num
private theorem prime_eighteenP_704321 : Nat.Prime 704321 := by norm_num
private theorem prime_eighteenP_63388891 : Nat.Prime 63388891 := by
  apply lucas_primality 63388891 (2 : ZMod 63388891)
  · rw [← eighteenPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 2), (5, 1), (704321, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 2), (5, 1), (704321, 1)] : List FactorBlock).map factorBlockValue).prod = 63388891 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eighteenP_2
      · exact prime_eighteenP_3
      · exact prime_eighteenP_5
      · exact prime_eighteenP_704321
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 63388891) ^ 31694445 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (2 : ZMod 63388891) ^ 21129630 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (2 : ZMod 63388891) ^ 12677778 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (2 : ZMod 63388891) ^ 90 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide

private theorem prime_eighteenP_1652843 : Nat.Prime 1652843 := by norm_num
private theorem prime_eighteenP_961954627 : Nat.Prime 961954627 := by
  apply lucas_primality 961954627 (2 : ZMod 961954627)
  · rw [← eighteenPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (97, 1), (1652843, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (97, 1), (1652843, 1)] : List FactorBlock).map factorBlockValue).prod = 961954627 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eighteenP_2
      · exact prime_eighteenP_3
      · exact prime_eighteenP_97
      · exact prime_eighteenP_1652843
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 961954627) ^ 480977313 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (2 : ZMod 961954627) ^ 320651542 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (2 : ZMod 961954627) ^ 9917058 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (2 : ZMod 961954627) ^ 582 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide

private theorem prime_eighteenP_5771727763 : Nat.Prime 5771727763 := by
  apply lucas_primality 5771727763 (3 : ZMod 5771727763)
  · rw [← eighteenPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (961954627, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (961954627, 1)] : List FactorBlock).map factorBlockValue).prod = 5771727763 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eighteenP_2
      · exact prime_eighteenP_3
      · exact prime_eighteenP_961954627
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 5771727763) ^ 2885863881 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (3 : ZMod 5771727763) ^ 1923909254 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (3 : ZMod 5771727763) ^ 6 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide

private theorem prime_eighteenP_2601761 : Nat.Prime 2601761 := by norm_num
private theorem prime_eighteenP_20814089 : Nat.Prime 20814089 := by
  apply lucas_primality 20814089 (3 : ZMod 20814089)
  · rw [← eighteenPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (2601761, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (2601761, 1)] : List FactorBlock).map factorBlockValue).prod = 20814089 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_eighteenP_2
      · exact prime_eighteenP_2601761
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 20814089) ^ 10407044 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (3 : ZMod 20814089) ^ 8 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide

private theorem prime_eighteenP_295851461047 : Nat.Prime 295851461047 := by
  apply lucas_primality 295851461047 (3 : ZMod 295851461047)
  · rw [← eighteenPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (23, 1), (103, 1), (20814089, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (23, 1), (103, 1), (20814089, 1)] : List FactorBlock).map factorBlockValue).prod = 295851461047 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eighteenP_2
      · exact prime_eighteenP_3
      · exact prime_eighteenP_23
      · exact prime_eighteenP_103
      · exact prime_eighteenP_20814089
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 295851461047) ^ 147925730523 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (3 : ZMod 295851461047) ^ 98617153682 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (3 : ZMod 295851461047) ^ 12863107002 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (3 : ZMod 295851461047) ^ 2872344282 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (3 : ZMod 295851461047) ^ 14214 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide

private theorem prime_eighteenP_8807 : Nat.Prime 8807 := by norm_num
private theorem prime_eighteenP_1756787 : Nat.Prime 1756787 := by norm_num
private theorem prime_eighteenP_1219164476942983 : Nat.Prime 1219164476942983 := by
  apply lucas_primality 1219164476942983 (3 : ZMod 1219164476942983)
  · rw [← eighteenPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (23, 1), (571, 1), (8807, 1), (1756787, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (23, 1), (571, 1), (8807, 1), (1756787, 1)] : List FactorBlock).map factorBlockValue).prod = 1219164476942983 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eighteenP_2
      · exact prime_eighteenP_3
      · exact prime_eighteenP_23
      · exact prime_eighteenP_571
      · exact prime_eighteenP_8807
      · exact prime_eighteenP_1756787
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1219164476942983) ^ 609582238471491 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (3 : ZMod 1219164476942983) ^ 406388158980994 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (3 : ZMod 1219164476942983) ^ 53007151171434 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (3 : ZMod 1219164476942983) ^ 2135139189042 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (3 : ZMod 1219164476942983) ^ 138431302026 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (3 : ZMod 1219164476942983) ^ 693973986 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide

private theorem prime_eighteenP_180533 : Nat.Prime 180533 := by norm_num
private theorem prime_eighteenP_2161 : Nat.Prime 2161 := by norm_num
private theorem prime_eighteenP_8537 : Nat.Prime 8537 := by norm_num
private theorem prime_eighteenP_561521 : Nat.Prime 561521 := by norm_num
private theorem prime_eighteenP_19518469961 : Nat.Prime 19518469961 := by
  apply lucas_primality 19518469961 (3 : ZMod 19518469961)
  · rw [← eighteenPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (5, 1), (11, 1), (79, 1), (561521, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (5, 1), (11, 1), (79, 1), (561521, 1)] : List FactorBlock).map factorBlockValue).prod = 19518469961 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eighteenP_2
      · exact prime_eighteenP_5
      · exact prime_eighteenP_11
      · exact prime_eighteenP_79
      · exact prime_eighteenP_561521
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 19518469961) ^ 9759234980 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (3 : ZMod 19518469961) ^ 3903693992 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (3 : ZMod 19518469961) ^ 1774406360 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (3 : ZMod 19518469961) ^ 247069240 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (3 : ZMod 19518469961) ^ 34760 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide

private theorem prime_eighteenP_44650621068881221949 : Nat.Prime 44650621068881221949 := by
  apply lucas_primality 44650621068881221949 (2 : ZMod 44650621068881221949)
  · rw [← eighteenPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (31, 1), (2161, 1), (8537, 1), (19518469961, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (31, 1), (2161, 1), (8537, 1), (19518469961, 1)] : List FactorBlock).map factorBlockValue).prod = 44650621068881221949 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eighteenP_2
      · exact prime_eighteenP_31
      · exact prime_eighteenP_2161
      · exact prime_eighteenP_8537
      · exact prime_eighteenP_19518469961
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 44650621068881221949) ^ 22325310534440610974 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (2 : ZMod 44650621068881221949) ^ 1440342615125200708 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (2 : ZMod 44650621068881221949) ^ 20662018079075068 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (2 : ZMod 44650621068881221949) ^ 5230247284629404 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (2 : ZMod 44650621068881221949) ^ 2287608668 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide

private theorem prime_eighteenP_1964627327030773765757 : Nat.Prime 1964627327030773765757 := by
  apply lucas_primality 1964627327030773765757 (3 : ZMod 1964627327030773765757)
  · rw [← eighteenPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (11, 1), (44650621068881221949, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (11, 1), (44650621068881221949, 1)] : List FactorBlock).map factorBlockValue).prod = 1964627327030773765757 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eighteenP_2
      · exact prime_eighteenP_11
      · exact prime_eighteenP_44650621068881221949
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 1964627327030773765757) ^ 982313663515386882878 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (3 : ZMod 1964627327030773765757) ^ 178602484275524887796 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (3 : ZMod 1964627327030773765757) ^ 44 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide

private theorem prime_eighteenP_8821091 : Nat.Prime 8821091 := by norm_num
private theorem prime_eighteenP_3140308397 : Nat.Prime 3140308397 := by
  apply lucas_primality 3140308397 (2 : ZMod 3140308397)
  · rw [← eighteenPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (89, 1), (8821091, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (89, 1), (8821091, 1)] : List FactorBlock).map factorBlockValue).prod = 3140308397 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eighteenP_2
      · exact prime_eighteenP_89
      · exact prime_eighteenP_8821091
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 3140308397) ^ 1570154198 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (2 : ZMod 3140308397) ^ 35284364 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (2 : ZMod 3140308397) ^ 356 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide

private theorem prime_eighteenP_39362201 : Nat.Prime 39362201 := by
  apply lucas_primality 39362201 (6 : ZMod 39362201)
  · rw [← eighteenPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (5, 2), (23, 1), (43, 1), (199, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (5, 2), (23, 1), (43, 1), (199, 1)] : List FactorBlock).map factorBlockValue).prod = 39362201 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eighteenP_2
      · exact prime_eighteenP_5
      · exact prime_eighteenP_23
      · exact prime_eighteenP_43
      · exact prime_eighteenP_199
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 39362201) ^ 19681100 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (6 : ZMod 39362201) ^ 7872440 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (6 : ZMod 39362201) ^ 1711400 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (6 : ZMod 39362201) ^ 915400 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (6 : ZMod 39362201) ^ 197800 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide

private theorem prime_eighteenP_911 : Nat.Prime 911 := by norm_num
private theorem prime_eighteenP_48407 : Nat.Prime 48407 := by norm_num
private theorem prime_eighteenP_705580433 : Nat.Prime 705580433 := by
  apply lucas_primality 705580433 (3 : ZMod 705580433)
  · rw [← eighteenPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 4), (911, 1), (48407, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 4), (911, 1), (48407, 1)] : List FactorBlock).map factorBlockValue).prod = 705580433 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eighteenP_2
      · exact prime_eighteenP_911
      · exact prime_eighteenP_48407
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 705580433) ^ 352790216 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (3 : ZMod 705580433) ^ 774512 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (3 : ZMod 705580433) ^ 14576 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide

private theorem prime_eighteenP_111092795301652133 : Nat.Prime 111092795301652133 := by
  apply lucas_primality 111092795301652133 (2 : ZMod 111092795301652133)
  · rw [← eighteenPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (39362201, 1), (705580433, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (39362201, 1), (705580433, 1)] : List FactorBlock).map factorBlockValue).prod = 111092795301652133 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eighteenP_2
      · exact prime_eighteenP_39362201
      · exact prime_eighteenP_705580433
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 111092795301652133) ^ 55546397650826066 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (2 : ZMod 111092795301652133) ^ 2822321732 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (2 : ZMod 111092795301652133) ^ 157448804 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide

private theorem prime_eighteenP_563 : Nat.Prime 563 := by norm_num
private theorem prime_eighteenP_210739 : Nat.Prime 210739 := by norm_num
private theorem prime_eighteenP_599 : Nat.Prime 599 := by norm_num
private theorem prime_eighteenP_616277 : Nat.Prime 616277 := by norm_num
private theorem prime_eighteenP_2296112521061 : Nat.Prime 2296112521061 := by
  apply lucas_primality 2296112521061 (2 : ZMod 2296112521061)
  · rw [← eighteenPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (5, 1), (311, 1), (599, 1), (616277, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (5, 1), (311, 1), (599, 1), (616277, 1)] : List FactorBlock).map factorBlockValue).prod = 2296112521061 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eighteenP_2
      · exact prime_eighteenP_5
      · exact prime_eighteenP_311
      · exact prime_eighteenP_599
      · exact prime_eighteenP_616277
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 2296112521061) ^ 1148056260530 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (2 : ZMod 2296112521061) ^ 459222504212 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (2 : ZMod 2296112521061) ^ 7382998460 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (2 : ZMod 2296112521061) ^ 3833242940 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (2 : ZMod 2296112521061) ^ 3725780 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide

private theorem prime_eighteenP_4592225042123 : Nat.Prime 4592225042123 := by
  apply lucas_primality 4592225042123 (2 : ZMod 4592225042123)
  · rw [← eighteenPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (2296112521061, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (2296112521061, 1)] : List FactorBlock).map factorBlockValue).prod = 4592225042123 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_eighteenP_2
      · exact prime_eighteenP_2296112521061
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 4592225042123) ^ 2296112521061 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (2 : ZMod 4592225042123) ^ 2 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide

private theorem prime_eighteenP_34854988069713571 : Nat.Prime 34854988069713571 := by
  apply lucas_primality 34854988069713571 (2 : ZMod 34854988069713571)
  · rw [← eighteenPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (5, 1), (11, 1), (23, 1), (4592225042123, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (5, 1), (11, 1), (23, 1), (4592225042123, 1)] : List FactorBlock).map factorBlockValue).prod = 34854988069713571 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eighteenP_2
      · exact prime_eighteenP_3
      · exact prime_eighteenP_5
      · exact prime_eighteenP_11
      · exact prime_eighteenP_23
      · exact prime_eighteenP_4592225042123
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 34854988069713571) ^ 17427494034856785 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (2 : ZMod 34854988069713571) ^ 11618329356571190 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (2 : ZMod 34854988069713571) ^ 6970997613942714 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (2 : ZMod 34854988069713571) ^ 3168635279064870 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (2 : ZMod 34854988069713571) ^ 1515434263900590 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (2 : ZMod 34854988069713571) ^ 7590 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide

private theorem prime_eighteenP_97523 : Nat.Prime 97523 := by norm_num
private theorem prime_eighteenP_467 : Nat.Prime 467 := by norm_num
private theorem prime_eighteenP_1123 : Nat.Prime 1123 := by norm_num
private theorem prime_eighteenP_5826967 : Nat.Prime 5826967 := by norm_num
private theorem prime_eighteenP_138448735921 : Nat.Prime 138448735921 := by
  apply lucas_primality 138448735921 (14 : ZMod 138448735921)
  · rw [← eighteenPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 4), (3, 3), (5, 1), (11, 1), (5826967, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 4), (3, 3), (5, 1), (11, 1), (5826967, 1)] : List FactorBlock).map factorBlockValue).prod = 138448735921 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eighteenP_2
      · exact prime_eighteenP_3
      · exact prime_eighteenP_5
      · exact prime_eighteenP_11
      · exact prime_eighteenP_5826967
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (14 : ZMod 138448735921) ^ 69224367960 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (14 : ZMod 138448735921) ^ 46149578640 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (14 : ZMod 138448735921) ^ 27689747184 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (14 : ZMod 138448735921) ^ 12586248720 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (14 : ZMod 138448735921) ^ 23760 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide

private theorem prime_eighteenP_621911721757133 : Nat.Prime 621911721757133 := by
  apply lucas_primality 621911721757133 (2 : ZMod 621911721757133)
  · rw [← eighteenPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (1123, 1), (138448735921, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (1123, 1), (138448735921, 1)] : List FactorBlock).map factorBlockValue).prod = 621911721757133 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eighteenP_2
      · exact prime_eighteenP_1123
      · exact prime_eighteenP_138448735921
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 621911721757133) ^ 310955860878566 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (2 : ZMod 621911721757133) ^ 553794943684 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (2 : ZMod 621911721757133) ^ 4492 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide

private theorem prime_eighteenP_3463701263446490329787 : Nat.Prime 3463701263446490329787 := by
  apply lucas_primality 3463701263446490329787 (2 : ZMod 3463701263446490329787)
  · rw [← eighteenPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (67, 1), (89, 1), (467, 1), (621911721757133, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (67, 1), (89, 1), (467, 1), (621911721757133, 1)] : List FactorBlock).map factorBlockValue).prod = 3463701263446490329787 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eighteenP_2
      · exact prime_eighteenP_67
      · exact prime_eighteenP_89
      · exact prime_eighteenP_467
      · exact prime_eighteenP_621911721757133
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 3463701263446490329787) ^ 1731850631723245164893 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (2 : ZMod 3463701263446490329787) ^ 51697033782783437758 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (2 : ZMod 3463701263446490329787) ^ 38917991724117868874 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (2 : ZMod 3463701263446490329787) ^ 7416919193675568158 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (2 : ZMod 3463701263446490329787) ^ 5569442 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide

private theorem prime_eighteenP_541 : Nat.Prime 541 := by norm_num
private theorem prime_eighteenP_36017 : Nat.Prime 36017 := by norm_num
private theorem prime_eighteenP_157 : Nat.Prime 157 := by norm_num
private theorem prime_eighteenP_6456001 : Nat.Prime 6456001 := by norm_num
private theorem prime_eighteenP_4054368629 : Nat.Prime 4054368629 := by
  apply lucas_primality 4054368629 (2 : ZMod 4054368629)
  · rw [← eighteenPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (157, 1), (6456001, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (157, 1), (6456001, 1)] : List FactorBlock).map factorBlockValue).prod = 4054368629 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eighteenP_2
      · exact prime_eighteenP_157
      · exact prime_eighteenP_6456001
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 4054368629) ^ 2027184314 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (2 : ZMod 4054368629) ^ 25824004 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (2 : ZMod 4054368629) ^ 628 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide

private theorem prime_eighteenP_16189 : Nat.Prime 16189 := by norm_num
private theorem prime_eighteenP_30500077 : Nat.Prime 30500077 := by
  apply lucas_primality 30500077 (5 : ZMod 30500077)
  · rw [← eighteenPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (157, 1), (16189, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (157, 1), (16189, 1)] : List FactorBlock).map factorBlockValue).prod = 30500077 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eighteenP_2
      · exact prime_eighteenP_3
      · exact prime_eighteenP_157
      · exact prime_eighteenP_16189
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 30500077) ^ 15250038 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (5 : ZMod 30500077) ^ 10166692 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (5 : ZMod 30500077) ^ 194268 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (5 : ZMod 30500077) ^ 1884 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide

private theorem prime_eighteenP_4209010627 : Nat.Prime 4209010627 := by
  apply lucas_primality 4209010627 (2 : ZMod 4209010627)
  · rw [← eighteenPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (23, 1), (30500077, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (23, 1), (30500077, 1)] : List FactorBlock).map factorBlockValue).prod = 4209010627 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eighteenP_2
      · exact prime_eighteenP_3
      · exact prime_eighteenP_23
      · exact prime_eighteenP_30500077
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 4209010627) ^ 2104505313 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (2 : ZMod 4209010627) ^ 1403003542 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (2 : ZMod 4209010627) ^ 183000462 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (2 : ZMod 4209010627) ^ 138 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide

private theorem prime_eighteenP_26111 : Nat.Prime 26111 := by norm_num
private theorem prime_eighteenP_41513 : Nat.Prime 41513 := by norm_num
private theorem prime_eighteenP_5874587657 : Nat.Prime 5874587657 := by
  apply lucas_primality 5874587657 (3 : ZMod 5874587657)
  · rw [← eighteenPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (7, 2), (19, 2), (41513, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (7, 2), (19, 2), (41513, 1)] : List FactorBlock).map factorBlockValue).prod = 5874587657 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eighteenP_2
      · exact prime_eighteenP_7
      · exact prime_eighteenP_19
      · exact prime_eighteenP_41513
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 5874587657) ^ 2937293828 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (3 : ZMod 5874587657) ^ 839226808 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (3 : ZMod 5874587657) ^ 309188824 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (3 : ZMod 5874587657) ^ 141512 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide

private theorem prime_eighteenP_863 : Nat.Prime 863 := by norm_num
private theorem prime_eighteenP_2927 : Nat.Prime 2927 := by norm_num
private theorem prime_eighteenP_9790779877 : Nat.Prime 9790779877 := by
  apply lucas_primality 9790779877 (2 : ZMod 9790779877)
  · rw [← eighteenPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (17, 1), (19, 1), (863, 1), (2927, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (17, 1), (19, 1), (863, 1), (2927, 1)] : List FactorBlock).map factorBlockValue).prod = 9790779877 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eighteenP_2
      · exact prime_eighteenP_3
      · exact prime_eighteenP_17
      · exact prime_eighteenP_19
      · exact prime_eighteenP_863
      · exact prime_eighteenP_2927
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 9790779877) ^ 4895389938 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (2 : ZMod 9790779877) ^ 3263593292 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (2 : ZMod 9790779877) ^ 575928228 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (2 : ZMod 9790779877) ^ 515304204 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (2 : ZMod 9790779877) ^ 11345052 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (2 : ZMod 9790779877) ^ 3344988 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide

private theorem prime_eighteenP_115033589235656356379 : Nat.Prime 115033589235656356379 := by
  apply lucas_primality 115033589235656356379 (2 : ZMod 115033589235656356379)
  · rw [← eighteenPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5874587657, 1), (9790779877, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5874587657, 1), (9790779877, 1)] : List FactorBlock).map factorBlockValue).prod = 115033589235656356379 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eighteenP_2
      · exact prime_eighteenP_5874587657
      · exact prime_eighteenP_9790779877
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 115033589235656356379) ^ 57516794617828178189 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (2 : ZMod 115033589235656356379) ^ 19581559754 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (2 : ZMod 115033589235656356379) ^ 11749175314 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide

private theorem prime_eighteenP_4637 : Nat.Prime 4637 := by norm_num
private theorem prime_eighteenP_13311821 : Nat.Prime 13311821 := by norm_num
private theorem prime_eighteenP_2076644077 : Nat.Prime 2076644077 := by
  apply lucas_primality 2076644077 (2 : ZMod 2076644077)
  · rw [← eighteenPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (13, 1), (13311821, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (13, 1), (13311821, 1)] : List FactorBlock).map factorBlockValue).prod = 2076644077 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eighteenP_2
      · exact prime_eighteenP_3
      · exact prime_eighteenP_13
      · exact prime_eighteenP_13311821
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 2076644077) ^ 1038322038 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (2 : ZMod 2076644077) ^ 692214692 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (2 : ZMod 2076644077) ^ 159741852 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (2 : ZMod 2076644077) ^ 156 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide

private theorem prime_eighteenP_809 : Nat.Prime 809 := by norm_num
private theorem prime_eighteenP_1873 : Nat.Prime 1873 := by norm_num
private theorem prime_eighteenP_14851 : Nat.Prime 14851 := by norm_num
private theorem prime_eighteenP_166895539 : Nat.Prime 166895539 := by
  apply lucas_primality 166895539 (2 : ZMod 166895539)
  · rw [← eighteenPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (1873, 1), (14851, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (1873, 1), (14851, 1)] : List FactorBlock).map factorBlockValue).prod = 166895539 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eighteenP_2
      · exact prime_eighteenP_3
      · exact prime_eighteenP_1873
      · exact prime_eighteenP_14851
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 166895539) ^ 83447769 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (2 : ZMod 166895539) ^ 55631846 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (2 : ZMod 166895539) ^ 89106 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (2 : ZMod 166895539) ^ 11238 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide

private theorem prime_eighteenP_33484585780649 : Nat.Prime 33484585780649 := by
  apply lucas_primality 33484585780649 (3 : ZMod 33484585780649)
  · rw [← eighteenPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (31, 1), (809, 1), (166895539, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (31, 1), (809, 1), (166895539, 1)] : List FactorBlock).map factorBlockValue).prod = 33484585780649 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eighteenP_2
      · exact prime_eighteenP_31
      · exact prime_eighteenP_809
      · exact prime_eighteenP_166895539
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 33484585780649) ^ 16742292890324 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (3 : ZMod 33484585780649) ^ 1080147928408 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (3 : ZMod 33484585780649) ^ 41390093672 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (3 : ZMod 33484585780649) ^ 200632 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide

private theorem prime_eighteenP_2806277 : Nat.Prime 2806277 := by norm_num
private theorem prime_eighteenP_252564931 : Nat.Prime 252564931 := by
  apply lucas_primality 252564931 (13 : ZMod 252564931)
  · rw [← eighteenPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 2), (5, 1), (2806277, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 2), (5, 1), (2806277, 1)] : List FactorBlock).map factorBlockValue).prod = 252564931 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eighteenP_2
      · exact prime_eighteenP_3
      · exact prime_eighteenP_5
      · exact prime_eighteenP_2806277
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (13 : ZMod 252564931) ^ 126282465 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (13 : ZMod 252564931) ^ 84188310 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (13 : ZMod 252564931) ^ 50512986 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (13 : ZMod 252564931) ^ 90 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide

private theorem prime_eighteenP_115169608536001 : Nat.Prime 115169608536001 := by
  apply lucas_primality 115169608536001 (7 : ZMod 115169608536001)
  · rw [← eighteenPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 6), (3, 1), (5, 3), (19, 1), (252564931, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 6), (3, 1), (5, 3), (19, 1), (252564931, 1)] : List FactorBlock).map factorBlockValue).prod = 115169608536001 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eighteenP_2
      · exact prime_eighteenP_3
      · exact prime_eighteenP_5
      · exact prime_eighteenP_19
      · exact prime_eighteenP_252564931
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 115169608536001) ^ 57584804268000 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (7 : ZMod 115169608536001) ^ 38389869512000 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (7 : ZMod 115169608536001) ^ 23033921707200 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (7 : ZMod 115169608536001) ^ 6061558344000 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (7 : ZMod 115169608536001) ^ 456000 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide

private theorem prime_eighteenP_2417 : Nat.Prime 2417 := by norm_num
private theorem prime_eighteenP_9433 : Nat.Prime 9433 := by norm_num
private theorem prime_eighteenP_3602330639 : Nat.Prime 3602330639 := by
  apply lucas_primality 3602330639 (13 : ZMod 3602330639)
  · rw [← eighteenPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (79, 1), (2417, 1), (9433, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (79, 1), (2417, 1), (9433, 1)] : List FactorBlock).map factorBlockValue).prod = 3602330639 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eighteenP_2
      · exact prime_eighteenP_79
      · exact prime_eighteenP_2417
      · exact prime_eighteenP_9433
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (13 : ZMod 3602330639) ^ 1801165319 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (13 : ZMod 3602330639) ^ 45599122 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (13 : ZMod 3602330639) ^ 1490414 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (13 : ZMod 3602330639) ^ 381886 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide

private theorem prime_eighteenP_184777947796867 : Nat.Prime 184777947796867 := by
  apply lucas_primality 184777947796867 (2 : ZMod 184777947796867)
  · rw [← eighteenPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (83, 1), (103, 1), (3602330639, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (83, 1), (103, 1), (3602330639, 1)] : List FactorBlock).map factorBlockValue).prod = 184777947796867 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eighteenP_2
      · exact prime_eighteenP_3
      · exact prime_eighteenP_83
      · exact prime_eighteenP_103
      · exact prime_eighteenP_3602330639
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 184777947796867) ^ 92388973898433 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (2 : ZMod 184777947796867) ^ 61592649265622 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (2 : ZMod 184777947796867) ^ 2226240334902 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (2 : ZMod 184777947796867) ^ 1793960658222 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (2 : ZMod 184777947796867) ^ 51294 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide

private theorem prime_eighteenP_15401 : Nat.Prime 15401 := by norm_num
private theorem prime_eighteenP_34847 : Nat.Prime 34847 := by norm_num
private theorem prime_eighteenP_569 : Nat.Prime 569 := by norm_num
private theorem prime_eighteenP_2399 : Nat.Prime 2399 := by norm_num
private theorem prime_eighteenP_2066201 : Nat.Prime 2066201 := by norm_num
private theorem prime_eighteenP_8213087550976673 : Nat.Prime 8213087550976673 := by
  apply lucas_primality 8213087550976673 (3 : ZMod 8213087550976673)
  · rw [← eighteenPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 5), (7, 1), (13, 1), (569, 1), (2399, 1), (2066201, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 5), (7, 1), (13, 1), (569, 1), (2399, 1), (2066201, 1)] : List FactorBlock).map factorBlockValue).prod = 8213087550976673 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eighteenP_2
      · exact prime_eighteenP_7
      · exact prime_eighteenP_13
      · exact prime_eighteenP_569
      · exact prime_eighteenP_2399
      · exact prime_eighteenP_2066201
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 8213087550976673) ^ 4106543775488336 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (3 : ZMod 8213087550976673) ^ 1173298221568096 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (3 : ZMod 8213087550976673) ^ 631775965459744 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (3 : ZMod 8213087550976673) ^ 14434248771488 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (3 : ZMod 8213087550976673) ^ 3423546290528 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (3 : ZMod 8213087550976673) ^ 3974970272 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide

private theorem prime_eighteenP_953 : Nat.Prime 953 := by norm_num
private theorem prime_eighteenP_34157 : Nat.Prime 34157 := by norm_num
private theorem prime_eighteenP_387017 : Nat.Prime 387017 := by norm_num
private theorem prime_eighteenP_485319319 : Nat.Prime 485319319 := by
  apply lucas_primality 485319319 (6 : ZMod 485319319)
  · rw [← eighteenPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (11, 1), (19, 1), (387017, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (11, 1), (19, 1), (387017, 1)] : List FactorBlock).map factorBlockValue).prod = 485319319 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eighteenP_2
      · exact prime_eighteenP_3
      · exact prime_eighteenP_11
      · exact prime_eighteenP_19
      · exact prime_eighteenP_387017
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 485319319) ^ 242659659 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (6 : ZMod 485319319) ^ 161773106 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (6 : ZMod 485319319) ^ 44119938 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (6 : ZMod 485319319) ^ 25543122 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (6 : ZMod 485319319) ^ 1254 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide

private theorem prime_eighteenP_367 : Nat.Prime 367 := by norm_num
private theorem prime_eighteenP_578209 : Nat.Prime 578209 := by norm_num
private theorem prime_eighteenP_848810813 : Nat.Prime 848810813 := by
  apply lucas_primality 848810813 (2 : ZMod 848810813)
  · rw [← eighteenPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (367, 1), (578209, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (367, 1), (578209, 1)] : List FactorBlock).map factorBlockValue).prod = 848810813 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eighteenP_2
      · exact prime_eighteenP_367
      · exact prime_eighteenP_578209
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 848810813) ^ 424405406 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (2 : ZMod 848810813) ^ 2312836 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (2 : ZMod 848810813) ^ 1468 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide

private theorem prime_eighteenP_925079 : Nat.Prime 925079 := by norm_num
private theorem prime_eighteenP_35153003 : Nat.Prime 35153003 := by
  apply lucas_primality 35153003 (2 : ZMod 35153003)
  · rw [← eighteenPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (19, 1), (925079, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (19, 1), (925079, 1)] : List FactorBlock).map factorBlockValue).prod = 35153003 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eighteenP_2
      · exact prime_eighteenP_19
      · exact prime_eighteenP_925079
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 35153003) ^ 17576501 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (2 : ZMod 35153003) ^ 1850158 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (2 : ZMod 35153003) ^ 38 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide

private theorem prime_eighteenP_668867 : Nat.Prime 668867 := by norm_num
private theorem prime_eighteenP_84277243 : Nat.Prime 84277243 := by
  apply lucas_primality 84277243 (2 : ZMod 84277243)
  · rw [← eighteenPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 2), (7, 1), (668867, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 2), (7, 1), (668867, 1)] : List FactorBlock).map factorBlockValue).prod = 84277243 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eighteenP_2
      · exact prime_eighteenP_3
      · exact prime_eighteenP_7
      · exact prime_eighteenP_668867
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 84277243) ^ 42138621 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (2 : ZMod 84277243) ^ 28092414 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (2 : ZMod 84277243) ^ 12039606 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (2 : ZMod 84277243) ^ 126 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide

private theorem prime_eighteenP_307235059 : Nat.Prime 307235059 := by
  apply lucas_primality 307235059 (3 : ZMod 307235059)
  · rw [← eighteenPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (13, 1), (23, 1), (41, 1), (4177, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (13, 1), (23, 1), (41, 1), (4177, 1)] : List FactorBlock).map factorBlockValue).prod = 307235059 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eighteenP_2
      · exact prime_eighteenP_3
      · exact prime_eighteenP_13
      · exact prime_eighteenP_23
      · exact prime_eighteenP_41
      · exact prime_eighteenP_4177
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 307235059) ^ 153617529 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (3 : ZMod 307235059) ^ 102411686 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (3 : ZMod 307235059) ^ 23633466 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (3 : ZMod 307235059) ^ 13358046 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (3 : ZMod 307235059) ^ 7493538 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (3 : ZMod 307235059) ^ 73554 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide

private theorem prime_eighteenP_1820428050799897417896023 : Nat.Prime 1820428050799897417896023 := by
  apply lucas_primality 1820428050799897417896023 (5 : ZMod 1820428050799897417896023)
  · rw [← eighteenPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (35153003, 1), (84277243, 1), (307235059, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (35153003, 1), (84277243, 1), (307235059, 1)] : List FactorBlock).map factorBlockValue).prod = 1820428050799897417896023 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eighteenP_2
      · exact prime_eighteenP_35153003
      · exact prime_eighteenP_84277243
      · exact prime_eighteenP_307235059
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 1820428050799897417896023) ^ 910214025399948708948011 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (5 : ZMod 1820428050799897417896023) ^ 51785847450924674 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (5 : ZMod 1820428050799897417896023) ^ 21600469901464354 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (5 : ZMod 1820428050799897417896023) ^ 5925196352021458 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide

private theorem prime_eighteenP_11894983 : Nat.Prime 11894983 := by norm_num
private theorem prime_eighteenP_617 : Nat.Prime 617 := by norm_num
private theorem prime_eighteenP_1471 : Nat.Prime 1471 := by norm_num
private theorem prime_eighteenP_19163 : Nat.Prime 19163 := by norm_num
private theorem prime_eighteenP_1739247294101 : Nat.Prime 1739247294101 := by
  apply lucas_primality 1739247294101 (2 : ZMod 1739247294101)
  · rw [← eighteenPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (5, 2), (617, 1), (1471, 1), (19163, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (5, 2), (617, 1), (1471, 1), (19163, 1)] : List FactorBlock).map factorBlockValue).prod = 1739247294101 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eighteenP_2
      · exact prime_eighteenP_5
      · exact prime_eighteenP_617
      · exact prime_eighteenP_1471
      · exact prime_eighteenP_19163
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1739247294101) ^ 869623647050 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (2 : ZMod 1739247294101) ^ 347849458820 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (2 : ZMod 1739247294101) ^ 2818877300 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (2 : ZMod 1739247294101) ^ 1182357100 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (2 : ZMod 1739247294101) ^ 90760700 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide

private theorem prime_eighteenP_295672039997171 : Nat.Prime 295672039997171 := by
  apply lucas_primality 295672039997171 (2 : ZMod 295672039997171)
  · rw [← eighteenPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 1), (17, 1), (1739247294101, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 1), (17, 1), (1739247294101, 1)] : List FactorBlock).map factorBlockValue).prod = 295672039997171 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eighteenP_2
      · exact prime_eighteenP_5
      · exact prime_eighteenP_17
      · exact prime_eighteenP_1739247294101
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 295672039997171) ^ 147836019998585 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (2 : ZMod 295672039997171) ^ 59134407999434 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (2 : ZMod 295672039997171) ^ 17392472941010 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (2 : ZMod 295672039997171) ^ 170 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide

private theorem prime_eighteenP_1789057110367522241537 : Nat.Prime 1789057110367522241537 := by
  apply lucas_primality 1789057110367522241537 (3 : ZMod 1789057110367522241537)
  · rw [← eighteenPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 10), (19, 1), (311, 1), (295672039997171, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 10), (19, 1), (311, 1), (295672039997171, 1)] : List FactorBlock).map factorBlockValue).prod = 1789057110367522241537 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eighteenP_2
      · exact prime_eighteenP_19
      · exact prime_eighteenP_311
      · exact prime_eighteenP_295672039997171
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1789057110367522241537) ^ 894528555183761120768 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (3 : ZMod 1789057110367522241537) ^ 94160900545659065344 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (3 : ZMod 1789057110367522241537) ^ 5752595210184958976 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (3 : ZMod 1789057110367522241537) ^ 6050816 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide

private theorem prime_eighteenP_18959 : Nat.Prime 18959 := by norm_num
private theorem prime_eighteenP_20930737 : Nat.Prime 20930737 := by
  apply lucas_primality 20930737 (5 : ZMod 20930737)
  · rw [← eighteenPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 4), (3, 1), (23, 1), (18959, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 4), (3, 1), (23, 1), (18959, 1)] : List FactorBlock).map factorBlockValue).prod = 20930737 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eighteenP_2
      · exact prime_eighteenP_3
      · exact prime_eighteenP_23
      · exact prime_eighteenP_18959
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 20930737) ^ 10465368 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (5 : ZMod 20930737) ^ 6976912 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (5 : ZMod 20930737) ^ 910032 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (5 : ZMod 20930737) ^ 1104 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide

private theorem prime_eighteenP_28807 : Nat.Prime 28807 := by norm_num
private theorem prime_eighteenP_1849103 : Nat.Prime 1849103 := by norm_num
private theorem prime_eighteenP_456818736397697 : Nat.Prime 456818736397697 := by
  apply lucas_primality 456818736397697 (3 : ZMod 456818736397697)
  · rw [← eighteenPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 7), (67, 1), (28807, 1), (1849103, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 7), (67, 1), (28807, 1), (1849103, 1)] : List FactorBlock).map factorBlockValue).prod = 456818736397697 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eighteenP_2
      · exact prime_eighteenP_67
      · exact prime_eighteenP_28807
      · exact prime_eighteenP_1849103
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 456818736397697) ^ 228409368198848 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (3 : ZMod 456818736397697) ^ 6818190095488 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (3 : ZMod 456818736397697) ^ 15857907328 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (3 : ZMod 456818736397697) ^ 247048832 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide

private theorem prime_eighteenP_6395462309567759 : Nat.Prime 6395462309567759 := by
  apply lucas_primality 6395462309567759 (7 : ZMod 6395462309567759)
  · rw [← eighteenPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (7, 1), (456818736397697, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (7, 1), (456818736397697, 1)] : List FactorBlock).map factorBlockValue).prod = 6395462309567759 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eighteenP_2
      · exact prime_eighteenP_7
      · exact prime_eighteenP_456818736397697
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 6395462309567759) ^ 3197731154783879 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (7 : ZMod 6395462309567759) ^ 913637472795394 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (7 : ZMod 6395462309567759) ^ 14 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide

private theorem prime_eighteenP_14121180779525611873 : Nat.Prime 14121180779525611873 := by
  apply lucas_primality 14121180779525611873 (5 : ZMod 14121180779525611873)
  · rw [← eighteenPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 5), (3, 1), (23, 1), (6395462309567759, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 5), (3, 1), (23, 1), (6395462309567759, 1)] : List FactorBlock).map factorBlockValue).prod = 14121180779525611873 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eighteenP_2
      · exact prime_eighteenP_3
      · exact prime_eighteenP_23
      · exact prime_eighteenP_6395462309567759
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 14121180779525611873) ^ 7060590389762805936 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (5 : ZMod 14121180779525611873) ^ 4707060259841870624 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (5 : ZMod 14121180779525611873) ^ 613964381718504864 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (5 : ZMod 14121180779525611873) ^ 2208 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide

private theorem prime_eighteenP_21280803913850800815204508873 : Nat.Prime 21280803913850800815204508873 := by
  apply lucas_primality 21280803913850800815204508873 (10 : ZMod 21280803913850800815204508873)
  · rw [← eighteenPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (3, 2), (20930737, 1), (14121180779525611873, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (3, 2), (20930737, 1), (14121180779525611873, 1)] : List FactorBlock).map factorBlockValue).prod = 21280803913850800815204508873 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eighteenP_2
      · exact prime_eighteenP_3
      · exact prime_eighteenP_20930737
      · exact prime_eighteenP_14121180779525611873
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (10 : ZMod 21280803913850800815204508873) ^ 10640401956925400407602254436 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (10 : ZMod 21280803913850800815204508873) ^ 7093601304616933605068169624 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (10 : ZMod 21280803913850800815204508873) ^ 1016725016125844054856 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (10 : ZMod 21280803913850800815204508873) ^ 1507013064 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide

private theorem prime_eighteenP_631 : Nat.Prime 631 := by norm_num
private theorem prime_eighteenP_7853 : Nat.Prime 7853 := by norm_num
private theorem prime_eighteenP_51564258659 : Nat.Prime 51564258659 := by
  apply lucas_primality 51564258659 (6 : ZMod 51564258659)
  · rw [← eighteenPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (11, 2), (43, 1), (631, 1), (7853, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (11, 2), (43, 1), (631, 1), (7853, 1)] : List FactorBlock).map factorBlockValue).prod = 51564258659 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eighteenP_2
      · exact prime_eighteenP_11
      · exact prime_eighteenP_43
      · exact prime_eighteenP_631
      · exact prime_eighteenP_7853
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 51564258659) ^ 25782129329 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (6 : ZMod 51564258659) ^ 4687659878 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (6 : ZMod 51564258659) ^ 1199168806 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (6 : ZMod 51564258659) ^ 81718318 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (6 : ZMod 51564258659) ^ 6566186 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide

private theorem prime_eighteenP_881 : Nat.Prime 881 := by norm_num
private theorem prime_eighteenP_1061 : Nat.Prime 1061 := by norm_num
private theorem prime_eighteenP_6307033 : Nat.Prime 6307033 := by norm_num
private theorem prime_eighteenP_5577088447446539 : Nat.Prime 5577088447446539 := by
  apply lucas_primality 5577088447446539 (2 : ZMod 5577088447446539)
  · rw [← eighteenPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (11, 1), (43, 1), (881, 1), (1061, 1), (6307033, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (11, 1), (43, 1), (881, 1), (1061, 1), (6307033, 1)] : List FactorBlock).map factorBlockValue).prod = 5577088447446539 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eighteenP_2
      · exact prime_eighteenP_11
      · exact prime_eighteenP_43
      · exact prime_eighteenP_881
      · exact prime_eighteenP_1061
      · exact prime_eighteenP_6307033
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 5577088447446539) ^ 2788544223723269 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (2 : ZMod 5577088447446539) ^ 507008040676958 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (2 : ZMod 5577088447446539) ^ 129699731335966 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (2 : ZMod 5577088447446539) ^ 6330406864298 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (2 : ZMod 5577088447446539) ^ 5256445285058 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (2 : ZMod 5577088447446539) ^ 884264986 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide

private theorem prime_eighteenP_489673 : Nat.Prime 489673 := by norm_num
private theorem prime_eighteenP_6911 : Nat.Prime 6911 := by norm_num
private theorem prime_eighteenP_8377 : Nat.Prime 8377 := by norm_num
private theorem prime_eighteenP_46649 : Nat.Prime 46649 := by norm_num
private theorem prime_eighteenP_54319 : Nat.Prime 54319 := by norm_num
private theorem prime_eighteenP_1466977702710658571 : Nat.Prime 1466977702710658571 := by
  apply lucas_primality 1466977702710658571 (2 : ZMod 1466977702710658571)
  · rw [← eighteenPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 1), (6911, 1), (8377, 1), (46649, 1), (54319, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 1), (6911, 1), (8377, 1), (46649, 1), (54319, 1)] : List FactorBlock).map factorBlockValue).prod = 1466977702710658571 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eighteenP_2
      · exact prime_eighteenP_5
      · exact prime_eighteenP_6911
      · exact prime_eighteenP_8377
      · exact prime_eighteenP_46649
      · exact prime_eighteenP_54319
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1466977702710658571) ^ 733488851355329285 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (2 : ZMod 1466977702710658571) ^ 293395540542131714 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (2 : ZMod 1466977702710658571) ^ 212267067386870 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (2 : ZMod 1466977702710658571) ^ 175119697112410 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (2 : ZMod 1466977702710658571) ^ 31447141475930 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (2 : ZMod 1466977702710658571) ^ 27006714091030 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide

private theorem prime_eighteenP_9029 : Nat.Prime 9029 := by norm_num
private theorem prime_eighteenP_3081137 : Nat.Prime 3081137 := by norm_num
private theorem prime_eighteenP_24593 : Nat.Prime 24593 := by norm_num
private theorem prime_eighteenP_55235879 : Nat.Prime 55235879 := by
  apply lucas_primality 55235879 (17 : ZMod 55235879)
  · rw [← eighteenPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (1123, 1), (24593, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (1123, 1), (24593, 1)] : List FactorBlock).map factorBlockValue).prod = 55235879 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eighteenP_2
      · exact prime_eighteenP_1123
      · exact prime_eighteenP_24593
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (17 : ZMod 55235879) ^ 27617939 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (17 : ZMod 55235879) ^ 49186 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (17 : ZMod 55235879) ^ 2246 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide

private theorem prime_eighteenP_143834228917 : Nat.Prime 143834228917 := by
  apply lucas_primality 143834228917 (13 : ZMod 143834228917)
  · rw [← eighteenPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (7, 1), (31, 1), (55235879, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (7, 1), (31, 1), (55235879, 1)] : List FactorBlock).map factorBlockValue).prod = 143834228917 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eighteenP_2
      · exact prime_eighteenP_3
      · exact prime_eighteenP_7
      · exact prime_eighteenP_31
      · exact prime_eighteenP_55235879
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 143834228917) ^ 71917114458 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (13 : ZMod 143834228917) ^ 47944742972 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (13 : ZMod 143834228917) ^ 20547746988 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (13 : ZMod 143834228917) ^ 4639813836 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (13 : ZMod 143834228917) ^ 2604 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide

private theorem prime_eighteenP_289835118837045663367 : Nat.Prime 289835118837045663367 := by
  apply lucas_primality 289835118837045663367 (3 : ZMod 289835118837045663367)
  · rw [← eighteenPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (109, 1), (3081137, 1), (143834228917, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (109, 1), (3081137, 1), (143834228917, 1)] : List FactorBlock).map factorBlockValue).prod = 289835118837045663367 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eighteenP_2
      · exact prime_eighteenP_3
      · exact prime_eighteenP_109
      · exact prime_eighteenP_3081137
      · exact prime_eighteenP_143834228917
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 289835118837045663367) ^ 144917559418522831683 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (3 : ZMod 289835118837045663367) ^ 96611706279015221122 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (3 : ZMod 289835118837045663367) ^ 2659037787495831774 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (3 : ZMod 289835118837045663367) ^ 94067585711718 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (3 : ZMod 289835118837045663367) ^ 2015063598 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide

private theorem prime_eighteenP_227 : Nat.Prime 227 := by norm_num
private theorem prime_eighteenP_9749 : Nat.Prime 9749 := by norm_num
private theorem prime_eighteenP_2223590917 : Nat.Prime 2223590917 := by
  apply lucas_primality 2223590917 (2 : ZMod 2223590917)
  · rw [← eighteenPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (83, 1), (229, 1), (9749, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (83, 1), (229, 1), (9749, 1)] : List FactorBlock).map factorBlockValue).prod = 2223590917 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eighteenP_2
      · exact prime_eighteenP_3
      · exact prime_eighteenP_83
      · exact prime_eighteenP_229
      · exact prime_eighteenP_9749
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 2223590917) ^ 1111795458 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (2 : ZMod 2223590917) ^ 741196972 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (2 : ZMod 2223590917) ^ 26790252 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (2 : ZMod 2223590917) ^ 9710004 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (2 : ZMod 2223590917) ^ 228084 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide

private theorem prime_eighteenP_233 : Nat.Prime 233 := by norm_num
private theorem prime_eighteenP_202661 : Nat.Prime 202661 := by norm_num
private theorem prime_eighteenP_5797763 : Nat.Prime 5797763 := by norm_num
private theorem prime_eighteenP_547540888461839 : Nat.Prime 547540888461839 := by
  apply lucas_primality 547540888461839 (23 : ZMod 547540888461839)
  · rw [← eighteenPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (233, 1), (202661, 1), (5797763, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (233, 1), (202661, 1), (5797763, 1)] : List FactorBlock).map factorBlockValue).prod = 547540888461839 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eighteenP_2
      · exact prime_eighteenP_233
      · exact prime_eighteenP_202661
      · exact prime_eighteenP_5797763
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (23 : ZMod 547540888461839) ^ 273770444230919 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (23 : ZMod 547540888461839) ^ 2349960894686 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (23 : ZMod 547540888461839) ^ 2701757558 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (23 : ZMod 547540888461839) ^ 94440026 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide

private theorem prime_eighteenP_272830819408343600194929601 : Nat.Prime 272830819408343600194929601 := by
  apply lucas_primality 272830819408343600194929601 (39 : ZMod 272830819408343600194929601)
  · rw [← eighteenPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 6), (3, 4), (5, 2), (7, 2), (11, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 6), (3, 4), (5, 2), (7, 2), (11, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod = 272830819408343600194929601 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eighteenP_2
      · exact prime_eighteenP_3
      · exact prime_eighteenP_5
      · exact prime_eighteenP_7
      · exact prime_eighteenP_11
      · exact prime_eighteenP_17
      · exact prime_eighteenP_19
      · exact prime_eighteenP_23
      · exact prime_eighteenP_29
      · exact prime_eighteenP_31
      · exact prime_eighteenP_37
      · exact prime_eighteenP_41
      · exact prime_eighteenP_43
      · exact prime_eighteenP_47
      · exact prime_eighteenP_53
      · exact prime_eighteenP_59
      · exact prime_eighteenP_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (39 : ZMod 272830819408343600194929601) ^ 136415409704171800097464800 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (39 : ZMod 272830819408343600194929601) ^ 90943606469447866731643200 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (39 : ZMod 272830819408343600194929601) ^ 54566163881668720038985920 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (39 : ZMod 272830819408343600194929601) ^ 38975831344049085742132800 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (39 : ZMod 272830819408343600194929601) ^ 24802801764394872744993600 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (39 : ZMod 272830819408343600194929601) ^ 16048871729902564717348800 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (39 : ZMod 272830819408343600194929601) ^ 14359516810965452641838400 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (39 : ZMod 272830819408343600194929601) ^ 11862209539493200008475200 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (39 : ZMod 272830819408343600194929601) ^ 9407959289942882765342400 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (39 : ZMod 272830819408343600194929601) ^ 8800994174462696780481600 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (39 : ZMod 272830819408343600194929601) ^ 7373805929955232437700800 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (39 : ZMod 272830819408343600194929601) ^ 6654410229471795126705600 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (39 : ZMod 272830819408343600194929601) ^ 6344902776938223260347200 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (39 : ZMod 272830819408343600194929601) ^ 5804911051241353195636800 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (39 : ZMod 272830819408343600194929601) ^ 5147751309591388682923200 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (39 : ZMod 272830819408343600194929601) ^ 4624251176412603393134400 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (39 : ZMod 272830819408343600194929601) ^ 4472636383743337708113600 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide

private theorem prime_eighteenP_1509163 : Nat.Prime 1509163 := by norm_num
private theorem prime_eighteenP_9011 : Nat.Prime 9011 := by norm_num
private theorem prime_eighteenP_1572401 : Nat.Prime 1572401 := by norm_num
private theorem prime_eighteenP_106923269 : Nat.Prime 106923269 := by
  apply lucas_primality 106923269 (2 : ZMod 106923269)
  · rw [← eighteenPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (17, 1), (1572401, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (17, 1), (1572401, 1)] : List FactorBlock).map factorBlockValue).prod = 106923269 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eighteenP_2
      · exact prime_eighteenP_17
      · exact prime_eighteenP_1572401
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 106923269) ^ 53461634 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (2 : ZMod 106923269) ^ 6289604 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (2 : ZMod 106923269) ^ 68 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide

private theorem prime_eighteenP_42027240866951581 : Nat.Prime 42027240866951581 := by
  apply lucas_primality 42027240866951581 (6 : ZMod 42027240866951581)
  · rw [← eighteenPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (5, 1), (727, 1), (9011, 1), (106923269, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (5, 1), (727, 1), (9011, 1), (106923269, 1)] : List FactorBlock).map factorBlockValue).prod = 42027240866951581 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eighteenP_2
      · exact prime_eighteenP_3
      · exact prime_eighteenP_5
      · exact prime_eighteenP_727
      · exact prime_eighteenP_9011
      · exact prime_eighteenP_106923269
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 42027240866951581) ^ 21013620433475790 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (6 : ZMod 42027240866951581) ^ 14009080288983860 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (6 : ZMod 42027240866951581) ^ 8405448173390316 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (6 : ZMod 42027240866951581) ^ 57809134617540 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (6 : ZMod 42027240866951581) ^ 4663992993780 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (6 : ZMod 42027240866951581) ^ 393059820 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide

private theorem prime_eighteenP_924599299072934783 : Nat.Prime 924599299072934783 := by
  apply lucas_primality 924599299072934783 (5 : ZMod 924599299072934783)
  · rw [← eighteenPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (11, 1), (42027240866951581, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (11, 1), (42027240866951581, 1)] : List FactorBlock).map factorBlockValue).prod = 924599299072934783 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eighteenP_2
      · exact prime_eighteenP_11
      · exact prime_eighteenP_42027240866951581
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 924599299072934783) ^ 462299649536467391 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (5 : ZMod 924599299072934783) ^ 84054481733903162 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (5 : ZMod 924599299072934783) ^ 22 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide

private theorem prime_eighteenP_2239 : Nat.Prime 2239 := by norm_num
private theorem prime_eighteenP_2609 : Nat.Prime 2609 := by norm_num
private theorem prime_eighteenP_276707 : Nat.Prime 276707 := by norm_num
private theorem prime_eighteenP_4175273 : Nat.Prime 4175273 := by norm_num
private theorem prime_eighteenP_394153 : Nat.Prime 394153 := by norm_num
private theorem prime_eighteenP_39415301 : Nat.Prime 39415301 := by
  apply lucas_primality 39415301 (2 : ZMod 39415301)
  · rw [← eighteenPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (5, 2), (394153, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (5, 2), (394153, 1)] : List FactorBlock).map factorBlockValue).prod = 39415301 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eighteenP_2
      · exact prime_eighteenP_5
      · exact prime_eighteenP_394153
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 39415301) ^ 19707650 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (2 : ZMod 39415301) ^ 7883060 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (2 : ZMod 39415301) ^ 100 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide

private theorem prime_eighteenP_491 : Nat.Prime 491 := by norm_num
private theorem prime_eighteenP_9492089 : Nat.Prime 9492089 := by norm_num
private theorem prime_eighteenP_1307 : Nat.Prime 1307 := by norm_num
private theorem prime_eighteenP_205253 : Nat.Prime 205253 := by norm_num
private theorem prime_eighteenP_792993323477 : Nat.Prime 792993323477 := by
  apply lucas_primality 792993323477 (2 : ZMod 792993323477)
  · rw [← eighteenPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (739, 1), (1307, 1), (205253, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (739, 1), (1307, 1), (205253, 1)] : List FactorBlock).map factorBlockValue).prod = 792993323477 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eighteenP_2
      · exact prime_eighteenP_739
      · exact prime_eighteenP_1307
      · exact prime_eighteenP_205253
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 792993323477) ^ 396496661738 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (2 : ZMod 792993323477) ^ 1073062684 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (2 : ZMod 792993323477) ^ 606727868 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (2 : ZMod 792993323477) ^ 3863492 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide

private theorem prime_eighteenP_22613 : Nat.Prime 22613 := by norm_num
private theorem prime_eighteenP_907 : Nat.Prime 907 := by norm_num
private theorem prime_eighteenP_105373 : Nat.Prime 105373 := by norm_num
private theorem prime_eighteenP_1114549 : Nat.Prime 1114549 := by norm_num
private theorem prime_eighteenP_668729401 : Nat.Prime 668729401 := by
  apply lucas_primality 668729401 (11 : ZMod 668729401)
  · rw [← eighteenPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (3, 1), (5, 2), (1114549, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (3, 1), (5, 2), (1114549, 1)] : List FactorBlock).map factorBlockValue).prod = 668729401 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eighteenP_2
      · exact prime_eighteenP_3
      · exact prime_eighteenP_5
      · exact prime_eighteenP_1114549
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 668729401) ^ 334364700 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (11 : ZMod 668729401) ^ 222909800 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (11 : ZMod 668729401) ^ 133745880 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (11 : ZMod 668729401) ^ 600 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide

private theorem prime_eighteenP_3163360712218255117 : Nat.Prime 3163360712218255117 := by
  apply lucas_primality 3163360712218255117 (2 : ZMod 3163360712218255117)
  · rw [← eighteenPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 2), (29, 1), (43, 1), (105373, 1), (668729401, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 2), (29, 1), (43, 1), (105373, 1), (668729401, 1)] : List FactorBlock).map factorBlockValue).prod = 3163360712218255117 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eighteenP_2
      · exact prime_eighteenP_3
      · exact prime_eighteenP_29
      · exact prime_eighteenP_43
      · exact prime_eighteenP_105373
      · exact prime_eighteenP_668729401
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 3163360712218255117) ^ 1581680356109127558 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (2 : ZMod 3163360712218255117) ^ 1054453570739418372 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (2 : ZMod 3163360712218255117) ^ 109081403869595004 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (2 : ZMod 3163360712218255117) ^ 73566528191122212 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (2 : ZMod 3163360712218255117) ^ 30020600269692 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (2 : ZMod 3163360712218255117) ^ 4730404716 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide

private theorem prime_eighteenP_11476672663927829564477 : Nat.Prime 11476672663927829564477 := by
  apply lucas_primality 11476672663927829564477 (2 : ZMod 11476672663927829564477)
  · rw [← eighteenPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (907, 1), (3163360712218255117, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (907, 1), (3163360712218255117, 1)] : List FactorBlock).map factorBlockValue).prod = 11476672663927829564477 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eighteenP_2
      · exact prime_eighteenP_907
      · exact prime_eighteenP_3163360712218255117
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 11476672663927829564477) ^ 5738336331963914782238 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (2 : ZMod 11476672663927829564477) ^ 12653442848873020468 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (2 : ZMod 11476672663927829564477) ^ 3628 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide

private theorem prime_eighteenP_5418419 : Nat.Prime 5418419 := by norm_num
private theorem prime_eighteenP_401 : Nat.Prime 401 := by norm_num
private theorem prime_eighteenP_4426561 : Nat.Prime 4426561 := by norm_num
private theorem prime_eighteenP_8314577 : Nat.Prime 8314577 := by norm_num
private theorem prime_eighteenP_531316724189705893 : Nat.Prime 531316724189705893 := by
  apply lucas_primality 531316724189705893 (6 : ZMod 531316724189705893)
  · rw [← eighteenPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 2), (401, 1), (4426561, 1), (8314577, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 2), (401, 1), (4426561, 1), (8314577, 1)] : List FactorBlock).map factorBlockValue).prod = 531316724189705893 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eighteenP_2
      · exact prime_eighteenP_3
      · exact prime_eighteenP_401
      · exact prime_eighteenP_4426561
      · exact prime_eighteenP_8314577
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 531316724189705893) ^ 265658362094852946 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (6 : ZMod 531316724189705893) ^ 177105574729901964 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (6 : ZMod 531316724189705893) ^ 1324979362069092 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (6 : ZMod 531316724189705893) ^ 120029233572 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (6 : ZMod 531316724189705893) ^ 63901834596 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide

private theorem prime_eighteenP_3927493225210305961057 : Nat.Prime 3927493225210305961057 := by
  apply lucas_primality 3927493225210305961057 (19 : ZMod 3927493225210305961057)
  · rw [← eighteenPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 5), (3, 1), (7, 1), (11, 1), (531316724189705893, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 5), (3, 1), (7, 1), (11, 1), (531316724189705893, 1)] : List FactorBlock).map factorBlockValue).prod = 3927493225210305961057 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eighteenP_2
      · exact prime_eighteenP_3
      · exact prime_eighteenP_7
      · exact prime_eighteenP_11
      · exact prime_eighteenP_531316724189705893
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (19 : ZMod 3927493225210305961057) ^ 1963746612605152980528 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (19 : ZMod 3927493225210305961057) ^ 1309164408403435320352 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (19 : ZMod 3927493225210305961057) ^ 561070460744329423008 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (19 : ZMod 3927493225210305961057) ^ 357044838655482360096 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (19 : ZMod 3927493225210305961057) ^ 7392 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide

private theorem prime_eighteenP_339389 : Nat.Prime 339389 := by norm_num
private theorem prime_eighteenP_545911 : Nat.Prime 545911 := by norm_num
private theorem prime_eighteenP_2940799 : Nat.Prime 2940799 := by norm_num
private theorem prime_eighteenP_1723 : Nat.Prime 1723 := by norm_num
private theorem prime_eighteenP_464968781 : Nat.Prime 464968781 := by
  apply lucas_primality 464968781 (2 : ZMod 464968781)
  · rw [← eighteenPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (5, 1), (103, 1), (131, 1), (1723, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (5, 1), (103, 1), (131, 1), (1723, 1)] : List FactorBlock).map factorBlockValue).prod = 464968781 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eighteenP_2
      · exact prime_eighteenP_5
      · exact prime_eighteenP_103
      · exact prime_eighteenP_131
      · exact prime_eighteenP_1723
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 464968781) ^ 232484390 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (2 : ZMod 464968781) ^ 92993756 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (2 : ZMod 464968781) ^ 4514260 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (2 : ZMod 464968781) ^ 3549380 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (2 : ZMod 464968781) ^ 269860 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide

private theorem prime_eighteenP_250362398986480009590641281 : Nat.Prime 250362398986480009590641281 := by
  apply lucas_primality 250362398986480009590641281 (67 : ZMod 250362398986480009590641281)
  · rw [← eighteenPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 7), (3, 5), (5, 1), (7, 2), (11, 1), (13, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 7), (3, 5), (5, 1), (7, 2), (11, 1), (13, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod = 250362398986480009590641281 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eighteenP_2
      · exact prime_eighteenP_3
      · exact prime_eighteenP_5
      · exact prime_eighteenP_7
      · exact prime_eighteenP_11
      · exact prime_eighteenP_13
      · exact prime_eighteenP_19
      · exact prime_eighteenP_23
      · exact prime_eighteenP_29
      · exact prime_eighteenP_31
      · exact prime_eighteenP_37
      · exact prime_eighteenP_41
      · exact prime_eighteenP_43
      · exact prime_eighteenP_47
      · exact prime_eighteenP_53
      · exact prime_eighteenP_59
      · exact prime_eighteenP_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (67 : ZMod 250362398986480009590641281) ^ 125181199493240004795320640 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (67 : ZMod 250362398986480009590641281) ^ 83454132995493336530213760 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (67 : ZMod 250362398986480009590641281) ^ 50072479797296001918128256 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (67 : ZMod 250362398986480009590641281) ^ 35766056998068572798663040 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (67 : ZMod 250362398986480009590641281) ^ 22760218089680000871876480 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (67 : ZMod 250362398986480009590641281) ^ 19258646075883077660818560 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (67 : ZMod 250362398986480009590641281) ^ 13176968367709474188981120 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (67 : ZMod 250362398986480009590641281) ^ 10885321695064348243071360 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (67 : ZMod 250362398986480009590641281) ^ 8633186171947586537608320 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (67 : ZMod 250362398986480009590641281) ^ 8076206418918709986794880 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (67 : ZMod 250362398986480009590641281) ^ 6766551323958919178125440 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (67 : ZMod 250362398986480009590641281) ^ 6106399975280000233918080 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (67 : ZMod 250362398986480009590641281) ^ 5822381371778604874200960 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (67 : ZMod 250362398986480009590641281) ^ 5326859552903829991290240 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (67 : ZMod 250362398986480009590641281) ^ 4723818848801509614917760 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (67 : ZMod 250362398986480009590641281) ^ 4243430491296271348993920 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (67 : ZMod 250362398986480009590641281) ^ 4104301622729180485092480 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide

private theorem prime_eighteenP_173827 : Nat.Prime 173827 := by norm_num
private theorem prime_eighteenP_1103 : Nat.Prime 1103 := by norm_num
private theorem prime_eighteenP_3001 : Nat.Prime 3001 := by norm_num
private theorem prime_eighteenP_19996541 : Nat.Prime 19996541 := by norm_num
private theorem prime_eighteenP_7438713253 : Nat.Prime 7438713253 := by
  apply lucas_primality 7438713253 (2 : ZMod 7438713253)
  · rw [← eighteenPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (31, 1), (19996541, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (31, 1), (19996541, 1)] : List FactorBlock).map factorBlockValue).prod = 7438713253 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eighteenP_2
      · exact prime_eighteenP_3
      · exact prime_eighteenP_31
      · exact prime_eighteenP_19996541
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 7438713253) ^ 3719356626 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (2 : ZMod 7438713253) ^ 2479571084 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (2 : ZMod 7438713253) ^ 239958492 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (2 : ZMod 7438713253) ^ 372 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide

private theorem prime_eighteenP_10390866777165714899 : Nat.Prime 10390866777165714899 := by
  apply lucas_primality 10390866777165714899 (2 : ZMod 10390866777165714899)
  · rw [← eighteenPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (211, 1), (1103, 1), (3001, 1), (7438713253, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (211, 1), (1103, 1), (3001, 1), (7438713253, 1)] : List FactorBlock).map factorBlockValue).prod = 10390866777165714899 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eighteenP_2
      · exact prime_eighteenP_211
      · exact prime_eighteenP_1103
      · exact prime_eighteenP_3001
      · exact prime_eighteenP_7438713253
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 10390866777165714899) ^ 5195433388582857449 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (2 : ZMod 10390866777165714899) ^ 49245814109790118 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (2 : ZMod 10390866777165714899) ^ 9420550115290766 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (2 : ZMod 10390866777165714899) ^ 3462468103020898 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (2 : ZMod 10390866777165714899) ^ 1396863466 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide

private theorem prime_eighteenP_1417679 : Nat.Prime 1417679 := by norm_num
private theorem prime_eighteenP_59553859433 : Nat.Prime 59553859433 := by
  apply lucas_primality 59553859433 (3 : ZMod 59553859433)
  · rw [← eighteenPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (59, 1), (89, 1), (1417679, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (59, 1), (89, 1), (1417679, 1)] : List FactorBlock).map factorBlockValue).prod = 59553859433 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eighteenP_2
      · exact prime_eighteenP_59
      · exact prime_eighteenP_89
      · exact prime_eighteenP_1417679
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 59553859433) ^ 29776929716 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (3 : ZMod 59553859433) ^ 1009387448 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (3 : ZMod 59553859433) ^ 669144488 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (3 : ZMod 59553859433) ^ 42008 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide

private theorem prime_eighteenP_499 : Nat.Prime 499 := by norm_num
private theorem prime_eighteenP_647 : Nat.Prime 647 := by norm_num
private theorem prime_eighteenP_9521 : Nat.Prime 9521 := by norm_num
private theorem prime_eighteenP_61600871 : Nat.Prime 61600871 := by
  apply lucas_primality 61600871 (13 : ZMod 61600871)
  · rw [← eighteenPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 1), (647, 1), (9521, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 1), (647, 1), (9521, 1)] : List FactorBlock).map factorBlockValue).prod = 61600871 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eighteenP_2
      · exact prime_eighteenP_5
      · exact prime_eighteenP_647
      · exact prime_eighteenP_9521
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (13 : ZMod 61600871) ^ 30800435 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (13 : ZMod 61600871) ^ 12320174 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (13 : ZMod 61600871) ^ 95210 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (13 : ZMod 61600871) ^ 6470 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide

private theorem prime_eighteenP_5225601886931 : Nat.Prime 5225601886931 := by
  apply lucas_primality 5225601886931 (2 : ZMod 5225601886931)
  · rw [← eighteenPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 1), (17, 1), (499, 1), (61600871, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 1), (17, 1), (499, 1), (61600871, 1)] : List FactorBlock).map factorBlockValue).prod = 5225601886931 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eighteenP_2
      · exact prime_eighteenP_5
      · exact prime_eighteenP_17
      · exact prime_eighteenP_499
      · exact prime_eighteenP_61600871
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 5225601886931) ^ 2612800943465 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (2 : ZMod 5225601886931) ^ 1045120377386 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (2 : ZMod 5225601886931) ^ 307388346290 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (2 : ZMod 5225601886931) ^ 10472148070 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (2 : ZMod 5225601886931) ^ 84830 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide

private theorem prime_eighteenP_31353611321587 : Nat.Prime 31353611321587 := by
  apply lucas_primality 31353611321587 (2 : ZMod 31353611321587)
  · rw [← eighteenPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (5225601886931, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (5225601886931, 1)] : List FactorBlock).map factorBlockValue).prod = 31353611321587 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eighteenP_2
      · exact prime_eighteenP_3
      · exact prime_eighteenP_5225601886931
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 31353611321587) ^ 15676805660793 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (2 : ZMod 31353611321587) ^ 10451203773862 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (2 : ZMod 31353611321587) ^ 6 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide

private theorem prime_eighteenP_55807 : Nat.Prime 55807 := by norm_num
private theorem prime_eighteenP_842077 : Nat.Prime 842077 := by norm_num
private theorem prime_eighteenP_3511 : Nat.Prime 3511 := by norm_num
private theorem prime_eighteenP_86851 : Nat.Prime 86851 := by norm_num
private theorem prime_eighteenP_2500457660201 : Nat.Prime 2500457660201 := by
  apply lucas_primality 2500457660201 (3 : ZMod 2500457660201)
  · rw [← eighteenPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (5, 2), (41, 1), (3511, 1), (86851, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (5, 2), (41, 1), (3511, 1), (86851, 1)] : List FactorBlock).map factorBlockValue).prod = 2500457660201 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eighteenP_2
      · exact prime_eighteenP_5
      · exact prime_eighteenP_41
      · exact prime_eighteenP_3511
      · exact prime_eighteenP_86851
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 2500457660201) ^ 1250228830100 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (3 : ZMod 2500457660201) ^ 500091532040 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (3 : ZMod 2500457660201) ^ 60986772200 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (3 : ZMod 2500457660201) ^ 712178200 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (3 : ZMod 2500457660201) ^ 28790200 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide

private theorem prime_eighteenP_5145941864693659 : Nat.Prime 5145941864693659 := by
  apply lucas_primality 5145941864693659 (3 : ZMod 5145941864693659)
  · rw [← eighteenPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (7, 3), (2500457660201, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (7, 3), (2500457660201, 1)] : List FactorBlock).map factorBlockValue).prod = 5145941864693659 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eighteenP_2
      · exact prime_eighteenP_3
      · exact prime_eighteenP_7
      · exact prime_eighteenP_2500457660201
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 5145941864693659) ^ 2572970932346829 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (3 : ZMod 5145941864693659) ^ 1715313954897886 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (3 : ZMod 5145941864693659) ^ 735134552099094 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (3 : ZMod 5145941864693659) ^ 2058 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide

private theorem prime_eighteenP_21280803913850800815204508889 : Nat.Prime 21280803913850800815204508889 := by
  apply lucas_primality 21280803913850800815204508889 (3 : ZMod 21280803913850800815204508889)
  · rw [← eighteenPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (11, 1), (55807, 1), (842077, 1), (5145941864693659, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (11, 1), (55807, 1), (842077, 1), (5145941864693659, 1)] : List FactorBlock).map factorBlockValue).prod = 21280803913850800815204508889 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eighteenP_2
      · exact prime_eighteenP_11
      · exact prime_eighteenP_55807
      · exact prime_eighteenP_842077
      · exact prime_eighteenP_5145941864693659
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 21280803913850800815204508889) ^ 10640401956925400407602254444 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (3 : ZMod 21280803913850800815204508889) ^ 1934618537622800074109500808 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (3 : ZMod 21280803913850800815204508889) ^ 381328577308416521497384 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (3 : ZMod 21280803913850800815204508889) ^ 25271802832580394447544 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (3 : ZMod 21280803913850800815204508889) ^ 4135453620232 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide

private theorem prime_eighteenP_1355153 : Nat.Prime 1355153 := by norm_num
private theorem prime_eighteenP_626080687 : Nat.Prime 626080687 := by
  apply lucas_primality 626080687 (5 : ZMod 626080687)
  · rw [← eighteenPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (7, 1), (11, 1), (1355153, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (7, 1), (11, 1), (1355153, 1)] : List FactorBlock).map factorBlockValue).prod = 626080687 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eighteenP_2
      · exact prime_eighteenP_3
      · exact prime_eighteenP_7
      · exact prime_eighteenP_11
      · exact prime_eighteenP_1355153
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 626080687) ^ 313040343 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (5 : ZMod 626080687) ^ 208693562 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (5 : ZMod 626080687) ^ 89440098 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (5 : ZMod 626080687) ^ 56916426 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (5 : ZMod 626080687) ^ 462 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide

private theorem prime_eighteenP_5037757 : Nat.Prime 5037757 := by norm_num
private theorem prime_eighteenP_14751743 : Nat.Prime 14751743 := by norm_num
private theorem prime_eighteenP_377672369920211983 : Nat.Prime 377672369920211983 := by
  apply lucas_primality 377672369920211983 (3 : ZMod 377672369920211983)
  · rw [← eighteenPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (7, 1), (11, 2), (5037757, 1), (14751743, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (7, 1), (11, 2), (5037757, 1), (14751743, 1)] : List FactorBlock).map factorBlockValue).prod = 377672369920211983 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eighteenP_2
      · exact prime_eighteenP_3
      · exact prime_eighteenP_7
      · exact prime_eighteenP_11
      · exact prime_eighteenP_5037757
      · exact prime_eighteenP_14751743
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 377672369920211983) ^ 188836184960105991 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (3 : ZMod 377672369920211983) ^ 125890789973403994 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (3 : ZMod 377672369920211983) ^ 53953195702887426 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (3 : ZMod 377672369920211983) ^ 34333851810928362 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (3 : ZMod 377672369920211983) ^ 74968357926 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (3 : ZMod 377672369920211983) ^ 25601881074 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide

private theorem prime_eighteenP_857 : Nat.Prime 857 := by norm_num
private theorem prime_eighteenP_15493 : Nat.Prime 15493 := by norm_num
private theorem prime_eighteenP_29297 : Nat.Prime 29297 := by norm_num
private theorem prime_eighteenP_3196723 : Nat.Prime 3196723 := by norm_num
private theorem prime_eighteenP_2089583 : Nat.Prime 2089583 := by norm_num
private theorem prime_eighteenP_188062471 : Nat.Prime 188062471 := by
  apply lucas_primality 188062471 (3 : ZMod 188062471)
  · rw [← eighteenPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 2), (5, 1), (2089583, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 2), (5, 1), (2089583, 1)] : List FactorBlock).map factorBlockValue).prod = 188062471 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eighteenP_2
      · exact prime_eighteenP_3
      · exact prime_eighteenP_5
      · exact prime_eighteenP_2089583
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 188062471) ^ 94031235 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (3 : ZMod 188062471) ^ 62687490 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (3 : ZMod 188062471) ^ 37612494 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide
    · change (3 : ZMod 188062471) ^ 90 ≠ 1
      rw [← eighteenPFastPow_eq_pow]
      decide

private theorem phi_eighteenP_21280803913850800815204508792 : Nat.totient 21280803913850800815204508792 = 10606407062494328840804801856 := by
  rw [← show ((([(2, 3), (313, 1), (8498723607767891699362823, 1)] : List FactorBlock).map factorBlockValue).prod) = 21280803913850800815204508792 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eighteenP_2, prime_eighteenP_313, prime_eighteenP_8498723607767891699362823]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eighteenP_21280803913850800815204508793 : Nat.totient 21280803913850800815204508793 = 18146177726688469681062614784 := by
  rw [← show ((([(7, 1), (193, 1), (15751890387750407709255743, 1)] : List FactorBlock).map factorBlockValue).prod) = 21280803913850800815204508793 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eighteenP_7, prime_eighteenP_193, prime_eighteenP_15751890387750407709255743]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eighteenP_21280803913850800815204508794 : Nat.totient 21280803913850800815204508794 = 7091792231120772871953438720 := by
  rw [← show ((([(2, 1), (3, 1), (3923, 1), (8197093, 1), (110295707065568641, 1)] : List FactorBlock).map factorBlockValue).prod) = 21280803913850800815204508794 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eighteenP_2, prime_eighteenP_3, prime_eighteenP_3923, prime_eighteenP_8197093, prime_eighteenP_110295707065568641]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eighteenP_21280803913850800815204508795 : Nat.totient 21280803913850800815204508795 = 17024162113841890598744649216 := by
  rw [← show ((([(5, 1), (35393, 1), (120254309687513354704063, 1)] : List FactorBlock).map factorBlockValue).prod) = 21280803913850800815204508795 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eighteenP_5, prime_eighteenP_35393, prime_eighteenP_120254309687513354704063]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eighteenP_21280803913850800815204508796 : Nat.totient 21280803913850800815204508796 = 10505652988184425469555277120 := by
  rw [← show ((([(2, 2), (79, 1), (189067, 1), (2202311, 1), (161735950924213, 1)] : List FactorBlock).map factorBlockValue).prod) = 21280803913850800815204508796 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eighteenP_2, prime_eighteenP_79, prime_eighteenP_189067, prime_eighteenP_2202311, prime_eighteenP_161735950924213]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eighteenP_21280803913850800815204508797 : Nat.totient 21280803913850800815204508797 = 13986180465894842667327004160 := by
  rw [← show ((([(3, 1), (71, 1), (11633, 1), (8588487709947216218393, 1)] : List FactorBlock).map factorBlockValue).prod) = 21280803913850800815204508797 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eighteenP_3, prime_eighteenP_71, prime_eighteenP_11633, prime_eighteenP_8588487709947216218393]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eighteenP_21280803913850800815204508798 : Nat.totient 21280803913850800815204508798 = 10530420468134277805495879680 := by
  rw [← show ((([(2, 1), (97, 1), (36749, 1), (160512643, 1), (18596513447881, 1)] : List FactorBlock).map factorBlockValue).prod) = 21280803913850800815204508798 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eighteenP_2, prime_eighteenP_97, prime_eighteenP_36749, prime_eighteenP_160512643, prime_eighteenP_18596513447881]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eighteenP_21280803913850800815204508799 : Nat.totient 21280803913850800815204508799 = 21280782352337545898644018440 := by
  rw [← show ((([(986981, 1), (21561513254916559503379, 1)] : List FactorBlock).map factorBlockValue).prod) = 21280803913850800815204508799 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eighteenP_986981, prime_eighteenP_21561513254916559503379]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eighteenP_21280803913850800815204508800 : Nat.totient 21280803913850800815204508800 = 2800284632268491508940800000 := by
  rw [← show ((([(2, 7), (3, 5), (5, 2), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 21280803913850800815204508800 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eighteenP_2, prime_eighteenP_3, prime_eighteenP_5, prime_eighteenP_7, prime_eighteenP_11, prime_eighteenP_13, prime_eighteenP_17, prime_eighteenP_19, prime_eighteenP_23, prime_eighteenP_29, prime_eighteenP_31, prime_eighteenP_37, prime_eighteenP_41, prime_eighteenP_43, prime_eighteenP_47, prime_eighteenP_53, prime_eighteenP_59, prime_eighteenP_61]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eighteenP_21280803913850800815204508801 : Nat.totient 21280803913850800815204508801 = 21279454888297731959293893888 := by
  rw [← show ((([(26417, 1), (39157, 1), (20572881415656670829, 1)] : List FactorBlock).map factorBlockValue).prod) = 21280803913850800815204508801 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eighteenP_26417, prime_eighteenP_39157, prime_eighteenP_20572881415656670829]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eighteenP_21280803913850800815204508802 : Nat.totient 21280803913850800815204508802 = 10604086591884699382320335152 := by
  rw [← show ((([(2, 1), (293, 1), (36315365040701025281918957, 1)] : List FactorBlock).map factorBlockValue).prod) = 21280803913850800815204508802 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eighteenP_2, prime_eighteenP_293, prime_eighteenP_36315365040701025281918957]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eighteenP_21280803913850800815204508803 : Nat.totient 21280803913850800815204508803 = 14187080202959039276371584960 := by
  rw [← show ((([(3, 1), (115903, 1), (32244294937, 1), (1898100541591, 1)] : List FactorBlock).map factorBlockValue).prod) = 21280803913850800815204508803 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eighteenP_3, prime_eighteenP_115903, prime_eighteenP_32244294937, prime_eighteenP_1898100541591]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eighteenP_21280803913850800815204508804 : Nat.totient 21280803913850800815204508804 = 10636404730263280306334937600 := by
  rw [← show ((([(2, 2), (2663, 1), (9063547, 1), (26126021, 1), (8436948721, 1)] : List FactorBlock).map factorBlockValue).prod) = 21280803913850800815204508804 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eighteenP_2, prime_eighteenP_2663, prime_eighteenP_9063547, prime_eighteenP_26126021, prime_eighteenP_8436948721]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eighteenP_21280803913850800815204508805 : Nat.totient 21280803913850800815204508805 = 17024643131080640652163607040 := by
  rw [← show ((([(5, 1), (4256160782770160163040901761, 1)] : List FactorBlock).map factorBlockValue).prod) = 21280803913850800815204508805 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eighteenP_5, prime_eighteenP_4256160782770160163040901761]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eighteenP_21280803913850800815204508806 : Nat.totient 21280803913850800815204508806 = 7093601304383813978677452200 := by
  rw [← show ((([(2, 1), (3, 1), (30429025931, 1), (116559782766332771, 1)] : List FactorBlock).map factorBlockValue).prod) = 21280803913850800815204508806 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eighteenP_2, prime_eighteenP_3, prime_eighteenP_30429025931, prime_eighteenP_116559782766332771]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eighteenP_21280803913850800815204508807 : Nat.totient 21280803913850800815204508807 = 18235252366398532689923449728 := by
  rw [← show ((([(7, 1), (4177, 1), (17047, 1), (42695052666442357879, 1)] : List FactorBlock).map factorBlockValue).prod) = 21280803913850800815204508807 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eighteenP_7, prime_eighteenP_4177, prime_eighteenP_17047, prime_eighteenP_42695052666442357879]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eighteenP_21280803913850800815204508808 : Nat.totient 21280803913850800815204508808 = 10636459169680880857285128192 := by
  rw [← show ((([(2, 3), (3137, 1), (19309, 1), (43916097622182558197, 1)] : List FactorBlock).map factorBlockValue).prod) = 21280803913850800815204508808 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eighteenP_2, prime_eighteenP_3137, prime_eighteenP_19309, prime_eighteenP_43916097622182558197]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eighteenP_21280803913850800815204508809 : Nat.totient 21280803913850800815204508809 = 14187135113158311726045645312 := by
  rw [← show ((([(3, 2), (210193, 1), (11249345925914014905457, 1)] : List FactorBlock).map factorBlockValue).prod) = 21280803913850800815204508809 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eighteenP_3, prime_eighteenP_210193, prime_eighteenP_11249345925914014905457]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eighteenP_21280803913850800815204508810 : Nat.totient 21280803913850800815204508810 = 8509511244484644338548800000 := by
  rw [← show ((([(2, 1), (5, 1), (3181, 1), (73571, 1), (455881, 1), (19946477413151, 1)] : List FactorBlock).map factorBlockValue).prod) = 21280803913850800815204508810 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eighteenP_2, prime_eighteenP_5, prime_eighteenP_3181, prime_eighteenP_73571, prime_eighteenP_455881, prime_eighteenP_19946477413151]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eighteenP_21280803913850800815204508811 : Nat.totient 21280803913850800815204508811 = 19346057078217003877880569000 := by
  rw [← show ((([(11, 1), (150791, 1), (12829801099686321293111, 1)] : List FactorBlock).map factorBlockValue).prod) = 21280803913850800815204508811 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eighteenP_11, prime_eighteenP_150791, prime_eighteenP_12829801099686321293111]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eighteenP_21280803913850800815204508812 : Nat.totient 21280803913850800815204508812 = 7092663234788967769154350080 := by
  rw [← show ((([(2, 2), (3, 1), (8233, 1), (93811, 1), (8274073, 1), (277508030299, 1)] : List FactorBlock).map factorBlockValue).prod) = 21280803913850800815204508812 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eighteenP_2, prime_eighteenP_3, prime_eighteenP_8233, prime_eighteenP_93811, prime_eighteenP_8274073, prime_eighteenP_277508030299]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eighteenP_21280803913850800815204508813 : Nat.totient 21280803913850800815204508813 = 19643817194719524685178400000 := by
  rw [← show ((([(13, 1), (10897001, 1), (150223434544060480601, 1)] : List FactorBlock).map factorBlockValue).prod) = 21280803913850800815204508813 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eighteenP_13, prime_eighteenP_10897001, prime_eighteenP_150223434544060480601]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eighteenP_21280803913850800815204508814 : Nat.totient 21280803913850800815204508814 = 8983470229083015603078075264 := by
  rw [← show ((([(2, 1), (7, 1), (67, 1), (12583, 1), (277259, 1), (2674733, 1), (2431279603, 1)] : List FactorBlock).map factorBlockValue).prod) = 21280803913850800815204508814 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eighteenP_2, prime_eighteenP_7, prime_eighteenP_67, prime_eighteenP_12583, prime_eighteenP_277259, prime_eighteenP_2674733, prime_eighteenP_2431279603]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eighteenP_21280803913850800815204508815 : Nat.totient 21280803913850800815204508815 = 11338861159810098678655401984 := by
  rw [← show ((([(3, 1), (5, 1), (1049, 1), (139537, 1), (175593973, 1), (55197867029, 1)] : List FactorBlock).map factorBlockValue).prod) = 21280803913850800815204508815 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eighteenP_3, prime_eighteenP_5, prime_eighteenP_1049, prime_eighteenP_139537, prime_eighteenP_175593973, prime_eighteenP_55197867029]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eighteenP_21280803913850800815204508816 : Nat.totient 21280803913850800815204508816 = 10627854531086620139232936960 := by
  rw [← show ((([(2, 4), (919, 1), (11257, 1), (425291, 1), (302303849620517, 1)] : List FactorBlock).map factorBlockValue).prod) = 21280803913850800815204508816 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eighteenP_2, prime_eighteenP_919, prime_eighteenP_11257, prime_eighteenP_425291, prime_eighteenP_302303849620517]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eighteenP_21280803913850800815204508817 : Nat.totient 21280803913850800815204508817 = 20028971131152228806081004864 := by
  rw [← show ((([(17, 1), (963499, 1), (1299235385747572180099, 1)] : List FactorBlock).map factorBlockValue).prod) = 21280803913850800815204508817 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eighteenP_17, prime_eighteenP_963499, prime_eighteenP_1299235385747572180099]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eighteenP_21280803913850800815204508818 : Nat.totient 21280803913850800815204508818 = 7023328967119773837005857152 := by
  rw [← show ((([(2, 1), (3, 2), (103, 1), (5009, 1), (2291539082278737626663, 1)] : List FactorBlock).map factorBlockValue).prod) = 21280803913850800815204508818 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eighteenP_2, prime_eighteenP_3, prime_eighteenP_103, prime_eighteenP_5009, prime_eighteenP_2291539082278737626663]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eighteenP_21280803913850800815204508819 : Nat.totient 21280803913850800815204508819 = 20158418574190094865696057600 := by
  rw [← show ((([(19, 1), (8713, 1), (712477, 1), (23415331, 1), (7705406671, 1)] : List FactorBlock).map factorBlockValue).prod) = 21280803913850800815204508819 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eighteenP_19, prime_eighteenP_8713, prime_eighteenP_712477, prime_eighteenP_23415331, prime_eighteenP_7705406671]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eighteenP_21280803913850800815204508820 : Nat.totient 21280803913850800815204508820 = 8436431590339536703019335680 := by
  rw [← show ((([(2, 2), (5, 1), (139, 1), (577, 1), (2303321, 1), (5759873610810107, 1)] : List FactorBlock).map factorBlockValue).prod) = 21280803913850800815204508820 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eighteenP_2, prime_eighteenP_5, prime_eighteenP_139, prime_eighteenP_577, prime_eighteenP_2303321, prime_eighteenP_5759873610810107]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eighteenP_21280803913850800815204508821 : Nat.totient 21280803913850800815204508821 = 12122020211250044472243546240 := by
  rw [← show ((([(3, 1), (7, 1), (331, 1), (7129, 1), (429449525106920937499, 1)] : List FactorBlock).map factorBlockValue).prod) = 21280803913850800815204508821 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eighteenP_3, prime_eighteenP_7, prime_eighteenP_331, prime_eighteenP_7129, prime_eighteenP_429449525106920937499]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eighteenP_21280803913850800815204508822 : Nat.totient 21280803913850800815204508822 = 9608014555607977865373822720 := by
  rw [← show ((([(2, 1), (11, 1), (149, 1), (60793, 1), (106788750604720147493, 1)] : List FactorBlock).map factorBlockValue).prod) = 21280803913850800815204508822 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eighteenP_2, prime_eighteenP_11, prime_eighteenP_149, prime_eighteenP_60793, prime_eighteenP_106788750604720147493]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eighteenP_21280803913850800815204508823 : Nat.totient 21280803913850800815204508823 = 20355489529643999634723743704 := by
  rw [← show ((([(23, 1), (328103, 1), (2820005742344536930967, 1)] : List FactorBlock).map factorBlockValue).prod) = 21280803913850800815204508823 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eighteenP_23, prime_eighteenP_328103, prime_eighteenP_2820005742344536930967]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eighteenP_21280803913850800815204508824 : Nat.totient 21280803913850800815204508824 = 7080246641613070805070643200 := by
  rw [← show ((([(2, 3), (3, 1), (769, 1), (2143, 1), (8597, 1), (9792301, 1), (6391408799, 1)] : List FactorBlock).map factorBlockValue).prod) = 21280803913850800815204508824 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eighteenP_2, prime_eighteenP_3, prime_eighteenP_769, prime_eighteenP_2143, prime_eighteenP_8597, prime_eighteenP_9792301, prime_eighteenP_6391408799]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eighteenP_21280803913850800815204508825 : Nat.totient 21280803913850800815204508825 = 17023945999794817768552612800 := by
  rw [← show ((([(5, 2), (24421, 1), (34856564291144180525293, 1)] : List FactorBlock).map factorBlockValue).prod) = 21280803913850800815204508825 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eighteenP_5, prime_eighteenP_24421, prime_eighteenP_34856564291144180525293]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eighteenP_21280803913850800815204508826 : Nat.totient 21280803913850800815204508826 = 9821054601886138571278184448 := by
  rw [← show ((([(2, 1), (13, 1), (11489, 1), (71241401185919644928609, 1)] : List FactorBlock).map factorBlockValue).prod) = 21280803913850800815204508826 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eighteenP_2, prime_eighteenP_13, prime_eighteenP_11489, prime_eighteenP_71241401185919644928609]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eighteenP_21280803913850800815204508827 : Nat.totient 21280803913850800815204508827 = 14143947563348090209298304000 := by
  rw [← show ((([(3, 3), (421, 1), (1483, 1), (2072201, 1), (2567179, 1), (237308333, 1)] : List FactorBlock).map factorBlockValue).prod) = 21280803913850800815204508827 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eighteenP_3, prime_eighteenP_421, prime_eighteenP_1483, prime_eighteenP_2072201, prime_eighteenP_2567179, prime_eighteenP_237308333]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eighteenP_21280803913850800815204508828 : Nat.totient 21280803913850800815204508828 = 9087419101640678716281154560 := by
  rw [← show ((([(2, 2), (7, 1), (277, 1), (6810796141, 1), (402858330250993, 1)] : List FactorBlock).map factorBlockValue).prod) = 21280803913850800815204508828 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eighteenP_2, prime_eighteenP_7, prime_eighteenP_277, prime_eighteenP_6810796141, prime_eighteenP_402858330250993]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eighteenP_21280803913850800815204508829 : Nat.totient 21280803913850800815204508829 = 20543631600603312415975246080 := by
  rw [← show ((([(29, 1), (6131, 1), (126749873, 1), (944302595030827, 1)] : List FactorBlock).map factorBlockValue).prod) = 21280803913850800815204508829 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eighteenP_29, prime_eighteenP_6131, prime_eighteenP_126749873, prime_eighteenP_944302595030827]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eighteenP_21280803913850800815204508830 : Nat.totient 21280803913850800815204508830 = 5647033928394127664705157120 := by
  rw [← show ((([(2, 1), (3, 1), (5, 1), (281, 1), (739, 1), (3540386347, 1), (964862349257, 1)] : List FactorBlock).map factorBlockValue).prod) = 21280803913850800815204508830 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eighteenP_2, prime_eighteenP_3, prime_eighteenP_5, prime_eighteenP_281, prime_eighteenP_739, prime_eighteenP_3540386347, prime_eighteenP_964862349257]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eighteenP_21280803913850800815204508831 : Nat.totient 21280803913850800815204508831 = 20594326368242710466326944000 := by
  rw [← show ((([(31, 1), (686477545608090348877564801, 1)] : List FactorBlock).map factorBlockValue).prod) = 21280803913850800815204508831 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eighteenP_31, prime_eighteenP_686477545608090348877564801]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eighteenP_21280803913850800815204508832 : Nat.totient 21280803913850800815204508832 = 10639991330552752375962800640 := by
  rw [← show ((([(2, 5), (25913, 1), (1731666887, 1), (14820266192971, 1)] : List FactorBlock).map factorBlockValue).prod) = 21280803913850800815204508832 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eighteenP_2, prime_eighteenP_25913, prime_eighteenP_1731666887, prime_eighteenP_14820266192971]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eighteenP_21280803913850800815204508833 : Nat.totient 21280803913850800815204508833 = 12897259335595233175515382080 := by
  rw [← show ((([(3, 1), (11, 1), (97327, 1), (208223, 1), (4129087, 1), (7706514863, 1)] : List FactorBlock).map factorBlockValue).prod) = 21280803913850800815204508833 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eighteenP_3, prime_eighteenP_11, prime_eighteenP_97327, prime_eighteenP_208223, prime_eighteenP_4129087, prime_eighteenP_7706514863]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eighteenP_21280803913850800815204508834 : Nat.totient 21280803913850800815204508834 = 10014495959459200383625651200 := by
  rw [← show ((([(2, 1), (17, 1), (625905997466200023976603201, 1)] : List FactorBlock).map factorBlockValue).prod) = 21280803913850800815204508834 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eighteenP_2, prime_eighteenP_17, prime_eighteenP_625905997466200023976603201]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eighteenP_21280803913850800815204508835 : Nat.totient 21280803913850800815204508835 = 14592115565627431319693209728 := by
  rw [← show ((([(5, 1), (7, 1), (33493, 1), (18153732689432590021117, 1)] : List FactorBlock).map factorBlockValue).prod) = 21280803913850800815204508835 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eighteenP_5, prime_eighteenP_7, prime_eighteenP_33493, prime_eighteenP_18153732689432590021117]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eighteenP_21280803913850800815204508836 : Nat.totient 21280803913850800815204508836 = 7093601298814946944586473200 := by
  rw [← show ((([(2, 2), (3, 2), (1222615931, 1), (483498887150858771, 1)] : List FactorBlock).map factorBlockValue).prod) = 21280803913850800815204508836 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eighteenP_2, prime_eighteenP_3, prime_eighteenP_1222615931, prime_eighteenP_483498887150858771]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eighteenP_21280803913850800815204508837 : Nat.totient 21280803913850800815204508837 = 20704674860533659389257414656 := by
  rw [← show ((([(37, 1), (28463, 1), (100103, 1), (546353, 1), (369475127753, 1)] : List FactorBlock).map factorBlockValue).prod) = 21280803913850800815204508837 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eighteenP_37, prime_eighteenP_28463, prime_eighteenP_100103, prime_eighteenP_546353, prime_eighteenP_369475127753]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eighteenP_21280803913850800815204508838 : Nat.totient 21280803913850800815204508838 = 10077624661318833928783818240 := by
  rw [← show ((([(2, 1), (19, 1), (3691, 1), (401987, 1), (377440396466729153, 1)] : List FactorBlock).map factorBlockValue).prod) = 21280803913850800815204508838 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eighteenP_2, prime_eighteenP_19, prime_eighteenP_3691, prime_eighteenP_401987, prime_eighteenP_377440396466729153]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eighteenP_21280803913850800815204508839 : Nat.totient 21280803913850800815204508839 = 13095879331600492809356620800 := by
  rw [← show ((([(3, 1), (13, 1), (545661638816687200389859201, 1)] : List FactorBlock).map factorBlockValue).prod) = 21280803913850800815204508839 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eighteenP_3, prime_eighteenP_13, prime_eighteenP_545661638816687200389859201]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eighteenP_21280803913850800815204508840 : Nat.totient 21280803913850800815204508840 = 8394987328928202759971364864 := by
  rw [← show ((([(2, 3), (5, 1), (73, 1), (11953, 1), (339907, 1), (1793775758729587, 1)] : List FactorBlock).map factorBlockValue).prod) = 21280803913850800815204508840 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eighteenP_2, prime_eighteenP_5, prime_eighteenP_73, prime_eighteenP_11953, prime_eighteenP_339907, prime_eighteenP_1793775758729587]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eighteenP_21280803913850800815204508841 : Nat.totient 21280803913850800815204508841 = 20761202148982225333890347680 := by
  rw [← show ((([(41, 1), (37223, 1), (13944174244386535740887, 1)] : List FactorBlock).map factorBlockValue).prod) = 21280803913850800815204508841 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eighteenP_41, prime_eighteenP_37223, prime_eighteenP_13944174244386535740887]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eighteenP_21280803913850800815204508842 : Nat.totient 21280803913850800815204508842 = 6071866087062023771393572416 := by
  rw [← show ((([(2, 1), (3, 1), (7, 1), (727, 1), (40346827, 1), (17274080639688469, 1)] : List FactorBlock).map factorBlockValue).prod) = 21280803913850800815204508842 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eighteenP_2, prime_eighteenP_3, prime_eighteenP_7, prime_eighteenP_727, prime_eighteenP_40346827, prime_eighteenP_17274080639688469]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eighteenP_21280803913850800815204508843 : Nat.totient 21280803913850800815204508843 = 20694986779026058346958028800 := by
  rw [← show ((([(43, 1), (257, 1), (2801, 1), (7829, 1), (87814665071106317, 1)] : List FactorBlock).map factorBlockValue).prod) = 21280803913850800815204508843 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eighteenP_43, prime_eighteenP_257, prime_eighteenP_2801, prime_eighteenP_7829, prime_eighteenP_87814665071106317]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eighteenP_21280803913850800815204508844 : Nat.totient 21280803913850800815204508844 = 9665107213698457570461572160 := by
  rw [← show ((([(2, 2), (11, 1), (1277, 1), (23539, 1), (16090014941653837367, 1)] : List FactorBlock).map factorBlockValue).prod) = 21280803913850800815204508844 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eighteenP_2, prime_eighteenP_11, prime_eighteenP_1277, prime_eighteenP_23539, prime_eighteenP_16090014941653837367]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eighteenP_21280803913850800815204508845 : Nat.totient 21280803913850800815204508845 = 11299652204252097710385228672 := by
  rw [← show ((([(3, 2), (5, 1), (239, 1), (4327, 1), (1214459, 1), (376537177183483, 1)] : List FactorBlock).map factorBlockValue).prod) = 21280803913850800815204508845 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eighteenP_3, prime_eighteenP_5, prime_eighteenP_239, prime_eighteenP_4327, prime_eighteenP_1214459, prime_eighteenP_376537177183483]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eighteenP_21280803913850800815204508846 : Nat.totient 21280803913850800815204508846 = 10170500748584318455300803288 := by
  rw [← show ((([(2, 1), (23, 1), (1399, 1), (330683468220325089585799, 1)] : List FactorBlock).map factorBlockValue).prod) = 21280803913850800815204508846 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eighteenP_2, prime_eighteenP_23, prime_eighteenP_1399, prime_eighteenP_330683468220325089585799]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eighteenP_21280803913850800815204508847 : Nat.totient 21280803913850800815204508847 = 20707627667561662586892322560 := by
  rw [← show ((([(47, 1), (173, 1), (117242500777, 1), (22323330836381, 1)] : List FactorBlock).map factorBlockValue).prod) = 21280803913850800815204508847 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eighteenP_47, prime_eighteenP_173, prime_eighteenP_117242500777, prime_eighteenP_22323330836381]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eighteenP_21280803913850800815204508848 : Nat.totient 21280803913850800815204508848 = 7074401428646019176591278080 := by
  rw [← show ((([(2, 4), (3, 1), (373, 1), (55249, 1), (157429, 1), (773027, 1), (176780411, 1)] : List FactorBlock).map factorBlockValue).prod) = 21280803913850800815204508848 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eighteenP_2, prime_eighteenP_3, prime_eighteenP_373, prime_eighteenP_55249, prime_eighteenP_157429, prime_eighteenP_773027, prime_eighteenP_176780411]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eighteenP_21280803913850800815204508849 : Nat.totient 21280803913850800815204508849 = 18240689069014972127318150400 := by
  rw [← show ((([(7, 2), (434302120690832669698051201, 1)] : List FactorBlock).map factorBlockValue).prod) = 21280803913850800815204508849 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eighteenP_7, prime_eighteenP_434302120690832669698051201]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eighteenP_21280803913850800815204508850 : Nat.totient 21280803913850800815204508850 = 8512320851560884454764286080 := by
  rw [← show ((([(2, 1), (5, 2), (12759209, 1), (181957939, 1), (183325663427, 1)] : List FactorBlock).map factorBlockValue).prod) = 21280803913850800815204508850 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eighteenP_2, prime_eighteenP_5, prime_eighteenP_12759209, prime_eighteenP_181957939, prime_eighteenP_183325663427]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eighteenP_21280803913850800815204508851 : Nat.totient 21280803913850800815204508851 = 13194205958389474737301625856 := by
  rw [← show ((([(3, 1), (17, 1), (89, 1), (1567, 1), (2991981134619696139127, 1)] : List FactorBlock).map factorBlockValue).prod) = 21280803913850800815204508851 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eighteenP_3, prime_eighteenP_17, prime_eighteenP_89, prime_eighteenP_1567, prime_eighteenP_2991981134619696139127]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eighteenP_21280803913850800815204508852 : Nat.totient 21280803913850800815204508852 = 9804706615559969056831305600 := by
  rw [← show ((([(2, 2), (13, 1), (571, 1), (11213231, 1), (12829519, 1), (4982042579, 1)] : List FactorBlock).map factorBlockValue).prod) = 21280803913850800815204508852 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eighteenP_2, prime_eighteenP_13, prime_eighteenP_571, prime_eighteenP_11213231, prime_eighteenP_12829519, prime_eighteenP_4982042579]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eighteenP_21280803913850800815204508853 : Nat.totient 21280803913850800815204508853 = 20713583792357546988196915200 := by
  rw [← show ((([(53, 1), (241, 1), (263, 1), (816119807, 1), (7762211128921, 1)] : List FactorBlock).map factorBlockValue).prod) = 21280803913850800815204508853 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eighteenP_53, prime_eighteenP_241, prime_eighteenP_263, prime_eighteenP_816119807, prime_eighteenP_7762211128921]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eighteenP_21280803913850800815204508854 : Nat.totient 21280803913850800815204508854 = 7093601304616933605068169600 := by
  rw [← show ((([(2, 1), (3, 3), (394088961367607422503787201, 1)] : List FactorBlock).map factorBlockValue).prod) = 21280803913850800815204508854 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eighteenP_2, prime_eighteenP_3, prime_eighteenP_394088961367607422503787201]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eighteenP_21280803913850800815204508855 : Nat.totient 21280803913850800815204508855 = 15447097102166506790691454080 := by
  rw [← show ((([(5, 1), (11, 1), (523, 1), (59743, 1), (12383306569274786749, 1)] : List FactorBlock).map factorBlockValue).prod) = 21280803913850800815204508855 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eighteenP_5, prime_eighteenP_11, prime_eighteenP_523, prime_eighteenP_59743, prime_eighteenP_12383306569274786749]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eighteenP_21280803913850800815204508856 : Nat.totient 21280803913850800815204508856 = 9119904342194415573477408096 := by
  rw [← show ((([(2, 3), (7, 1), (20719, 1), (18341346377937090882079, 1)] : List FactorBlock).map factorBlockValue).prod) = 21280803913850800815204508856 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eighteenP_2, prime_eighteenP_7, prime_eighteenP_20719, prime_eighteenP_18341346377937090882079]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eighteenP_21280803913850800815204508857 : Nat.totient 21280803913850800815204508857 = 13440502779739994429621517312 := by
  rw [← show ((([(3, 1), (19, 1), (2712337, 1), (137647879701195599473, 1)] : List FactorBlock).map factorBlockValue).prod) = 21280803913850800815204508857 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eighteenP_3, prime_eighteenP_19, prime_eighteenP_2712337, prime_eighteenP_137647879701195599473]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eighteenP_21280803913850800815204508858 : Nat.totient 21280803913850800815204508858 = 10250084863337765202739765440 := by
  rw [← show ((([(2, 1), (29, 1), (439, 1), (2284423, 1), (63388891, 1), (5771727763, 1)] : List FactorBlock).map factorBlockValue).prod) = 21280803913850800815204508858 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eighteenP_2, prime_eighteenP_29, prime_eighteenP_439, prime_eighteenP_2284423, prime_eighteenP_63388891, prime_eighteenP_5771727763]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eighteenP_21280803913850800815204508859 : Nat.totient 21280803913850800815204508859 = 20920112322019889051492591976 := by
  rw [← show ((([(59, 1), (295851461047, 1), (1219164476942983, 1)] : List FactorBlock).map factorBlockValue).prod) = 21280803913850800815204508859 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eighteenP_59, prime_eighteenP_295851461047, prime_eighteenP_1219164476942983]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eighteenP_21280803913850800815204508860 : Nat.totient 21280803913850800815204508860 = 5674849609656314391671395072 := by
  rw [← show ((([(2, 2), (3, 1), (5, 1), (180533, 1), (1964627327030773765757, 1)] : List FactorBlock).map factorBlockValue).prod) = 21280803913850800815204508860 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eighteenP_2, prime_eighteenP_3, prime_eighteenP_5, prime_eighteenP_180533, prime_eighteenP_1964627327030773765757]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eighteenP_21280803913850800815204508861 : Nat.totient 21280803913850800815204508861 = 20931938269253252567454016320 := by
  rw [← show ((([(61, 1), (3140308397, 1), (111092795301652133, 1)] : List FactorBlock).map factorBlockValue).prod) = 21280803913850800815204508861 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eighteenP_61, prime_eighteenP_3140308397, prime_eighteenP_111092795301652133]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eighteenP_21280803913850800815204508862 : Nat.totient 21280803913850800815204508862 = 10154983338251816625983743200 := by
  rw [← show ((([(2, 1), (31, 1), (83, 1), (563, 1), (210739, 1), (34854988069713571, 1)] : List FactorBlock).map factorBlockValue).prod) = 21280803913850800815204508862 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eighteenP_2, prime_eighteenP_31, prime_eighteenP_83, prime_eighteenP_563, prime_eighteenP_210739, prime_eighteenP_34854988069713571]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eighteenP_21280803913850800815204508863 : Nat.totient 21280803913850800815204508863 = 12160334686097830677890050512 := by
  rw [← show ((([(3, 2), (7, 1), (97523, 1), (3463701263446490329787, 1)] : List FactorBlock).map factorBlockValue).prod) = 21280803913850800815204508863 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eighteenP_3, prime_eighteenP_7, prime_eighteenP_97523, prime_eighteenP_3463701263446490329787]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eighteenP_21280803913850800815204508864 : Nat.totient 21280803913850800815204508864 = 10620439044846699731317309440 := by
  rw [← show ((([(2, 6), (541, 1), (36017, 1), (4054368629, 1), (4209010627, 1)] : List FactorBlock).map factorBlockValue).prod) = 21280803913850800815204508864 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eighteenP_2, prime_eighteenP_541, prime_eighteenP_36017, prime_eighteenP_4054368629, prime_eighteenP_4209010627]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eighteenP_21280803913850800815204508865 : Nat.totient 21280803913850800815204508865 = 15570284045464447018713342720 := by
  rw [← show ((([(5, 1), (13, 1), (109, 1), (26111, 1), (115033589235656356379, 1)] : List FactorBlock).map factorBlockValue).prod) = 21280803913850800815204508865 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eighteenP_5, prime_eighteenP_13, prime_eighteenP_109, prime_eighteenP_26111, prime_eighteenP_115033589235656356379]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eighteenP_21280803913850800815204508866 : Nat.totient 21280803913850800815204508866 = 6447337744303139910336514560 := by
  rw [← show ((([(2, 1), (3, 1), (11, 1), (4637, 1), (2076644077, 1), (33484585780649, 1)] : List FactorBlock).map factorBlockValue).prod) = 21280803913850800815204508866 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eighteenP_2, prime_eighteenP_3, prime_eighteenP_11, prime_eighteenP_4637, prime_eighteenP_2076644077, prime_eighteenP_33484585780649]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eighteenP_21280803913850800815204508867 : Nat.totient 21280803913850800815204508867 = 21280803913850500867648176000 := by
  rw [← show ((([(115169608536001, 1), (184777947796867, 1)] : List FactorBlock).map factorBlockValue).prod) = 21280803913850800815204508867 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eighteenP_115169608536001, prime_eighteenP_184777947796867]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eighteenP_21280803913850800815204508868 : Nat.totient 21280803913850800815204508868 = 9872522310650787049213952000 := by
  rw [← show ((([(2, 2), (17, 1), (71, 1), (15401, 1), (34847, 1), (8213087550976673, 1)] : List FactorBlock).map factorBlockValue).prod) = 21280803913850800815204508868 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eighteenP_2, prime_eighteenP_17, prime_eighteenP_71, prime_eighteenP_15401, prime_eighteenP_34847, prime_eighteenP_8213087550976673]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eighteenP_21280803913850800815204508869 : Nat.totient 21280803913850800815204508869 = 13555731161927738170994095104 := by
  rw [← show ((([(3, 1), (23, 2), (953, 1), (34157, 1), (485319319, 1), (848810813, 1)] : List FactorBlock).map factorBlockValue).prod) = 21280803913850800815204508869 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eighteenP_3, prime_eighteenP_23, prime_eighteenP_953, prime_eighteenP_34157, prime_eighteenP_485319319, prime_eighteenP_848810813]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eighteenP_21280803913850800815204508870 : Nat.totient 21280803913850800815204508870 = 7252585354386791312897751648 := by
  rw [← show ((([(2, 1), (5, 1), (7, 1), (167, 1), (1820428050799897417896023, 1)] : List FactorBlock).map factorBlockValue).prod) = 21280803913850800815204508870 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eighteenP_2, prime_eighteenP_5, prime_eighteenP_7, prime_eighteenP_167, prime_eighteenP_1820428050799897417896023]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eighteenP_21280803913850800815204508871 : Nat.totient 21280803913850800815204508871 = 21280802124793690447670372352 := by
  rw [← show ((([(11894983, 1), (1789057110367522241537, 1)] : List FactorBlock).map factorBlockValue).prod) = 21280803913850800815204508871 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eighteenP_11894983, prime_eighteenP_1789057110367522241537]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eighteenP_21280803913850800815204508872 : Nat.totient 21280803913850800815204508872 = 7093600965708594895951147008 := by
  rw [← show ((([(2, 3), (3, 2), (20930737, 1), (14121180779525611873, 1)] : List FactorBlock).map factorBlockValue).prod) = 21280803913850800815204508872 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eighteenP_2, prime_eighteenP_3, prime_eighteenP_20930737, prime_eighteenP_14121180779525611873]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eighteenP_21280803913850800815204508873 : Nat.totient 21280803913850800815204508873 = 21280803913850800815204508872 := by
  rw [← show ((([(21280803913850800815204508873, 1)] : List FactorBlock).map factorBlockValue).prod) = 21280803913850800815204508873 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eighteenP_21280803913850800815204508873]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eighteenP_21280803913850800815204508874 : Nat.totient 21280803913850800815204508874 = 10352823525456369302110536144 := by
  rw [← show ((([(2, 1), (37, 1), (51564258659, 1), (5577088447446539, 1)] : List FactorBlock).map factorBlockValue).prod) = 21280803913850800815204508874 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eighteenP_2, prime_eighteenP_37, prime_eighteenP_51564258659, prime_eighteenP_5577088447446539]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eighteenP_21280803913850800815204508875 : Nat.totient 21280803913850800815204508875 = 11206071328011044211309024000 := by
  rw [← show ((([(3, 1), (5, 3), (79, 1), (489673, 1), (1466977702710658571, 1)] : List FactorBlock).map factorBlockValue).prod) = 21280803913850800815204508875 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eighteenP_3, prime_eighteenP_5, prime_eighteenP_79, prime_eighteenP_489673, prime_eighteenP_1466977702710658571]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eighteenP_21280803913850800815204508876 : Nat.totient 21280803913850800815204508876 = 9985065624116996917681234368 := by
  rw [← show ((([(2, 2), (19, 1), (107, 1), (9029, 1), (289835118837045663367, 1)] : List FactorBlock).map factorBlockValue).prod) = 21280803913850800815204508876 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eighteenP_2, prime_eighteenP_19, prime_eighteenP_107, prime_eighteenP_9029, prime_eighteenP_289835118837045663367]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eighteenP_21280803913850800815204508877 : Nat.totient 21280803913850800815204508877 = 16509394183994553289126524480 := by
  rw [← show ((([(7, 1), (11, 1), (227, 1), (2223590917, 1), (547540888461839, 1)] : List FactorBlock).map factorBlockValue).prod) = 21280803913850800815204508877 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eighteenP_7, prime_eighteenP_11, prime_eighteenP_227, prime_eighteenP_2223590917, prime_eighteenP_547540888461839]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eighteenP_21280803913850800815204508878 : Nat.totient 21280803913850800815204508878 = 6547939665800246404678310400 := by
  rw [← show ((([(2, 1), (3, 1), (13, 1), (272830819408343600194929601, 1)] : List FactorBlock).map factorBlockValue).prod) = 21280803913850800815204508878 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eighteenP_2, prime_eighteenP_3, prime_eighteenP_13, prime_eighteenP_272830819408343600194929601]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eighteenP_21280803913850800815204508879 : Nat.totient 21280803913850800815204508879 = 20930551910812626022090260000 := by
  rw [← show ((([(101, 1), (151, 1), (1509163, 1), (924599299072934783, 1)] : List FactorBlock).map factorBlockValue).prod) = 21280803913850800815204508879 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eighteenP_101, prime_eighteenP_151, prime_eighteenP_1509163, prime_eighteenP_924599299072934783]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eighteenP_21280803913850800815204508880 : Nat.totient 21280803913850800815204508880 = 8505225515732428345928908800 := by
  rw [← show ((([(2, 4), (5, 1), (2239, 1), (2609, 1), (276707, 1), (4175273, 1), (39415301, 1)] : List FactorBlock).map factorBlockValue).prod) = 21280803913850800815204508880 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eighteenP_2, prime_eighteenP_5, prime_eighteenP_2239, prime_eighteenP_2609, prime_eighteenP_276707, prime_eighteenP_4175273, prime_eighteenP_39415301]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eighteenP_21280803913850800815204508881 : Nat.totient 21280803913850800815204508881 = 13933843466823398037444940800 := by
  rw [← show ((([(3, 4), (67, 1), (491, 1), (1061, 1), (9492089, 1), (792993323477, 1)] : List FactorBlock).map factorBlockValue).prod) = 21280803913850800815204508881 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eighteenP_3, prime_eighteenP_67, prime_eighteenP_491, prime_eighteenP_1061, prime_eighteenP_9492089, prime_eighteenP_792993323477]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eighteenP_21280803913850800815204508882 : Nat.totient 21280803913850800815204508882 = 10380420891069443284477252480 := by
  rw [← show ((([(2, 1), (41, 1), (22613, 1), (11476672663927829564477, 1)] : List FactorBlock).map factorBlockValue).prod) = 21280803913850800815204508882 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eighteenP_2, prime_eighteenP_41, prime_eighteenP_22613, prime_eighteenP_11476672663927829564477]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eighteenP_21280803913850800815204508883 : Nat.totient 21280803913850800815204508883 = 21280799986357575604893129408 := by
  rw [← show ((([(5418419, 1), (3927493225210305961057, 1)] : List FactorBlock).map factorBlockValue).prod) = 21280803913850800815204508883 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eighteenP_5418419, prime_eighteenP_3927493225210305961057]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eighteenP_21280803913850800815204508884 : Nat.totient 21280803913850800815204508884 = 6080198556103818538901644800 := by
  rw [← show ((([(2, 2), (3, 1), (7, 1), (339389, 1), (545911, 1), (2940799, 1), (464968781, 1)] : List FactorBlock).map factorBlockValue).prod) = 21280803913850800815204508884 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eighteenP_2, prime_eighteenP_3, prime_eighteenP_7, prime_eighteenP_339389, prime_eighteenP_545911, prime_eighteenP_2940799, prime_eighteenP_464968781]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eighteenP_21280803913850800815204508885 : Nat.totient 21280803913850800815204508885 = 16023193535134720613801041920 := by
  rw [← show ((([(5, 1), (17, 1), (250362398986480009590641281, 1)] : List FactorBlock).map factorBlockValue).prod) = 21280803913850800815204508885 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eighteenP_5, prime_eighteenP_17, prime_eighteenP_250362398986480009590641281]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eighteenP_21280803913850800815204508886 : Nat.totient 21280803913850800815204508886 = 10317030441624254370494880576 := by
  rw [← show ((([(2, 1), (43, 1), (137, 1), (173827, 1), (10390866777165714899, 1)] : List FactorBlock).map factorBlockValue).prod) = 21280803913850800815204508886 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eighteenP_2, prime_eighteenP_43, prime_eighteenP_137, prime_eighteenP_173827, prime_eighteenP_10390866777165714899]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eighteenP_21280803913850800815204508887 : Nat.totient 21280803913850800815204508887 = 13593423926491837728657826560 := by
  rw [← show ((([(3, 1), (29, 1), (131, 1), (59553859433, 1), (31353611321587, 1)] : List FactorBlock).map factorBlockValue).prod) = 21280803913850800815204508887 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eighteenP_3, prime_eighteenP_29, prime_eighteenP_131, prime_eighteenP_59553859433, prime_eighteenP_31353611321587]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eighteenP_21280803913850800815204508888 : Nat.totient 21280803913850800815204508888 = 9672907869965226621366817920 := by
  rw [← show ((([(2, 3), (11, 1), (55807, 1), (842077, 1), (5145941864693659, 1)] : List FactorBlock).map factorBlockValue).prod) = 21280803913850800815204508888 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eighteenP_2, prime_eighteenP_11, prime_eighteenP_55807, prime_eighteenP_842077, prime_eighteenP_5145941864693659]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eighteenP_21280803913850800815204508889 : Nat.totient 21280803913850800815204508889 = 21280803913850800815204508888 := by
  rw [← show ((([(21280803913850800815204508889, 1)] : List FactorBlock).map factorBlockValue).prod) = 21280803913850800815204508889 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eighteenP_21280803913850800815204508889]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eighteenP_21280803913850800815204508890 : Nat.totient 21280803913850800815204508890 = 5674881034629409990943511648 := by
  rw [← show ((([(2, 1), (3, 2), (5, 1), (626080687, 1), (377672369920211983, 1)] : List FactorBlock).map factorBlockValue).prod) = 21280803913850800815204508890 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eighteenP_2, prime_eighteenP_3, prime_eighteenP_5, prime_eighteenP_626080687, prime_eighteenP_377672369920211983]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eighteenP_21280803913850800815204508891 : Nat.totient 21280803913850800815204508891 = 16816247168518313941411676160 := by
  rw [← show ((([(7, 1), (13, 1), (857, 1), (15493, 1), (29297, 1), (3196723, 1), (188062471, 1)] : List FactorBlock).map factorBlockValue).prod) = 21280803913850800815204508891 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eighteenP_7, prime_eighteenP_13, prime_eighteenP_857, prime_eighteenP_15493, prime_eighteenP_29297, prime_eighteenP_3196723, prime_eighteenP_188062471]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

theorem freeKill_64EighteenP : certifiedKill 1 21280803913850800815204508791 99 := by
  norm_num [certifiedKill, windowDiscrepancy, Finset.sum_range_succ,
    phi_eighteenP_21280803913850800815204508792, phi_eighteenP_21280803913850800815204508793, phi_eighteenP_21280803913850800815204508794,
    phi_eighteenP_21280803913850800815204508795, phi_eighteenP_21280803913850800815204508796, phi_eighteenP_21280803913850800815204508797,
    phi_eighteenP_21280803913850800815204508798, phi_eighteenP_21280803913850800815204508799, phi_eighteenP_21280803913850800815204508800,
    phi_eighteenP_21280803913850800815204508801, phi_eighteenP_21280803913850800815204508802, phi_eighteenP_21280803913850800815204508803,
    phi_eighteenP_21280803913850800815204508804, phi_eighteenP_21280803913850800815204508805, phi_eighteenP_21280803913850800815204508806,
    phi_eighteenP_21280803913850800815204508807, phi_eighteenP_21280803913850800815204508808, phi_eighteenP_21280803913850800815204508809,
    phi_eighteenP_21280803913850800815204508810, phi_eighteenP_21280803913850800815204508811, phi_eighteenP_21280803913850800815204508812,
    phi_eighteenP_21280803913850800815204508813, phi_eighteenP_21280803913850800815204508814, phi_eighteenP_21280803913850800815204508815,
    phi_eighteenP_21280803913850800815204508816, phi_eighteenP_21280803913850800815204508817, phi_eighteenP_21280803913850800815204508818,
    phi_eighteenP_21280803913850800815204508819, phi_eighteenP_21280803913850800815204508820, phi_eighteenP_21280803913850800815204508821,
    phi_eighteenP_21280803913850800815204508822, phi_eighteenP_21280803913850800815204508823, phi_eighteenP_21280803913850800815204508824,
    phi_eighteenP_21280803913850800815204508825, phi_eighteenP_21280803913850800815204508826, phi_eighteenP_21280803913850800815204508827,
    phi_eighteenP_21280803913850800815204508828, phi_eighteenP_21280803913850800815204508829, phi_eighteenP_21280803913850800815204508830,
    phi_eighteenP_21280803913850800815204508831, phi_eighteenP_21280803913850800815204508832, phi_eighteenP_21280803913850800815204508833,
    phi_eighteenP_21280803913850800815204508834, phi_eighteenP_21280803913850800815204508835, phi_eighteenP_21280803913850800815204508836,
    phi_eighteenP_21280803913850800815204508837, phi_eighteenP_21280803913850800815204508838, phi_eighteenP_21280803913850800815204508839,
    phi_eighteenP_21280803913850800815204508840, phi_eighteenP_21280803913850800815204508841, phi_eighteenP_21280803913850800815204508842,
    phi_eighteenP_21280803913850800815204508843, phi_eighteenP_21280803913850800815204508844, phi_eighteenP_21280803913850800815204508845,
    phi_eighteenP_21280803913850800815204508846, phi_eighteenP_21280803913850800815204508847, phi_eighteenP_21280803913850800815204508848,
    phi_eighteenP_21280803913850800815204508849, phi_eighteenP_21280803913850800815204508850, phi_eighteenP_21280803913850800815204508851,
    phi_eighteenP_21280803913850800815204508852, phi_eighteenP_21280803913850800815204508853, phi_eighteenP_21280803913850800815204508854,
    phi_eighteenP_21280803913850800815204508855, phi_eighteenP_21280803913850800815204508856, phi_eighteenP_21280803913850800815204508857,
    phi_eighteenP_21280803913850800815204508858, phi_eighteenP_21280803913850800815204508859, phi_eighteenP_21280803913850800815204508860,
    phi_eighteenP_21280803913850800815204508861, phi_eighteenP_21280803913850800815204508862, phi_eighteenP_21280803913850800815204508863,
    phi_eighteenP_21280803913850800815204508864, phi_eighteenP_21280803913850800815204508865, phi_eighteenP_21280803913850800815204508866,
    phi_eighteenP_21280803913850800815204508867, phi_eighteenP_21280803913850800815204508868, phi_eighteenP_21280803913850800815204508869,
    phi_eighteenP_21280803913850800815204508870, phi_eighteenP_21280803913850800815204508871, phi_eighteenP_21280803913850800815204508872,
    phi_eighteenP_21280803913850800815204508873, phi_eighteenP_21280803913850800815204508874, phi_eighteenP_21280803913850800815204508875,
    phi_eighteenP_21280803913850800815204508876, phi_eighteenP_21280803913850800815204508877, phi_eighteenP_21280803913850800815204508878,
    phi_eighteenP_21280803913850800815204508879, phi_eighteenP_21280803913850800815204508880, phi_eighteenP_21280803913850800815204508881,
    phi_eighteenP_21280803913850800815204508882, phi_eighteenP_21280803913850800815204508883, phi_eighteenP_21280803913850800815204508884,
    phi_eighteenP_21280803913850800815204508885, phi_eighteenP_21280803913850800815204508886, phi_eighteenP_21280803913850800815204508887,
    phi_eighteenP_21280803913850800815204508888, phi_eighteenP_21280803913850800815204508889, phi_eighteenP_21280803913850800815204508890,
    phi_eighteenP_21280803913850800815204508891]

end TotientTailPeriodKiller
end Erdos249257
