import Erdos249257.DiagonalPincerCertificatesT64

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

private def thirtySixAHFastPow {M : Type*} [Monoid M] (a : M) (n : ℕ) : M :=
  Nat.binaryRec 1 (fun b _ r => if b then r * r * a else r * r) n

private theorem thirtySixAHFastPow_eq_pow {M : Type*} [Monoid M] (a : M) (n : ℕ) :
    thirtySixAHFastPow a n = a ^ n := by
  induction n using Nat.binaryRec with
  | zero => simp [thirtySixAHFastPow, Nat.binaryRec_zero]
  | bit b n ih =>
      rw [thirtySixAHFastPow, Nat.binaryRec_eq b n (by left; simp)]
      change (if b then thirtySixAHFastPow a n * thirtySixAHFastPow a n * a
        else thirtySixAHFastPow a n * thirtySixAHFastPow a n) = _
      rw [ih]
      cases b <;> simp [Nat.bit, two_mul, pow_add]

private theorem prime_thirtySixAH_2 : Nat.Prime 2 := by norm_num
private theorem prime_thirtySixAH_3 : Nat.Prime 3 := by norm_num
private theorem prime_thirtySixAH_5 : Nat.Prime 5 := by norm_num
private theorem prime_thirtySixAH_7 : Nat.Prime 7 := by norm_num
private theorem prime_thirtySixAH_11 : Nat.Prime 11 := by norm_num
private theorem prime_thirtySixAH_13 : Nat.Prime 13 := by norm_num
private theorem prime_thirtySixAH_17 : Nat.Prime 17 := by norm_num
private theorem prime_thirtySixAH_19 : Nat.Prime 19 := by norm_num
private theorem prime_thirtySixAH_23 : Nat.Prime 23 := by norm_num
private theorem prime_thirtySixAH_29 : Nat.Prime 29 := by norm_num
private theorem prime_thirtySixAH_31 : Nat.Prime 31 := by norm_num
private theorem prime_thirtySixAH_37 : Nat.Prime 37 := by norm_num
private theorem prime_thirtySixAH_41 : Nat.Prime 41 := by norm_num
private theorem prime_thirtySixAH_43 : Nat.Prime 43 := by norm_num
private theorem prime_thirtySixAH_47 : Nat.Prime 47 := by norm_num
private theorem prime_thirtySixAH_53 : Nat.Prime 53 := by norm_num
private theorem prime_thirtySixAH_59 : Nat.Prime 59 := by norm_num
private theorem prime_thirtySixAH_61 : Nat.Prime 61 := by norm_num
private theorem prime_thirtySixAH_1151 : Nat.Prime 1151 := by norm_num
private theorem prime_thirtySixAH_31793 : Nat.Prime 31793 := by norm_num
private theorem prime_thirtySixAH_383 : Nat.Prime 383 := by norm_num
private theorem prime_thirtySixAH_739 : Nat.Prime 739 := by norm_num
private theorem prime_thirtySixAH_5419 : Nat.Prime 5419 := by norm_num
private theorem prime_thirtySixAH_109 : Nat.Prime 109 := by norm_num
private theorem prime_thirtySixAH_2671661 : Nat.Prime 2671661 := by norm_num
private theorem prime_thirtySixAH_126385595267 : Nat.Prime 126385595267 := by
  apply lucas_primality 126385595267 (2 : ZMod 126385595267)
  · rw [← thirtySixAHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (7, 1), (31, 1), (109, 1), (2671661, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (7, 1), (31, 1), (109, 1), (2671661, 1)] : List FactorBlock).map factorBlockValue).prod = 126385595267 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtySixAH_2
      · exact prime_thirtySixAH_7
      · exact prime_thirtySixAH_31
      · exact prime_thirtySixAH_109
      · exact prime_thirtySixAH_2671661
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 126385595267) ^ 63192797633 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (2 : ZMod 126385595267) ^ 18055085038 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (2 : ZMod 126385595267) ^ 4076954686 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (2 : ZMod 126385595267) ^ 1159500874 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (2 : ZMod 126385595267) ^ 47306 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide

private theorem prime_thirtySixAH_1163084296342727269807 : Nat.Prime 1163084296342727269807 := by
  apply lucas_primality 1163084296342727269807 (3 : ZMod 1163084296342727269807)
  · rw [← thirtySixAHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (383, 1), (739, 1), (5419, 1), (126385595267, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (383, 1), (739, 1), (5419, 1), (126385595267, 1)] : List FactorBlock).map factorBlockValue).prod = 1163084296342727269807 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtySixAH_2
      · exact prime_thirtySixAH_3
      · exact prime_thirtySixAH_383
      · exact prime_thirtySixAH_739
      · exact prime_thirtySixAH_5419
      · exact prime_thirtySixAH_126385595267
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1163084296342727269807) ^ 581542148171363634903 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (3 : ZMod 1163084296342727269807) ^ 387694765447575756602 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (3 : ZMod 1163084296342727269807) ^ 3036773619693804882 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (3 : ZMod 1163084296342727269807) ^ 1573862376647804154 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (3 : ZMod 1163084296342727269807) ^ 214630798365515274 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (3 : ZMod 1163084296342727269807) ^ 9202665018 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide

private theorem prime_thirtySixAH_26417 : Nat.Prime 26417 := by norm_num
private theorem prime_thirtySixAH_39157 : Nat.Prime 39157 := by norm_num
private theorem prime_thirtySixAH_137 : Nat.Prime 137 := by norm_num
private theorem prime_thirtySixAH_1693 : Nat.Prime 1693 := by norm_num
private theorem prime_thirtySixAH_67819 : Nat.Prime 67819 := by norm_num
private theorem prime_thirtySixAH_3593063 : Nat.Prime 3593063 := by norm_num
private theorem prime_thirtySixAH_20572881415656670829 : Nat.Prime 20572881415656670829 := by
  apply lucas_primality 20572881415656670829 (2 : ZMod 20572881415656670829)
  · rw [← thirtySixAHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (7, 1), (13, 1), (137, 1), (1693, 1), (67819, 1), (3593063, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (7, 1), (13, 1), (137, 1), (1693, 1), (67819, 1), (3593063, 1)] : List FactorBlock).map factorBlockValue).prod = 20572881415656670829 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtySixAH_2
      · exact prime_thirtySixAH_7
      · exact prime_thirtySixAH_13
      · exact prime_thirtySixAH_137
      · exact prime_thirtySixAH_1693
      · exact prime_thirtySixAH_67819
      · exact prime_thirtySixAH_3593063
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 20572881415656670829) ^ 10286440707828335414 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (2 : ZMod 20572881415656670829) ^ 2938983059379524404 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (2 : ZMod 20572881415656670829) ^ 1582529339665897756 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (2 : ZMod 20572881415656670829) ^ 150167017632530444 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (2 : ZMod 20572881415656670829) ^ 12151731491823196 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (2 : ZMod 20572881415656670829) ^ 303349819603012 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (2 : ZMod 20572881415656670829) ^ 5725722431156 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide

private theorem prime_thirtySixAH_181 : Nat.Prime 181 := by norm_num
private theorem prime_thirtySixAH_317 : Nat.Prime 317 := by norm_num
private theorem prime_thirtySixAH_372377 : Nat.Prime 372377 := by norm_num
private theorem prime_thirtySixAH_6305347 : Nat.Prime 6305347 := by norm_num
private theorem prime_thirtySixAH_441374291 : Nat.Prime 441374291 := by
  apply lucas_primality 441374291 (6 : ZMod 441374291)
  · rw [← thirtySixAHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 1), (7, 1), (6305347, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 1), (7, 1), (6305347, 1)] : List FactorBlock).map factorBlockValue).prod = 441374291 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtySixAH_2
      · exact prime_thirtySixAH_5
      · exact prime_thirtySixAH_7
      · exact prime_thirtySixAH_6305347
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 441374291) ^ 220687145 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (6 : ZMod 441374291) ^ 88274858 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (6 : ZMod 441374291) ^ 63053470 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (6 : ZMod 441374291) ^ 70 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide

private theorem prime_thirtySixAH_4491424785217 : Nat.Prime 4491424785217 := by
  apply lucas_primality 4491424785217 (7 : ZMod 4491424785217)
  · rw [← thirtySixAHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 6), (3, 1), (53, 1), (441374291, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 6), (3, 1), (53, 1), (441374291, 1)] : List FactorBlock).map factorBlockValue).prod = 4491424785217 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtySixAH_2
      · exact prime_thirtySixAH_3
      · exact prime_thirtySixAH_53
      · exact prime_thirtySixAH_441374291
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 4491424785217) ^ 2245712392608 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (7 : ZMod 4491424785217) ^ 1497141595072 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (7 : ZMod 4491424785217) ^ 84743863872 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (7 : ZMod 4491424785217) ^ 10176 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide

private theorem prime_thirtySixAH_702451380642795339781 : Nat.Prime 702451380642795339781 := by
  apply lucas_primality 702451380642795339781 (2 : ZMod 702451380642795339781)
  · rw [← thirtySixAHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (5, 1), (7, 1), (372377, 1), (4491424785217, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (5, 1), (7, 1), (372377, 1), (4491424785217, 1)] : List FactorBlock).map factorBlockValue).prod = 702451380642795339781 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtySixAH_2
      · exact prime_thirtySixAH_3
      · exact prime_thirtySixAH_5
      · exact prime_thirtySixAH_7
      · exact prime_thirtySixAH_372377
      · exact prime_thirtySixAH_4491424785217
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 702451380642795339781) ^ 351225690321397669890 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (2 : ZMod 702451380642795339781) ^ 234150460214265113260 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (2 : ZMod 702451380642795339781) ^ 140490276128559067956 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (2 : ZMod 702451380642795339781) ^ 100350197234685048540 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (2 : ZMod 702451380642795339781) ^ 1886398409791140 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (2 : ZMod 702451380642795339781) ^ 156398340 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide

private theorem prime_thirtySixAH_247262885986263959602913 : Nat.Prime 247262885986263959602913 := by
  apply lucas_primality 247262885986263959602913 (3 : ZMod 247262885986263959602913)
  · rw [← thirtySixAHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 5), (11, 1), (702451380642795339781, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 5), (11, 1), (702451380642795339781, 1)] : List FactorBlock).map factorBlockValue).prod = 247262885986263959602913 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtySixAH_2
      · exact prime_thirtySixAH_11
      · exact prime_thirtySixAH_702451380642795339781
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 247262885986263959602913) ^ 123631442993131979801456 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (3 : ZMod 247262885986263959602913) ^ 22478444180569450872992 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (3 : ZMod 247262885986263959602913) ^ 352 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide

private theorem prime_thirtySixAH_293 : Nat.Prime 293 := by norm_num
private theorem prime_thirtySixAH_97 : Nat.Prime 97 := by norm_num
private theorem prime_thirtySixAH_3616901 : Nat.Prime 3616901 := by norm_num
private theorem prime_thirtySixAH_5004841 : Nat.Prime 5004841 := by norm_num
private theorem prime_thirtySixAH_11968729 : Nat.Prime 11968729 := by norm_num
private theorem prime_thirtySixAH_287249497 : Nat.Prime 287249497 := by
  apply lucas_primality 287249497 (5 : ZMod 287249497)
  · rw [← thirtySixAHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (3, 1), (11968729, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (3, 1), (11968729, 1)] : List FactorBlock).map factorBlockValue).prod = 287249497 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtySixAH_2
      · exact prime_thirtySixAH_3
      · exact prime_thirtySixAH_11968729
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 287249497) ^ 143624748 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (5 : ZMod 287249497) ^ 95749832 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (5 : ZMod 287249497) ^ 24 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide

private theorem prime_thirtySixAH_93596301651291302272987 : Nat.Prime 93596301651291302272987 := by
  apply lucas_primality 93596301651291302272987 (2 : ZMod 93596301651291302272987)
  · rw [← thirtySixAHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 2), (3616901, 1), (5004841, 1), (287249497, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 2), (3616901, 1), (5004841, 1), (287249497, 1)] : List FactorBlock).map factorBlockValue).prod = 93596301651291302272987 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtySixAH_2
      · exact prime_thirtySixAH_3
      · exact prime_thirtySixAH_3616901
      · exact prime_thirtySixAH_5004841
      · exact prime_thirtySixAH_287249497
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 93596301651291302272987) ^ 46798150825645651136493 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (2 : ZMod 93596301651291302272987) ^ 31198767217097100757662 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (2 : ZMod 93596301651291302272987) ^ 25877485076669586 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (2 : ZMod 93596301651291302272987) ^ 18701153873078346 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (2 : ZMod 93596301651291302272987) ^ 325836259519338 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide

private theorem prime_thirtySixAH_36315365040701025281918957 : Nat.Prime 36315365040701025281918957 := by
  apply lucas_primality 36315365040701025281918957 (2 : ZMod 36315365040701025281918957)
  · rw [← thirtySixAHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (97, 1), (93596301651291302272987, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (97, 1), (93596301651291302272987, 1)] : List FactorBlock).map factorBlockValue).prod = 36315365040701025281918957 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtySixAH_2
      · exact prime_thirtySixAH_97
      · exact prime_thirtySixAH_93596301651291302272987
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 36315365040701025281918957) ^ 18157682520350512640959478 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (2 : ZMod 36315365040701025281918957) ^ 374385206605165209091948 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (2 : ZMod 36315365040701025281918957) ^ 388 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide

private theorem prime_thirtySixAH_41189 : Nat.Prime 41189 := by norm_num
private theorem prime_thirtySixAH_436531 : Nat.Prime 436531 := by norm_num
private theorem prime_thirtySixAH_14197 : Nat.Prime 14197 := by norm_num
private theorem prime_thirtySixAH_62268043 : Nat.Prime 62268043 := by
  apply lucas_primality 62268043 (2 : ZMod 62268043)
  · rw [← thirtySixAHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (17, 1), (43, 1), (14197, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (17, 1), (43, 1), (14197, 1)] : List FactorBlock).map factorBlockValue).prod = 62268043 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtySixAH_2
      · exact prime_thirtySixAH_3
      · exact prime_thirtySixAH_17
      · exact prime_thirtySixAH_43
      · exact prime_thirtySixAH_14197
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 62268043) ^ 31134021 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (2 : ZMod 62268043) ^ 20756014 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (2 : ZMod 62268043) ^ 3662826 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (2 : ZMod 62268043) ^ 1448094 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (2 : ZMod 62268043) ^ 4386 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide

private theorem prime_thirtySixAH_1783 : Nat.Prime 1783 := by norm_num
private theorem prime_thirtySixAH_271536637 : Nat.Prime 271536637 := by
  apply lucas_primality 271536637 (2 : ZMod 271536637)
  · rw [← thirtySixAHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (7, 3), (37, 1), (1783, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (7, 3), (37, 1), (1783, 1)] : List FactorBlock).map factorBlockValue).prod = 271536637 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtySixAH_2
      · exact prime_thirtySixAH_3
      · exact prime_thirtySixAH_7
      · exact prime_thirtySixAH_37
      · exact prime_thirtySixAH_1783
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 271536637) ^ 135768318 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (2 : ZMod 271536637) ^ 90512212 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (2 : ZMod 271536637) ^ 38790948 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (2 : ZMod 271536637) ^ 7338828 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (2 : ZMod 271536637) ^ 152292 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide

private theorem prime_thirtySixAH_206664924264738651729389 : Nat.Prime 206664924264738651729389 := by
  apply lucas_primality 206664924264738651729389 (2 : ZMod 206664924264738651729389)
  · rw [← thirtySixAHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (7, 1), (436531, 1), (62268043, 1), (271536637, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (7, 1), (436531, 1), (62268043, 1), (271536637, 1)] : List FactorBlock).map factorBlockValue).prod = 206664924264738651729389 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtySixAH_2
      · exact prime_thirtySixAH_7
      · exact prime_thirtySixAH_436531
      · exact prime_thirtySixAH_62268043
      · exact prime_thirtySixAH_271536637
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 206664924264738651729389) ^ 103332462132369325864694 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (2 : ZMod 206664924264738651729389) ^ 29523560609248378818484 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (2 : ZMod 206664924264738651729389) ^ 473425539686158948 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (2 : ZMod 206664924264738651729389) ^ 3318956471214916 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (2 : ZMod 206664924264738651729389) ^ 761094070207324 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide

private theorem prime_thirtySixAH_115903 : Nat.Prime 115903 := by norm_num
private theorem prime_thirtySixAH_131 : Nat.Prime 131 := by norm_num
private theorem prime_thirtySixAH_149 : Nat.Prime 149 := by norm_num
private theorem prime_thirtySixAH_9833 : Nat.Prime 9833 := by norm_num
private theorem prime_thirtySixAH_32244294937 : Nat.Prime 32244294937 := by
  apply lucas_primality 32244294937 (10 : ZMod 32244294937)
  · rw [← thirtySixAHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (3, 1), (7, 1), (131, 1), (149, 1), (9833, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (3, 1), (7, 1), (131, 1), (149, 1), (9833, 1)] : List FactorBlock).map factorBlockValue).prod = 32244294937 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtySixAH_2
      · exact prime_thirtySixAH_3
      · exact prime_thirtySixAH_7
      · exact prime_thirtySixAH_131
      · exact prime_thirtySixAH_149
      · exact prime_thirtySixAH_9833
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 32244294937) ^ 16122147468 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (10 : ZMod 32244294937) ^ 10748098312 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (10 : ZMod 32244294937) ^ 4606327848 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (10 : ZMod 32244294937) ^ 246139656 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (10 : ZMod 32244294937) ^ 216404664 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (10 : ZMod 32244294937) ^ 3279192 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide

private theorem prime_thirtySixAH_457 : Nat.Prime 457 := by norm_num
private theorem prime_thirtySixAH_1433 : Nat.Prime 1433 := by norm_num
private theorem prime_thirtySixAH_8783 : Nat.Prime 8783 := by norm_num
private theorem prime_thirtySixAH_1898100541591 : Nat.Prime 1898100541591 := by
  apply lucas_primality 1898100541591 (3 : ZMod 1898100541591)
  · rw [← thirtySixAHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (5, 1), (11, 1), (457, 1), (1433, 1), (8783, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (5, 1), (11, 1), (457, 1), (1433, 1), (8783, 1)] : List FactorBlock).map factorBlockValue).prod = 1898100541591 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtySixAH_2
      · exact prime_thirtySixAH_3
      · exact prime_thirtySixAH_5
      · exact prime_thirtySixAH_11
      · exact prime_thirtySixAH_457
      · exact prime_thirtySixAH_1433
      · exact prime_thirtySixAH_8783
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1898100541591) ^ 949050270795 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (3 : ZMod 1898100541591) ^ 632700180530 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (3 : ZMod 1898100541591) ^ 379620108318 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (3 : ZMod 1898100541591) ^ 172554594690 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (3 : ZMod 1898100541591) ^ 4153392870 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (3 : ZMod 1898100541591) ^ 1324564230 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (3 : ZMod 1898100541591) ^ 216110730 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide

private theorem prime_thirtySixAH_73 : Nat.Prime 73 := by norm_num
private theorem prime_thirtySixAH_151 : Nat.Prime 151 := by norm_num
private theorem prime_thirtySixAH_1851841 : Nat.Prime 1851841 := by norm_num
private theorem prime_thirtySixAH_641 : Nat.Prime 641 := by norm_num
private theorem prime_thirtySixAH_4019 : Nat.Prime 4019 := by norm_num
private theorem prime_thirtySixAH_9391 : Nat.Prime 9391 := by norm_num
private theorem prime_thirtySixAH_1451573819341 : Nat.Prime 1451573819341 := by
  apply lucas_primality 1451573819341 (6 : ZMod 1451573819341)
  · rw [← thirtySixAHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (5, 1), (641, 1), (4019, 1), (9391, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (5, 1), (641, 1), (4019, 1), (9391, 1)] : List FactorBlock).map factorBlockValue).prod = 1451573819341 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtySixAH_2
      · exact prime_thirtySixAH_3
      · exact prime_thirtySixAH_5
      · exact prime_thirtySixAH_641
      · exact prime_thirtySixAH_4019
      · exact prime_thirtySixAH_9391
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 1451573819341) ^ 725786909670 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (6 : ZMod 1451573819341) ^ 483857939780 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (6 : ZMod 1451573819341) ^ 290314763868 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (6 : ZMod 1451573819341) ^ 2264545740 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (6 : ZMod 1451573819341) ^ 361177860 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (6 : ZMod 1451573819341) ^ 154570740 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide

private theorem prime_thirtySixAH_496438246214623 : Nat.Prime 496438246214623 := by
  apply lucas_primality 496438246214623 (3 : ZMod 496438246214623)
  · rw [← thirtySixAHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 2), (19, 1), (1451573819341, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 2), (19, 1), (1451573819341, 1)] : List FactorBlock).map factorBlockValue).prod = 496438246214623 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtySixAH_2
      · exact prime_thirtySixAH_3
      · exact prime_thirtySixAH_19
      · exact prime_thirtySixAH_1451573819341
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 496438246214623) ^ 248219123107311 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (3 : ZMod 496438246214623) ^ 165479415404874 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (3 : ZMod 496438246214623) ^ 26128328748138 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (3 : ZMod 496438246214623) ^ 342 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide

private theorem prime_thirtySixAH_49643824621462301 : Nat.Prime 49643824621462301 := by
  apply lucas_primality 49643824621462301 (2 : ZMod 49643824621462301)
  · rw [← thirtySixAHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (5, 2), (496438246214623, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (5, 2), (496438246214623, 1)] : List FactorBlock).map factorBlockValue).prod = 49643824621462301 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtySixAH_2
      · exact prime_thirtySixAH_5
      · exact prime_thirtySixAH_496438246214623
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 49643824621462301) ^ 24821912310731150 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (2 : ZMod 49643824621462301) ^ 9928764924292460 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (2 : ZMod 49643824621462301) ^ 100 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide

private theorem prime_thirtySixAH_297862947728773807 : Nat.Prime 297862947728773807 := by
  apply lucas_primality 297862947728773807 (3 : ZMod 297862947728773807)
  · rw [← thirtySixAHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (49643824621462301, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (49643824621462301, 1)] : List FactorBlock).map factorBlockValue).prod = 297862947728773807 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtySixAH_2
      · exact prime_thirtySixAH_3
      · exact prime_thirtySixAH_49643824621462301
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 297862947728773807) ^ 148931473864386903 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (3 : ZMod 297862947728773807) ^ 99287649242924602 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (3 : ZMod 297862947728773807) ^ 6 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide

private theorem prime_thirtySixAH_2663 : Nat.Prime 2663 := by norm_num
private theorem prime_thirtySixAH_9063547 : Nat.Prime 9063547 := by norm_num
private theorem prime_thirtySixAH_211 : Nat.Prime 211 := by norm_num
private theorem prime_thirtySixAH_26126021 : Nat.Prime 26126021 := by
  apply lucas_primality 26126021 (3 : ZMod 26126021)
  · rw [← thirtySixAHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (5, 1), (41, 1), (151, 1), (211, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (5, 1), (41, 1), (151, 1), (211, 1)] : List FactorBlock).map factorBlockValue).prod = 26126021 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtySixAH_2
      · exact prime_thirtySixAH_5
      · exact prime_thirtySixAH_41
      · exact prime_thirtySixAH_151
      · exact prime_thirtySixAH_211
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 26126021) ^ 13063010 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (3 : ZMod 26126021) ^ 5225204 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (3 : ZMod 26126021) ^ 637220 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (3 : ZMod 26126021) ^ 173020 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (3 : ZMod 26126021) ^ 123820 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide

private theorem prime_thirtySixAH_397 : Nat.Prime 397 := by norm_num
private theorem prime_thirtySixAH_1213 : Nat.Prime 1213 := by norm_num
private theorem prime_thirtySixAH_8436948721 : Nat.Prime 8436948721 := by
  apply lucas_primality 8436948721 (7 : ZMod 8436948721)
  · rw [← thirtySixAHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 4), (3, 1), (5, 1), (73, 1), (397, 1), (1213, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 4), (3, 1), (5, 1), (73, 1), (397, 1), (1213, 1)] : List FactorBlock).map factorBlockValue).prod = 8436948721 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtySixAH_2
      · exact prime_thirtySixAH_3
      · exact prime_thirtySixAH_5
      · exact prime_thirtySixAH_73
      · exact prime_thirtySixAH_397
      · exact prime_thirtySixAH_1213
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 8436948721) ^ 4218474360 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (7 : ZMod 8436948721) ^ 2812316240 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (7 : ZMod 8436948721) ^ 1687389744 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (7 : ZMod 8436948721) ^ 115574640 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (7 : ZMod 8436948721) ^ 21251760 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (7 : ZMod 8436948721) ^ 6955440 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide

private theorem prime_thirtySixAH_401 : Nat.Prime 401 := by norm_num
private theorem prime_thirtySixAH_11069 : Nat.Prime 11069 := by norm_num
private theorem prime_thirtySixAH_53269 : Nat.Prime 53269 := by norm_num
private theorem prime_thirtySixAH_384973 : Nat.Prime 384973 := by norm_num
private theorem prime_thirtySixAH_1901 : Nat.Prime 1901 := by norm_num
private theorem prime_thirtySixAH_18979 : Nat.Prime 18979 := by norm_num
private theorem prime_thirtySixAH_72158159 : Nat.Prime 72158159 := by
  apply lucas_primality 72158159 (13 : ZMod 72158159)
  · rw [← thirtySixAHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (1901, 1), (18979, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (1901, 1), (18979, 1)] : List FactorBlock).map factorBlockValue).prod = 72158159 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtySixAH_2
      · exact prime_thirtySixAH_1901
      · exact prime_thirtySixAH_18979
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (13 : ZMod 72158159) ^ 36079079 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (13 : ZMod 72158159) ^ 37958 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (13 : ZMod 72158159) ^ 3802 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide

private theorem prime_thirtySixAH_20000838920189041 : Nat.Prime 20000838920189041 := by
  apply lucas_primality 20000838920189041 (7 : ZMod 20000838920189041)
  · rw [← thirtySixAHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 4), (3, 2), (5, 1), (384973, 1), (72158159, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 4), (3, 2), (5, 1), (384973, 1), (72158159, 1)] : List FactorBlock).map factorBlockValue).prod = 20000838920189041 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtySixAH_2
      · exact prime_thirtySixAH_3
      · exact prime_thirtySixAH_5
      · exact prime_thirtySixAH_384973
      · exact prime_thirtySixAH_72158159
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 20000838920189041) ^ 10000419460094520 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (7 : ZMod 20000838920189041) ^ 6666946306729680 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (7 : ZMod 20000838920189041) ^ 4000167784037808 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (7 : ZMod 20000838920189041) ^ 51953874480 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (7 : ZMod 20000838920189041) ^ 277180560 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide

private theorem prime_thirtySixAH_4256160782770160163040901761 : Nat.Prime 4256160782770160163040901761 := by
  apply lucas_primality 4256160782770160163040901761 (83 : ZMod 4256160782770160163040901761)
  · rw [← thirtySixAHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 7), (3, 5), (5, 1), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 7), (3, 5), (5, 1), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod = 4256160782770160163040901761 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtySixAH_2
      · exact prime_thirtySixAH_3
      · exact prime_thirtySixAH_5
      · exact prime_thirtySixAH_7
      · exact prime_thirtySixAH_11
      · exact prime_thirtySixAH_13
      · exact prime_thirtySixAH_17
      · exact prime_thirtySixAH_19
      · exact prime_thirtySixAH_23
      · exact prime_thirtySixAH_29
      · exact prime_thirtySixAH_31
      · exact prime_thirtySixAH_37
      · exact prime_thirtySixAH_41
      · exact prime_thirtySixAH_43
      · exact prime_thirtySixAH_47
      · exact prime_thirtySixAH_53
      · exact prime_thirtySixAH_59
      · exact prime_thirtySixAH_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (83 : ZMod 4256160782770160163040901761) ^ 2128080391385080081520450880 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (83 : ZMod 4256160782770160163040901761) ^ 1418720260923386721013633920 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (83 : ZMod 4256160782770160163040901761) ^ 851232156554032032608180352 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (83 : ZMod 4256160782770160163040901761) ^ 608022968967165737577271680 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (83 : ZMod 4256160782770160163040901761) ^ 386923707524560014821900160 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (83 : ZMod 4256160782770160163040901761) ^ 327396983290012320233915520 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (83 : ZMod 4256160782770160163040901761) ^ 250362398986480009590641280 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (83 : ZMod 4256160782770160163040901761) ^ 224008462251061061212679040 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (83 : ZMod 4256160782770160163040901761) ^ 185050468816093920132213120 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (83 : ZMod 4256160782770160163040901761) ^ 146764164923108971139341440 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (83 : ZMod 4256160782770160163040901761) ^ 137295509121618069775512960 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (83 : ZMod 4256160782770160163040901761) ^ 115031372507301626028132480 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (83 : ZMod 4256160782770160163040901761) ^ 103808799579760003976607360 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (83 : ZMod 4256160782770160163040901761) ^ 98980483320236282861416320 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (83 : ZMod 4256160782770160163040901761) ^ 90556612399365109851934080 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (83 : ZMod 4256160782770160163040901761) ^ 80304920429625663453601920 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (83 : ZMod 4256160782770160163040901761) ^ 72138318352036612932896640 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (83 : ZMod 4256160782770160163040901761) ^ 69773127586396068246572160 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide

private theorem prime_thirtySixAH_3869237075245600148219001601 : Nat.Prime 3869237075245600148219001601 := by
  apply lucas_primality 3869237075245600148219001601 (73 : ZMod 3869237075245600148219001601)
  · rw [← thirtySixAHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 8), (3, 5), (5, 2), (7, 2), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 8), (3, 5), (5, 2), (7, 2), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod = 3869237075245600148219001601 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtySixAH_2
      · exact prime_thirtySixAH_3
      · exact prime_thirtySixAH_5
      · exact prime_thirtySixAH_7
      · exact prime_thirtySixAH_13
      · exact prime_thirtySixAH_17
      · exact prime_thirtySixAH_19
      · exact prime_thirtySixAH_23
      · exact prime_thirtySixAH_29
      · exact prime_thirtySixAH_31
      · exact prime_thirtySixAH_37
      · exact prime_thirtySixAH_41
      · exact prime_thirtySixAH_43
      · exact prime_thirtySixAH_47
      · exact prime_thirtySixAH_53
      · exact prime_thirtySixAH_59
      · exact prime_thirtySixAH_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (73 : ZMod 3869237075245600148219001601) ^ 1934618537622800074109500800 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (73 : ZMod 3869237075245600148219001601) ^ 1289745691748533382739667200 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (73 : ZMod 3869237075245600148219001601) ^ 773847415049120029643800320 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (73 : ZMod 3869237075245600148219001601) ^ 552748153606514306888428800 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (73 : ZMod 3869237075245600148219001601) ^ 297633621172738472939923200 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (73 : ZMod 3869237075245600148219001601) ^ 227602180896800008718764800 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (73 : ZMod 3869237075245600148219001601) ^ 203644056591873692011526400 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (73 : ZMod 3869237075245600148219001601) ^ 168227698923721745574739200 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (73 : ZMod 3869237075245600148219001601) ^ 133421968111917246490310400 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (73 : ZMod 3869237075245600148219001601) ^ 124814099201470972523193600 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (73 : ZMod 3869237075245600148219001601) ^ 104573975006637841843756800 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (73 : ZMod 3869237075245600148219001601) ^ 94371635981600003615097600 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (73 : ZMod 3869237075245600148219001601) ^ 89982257563851166237651200 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (73 : ZMod 3869237075245600148219001601) ^ 82324193090331918047212800 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (73 : ZMod 3869237075245600148219001601) ^ 73004473117841512230547200 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (73 : ZMod 3869237075245600148219001601) ^ 65580289410942375393542400 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (73 : ZMod 3869237075245600148219001601) ^ 63430115987632789315065600 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide

private theorem prime_thirtySixAH_71 : Nat.Prime 71 := by norm_num
private theorem prime_thirtySixAH_114593 : Nat.Prime 114593 := by norm_num
private theorem prime_thirtySixAH_42857783 : Nat.Prime 42857783 := by
  apply lucas_primality 42857783 (5 : ZMod 42857783)
  · rw [← thirtySixAHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (11, 1), (17, 1), (114593, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (11, 1), (17, 1), (114593, 1)] : List FactorBlock).map factorBlockValue).prod = 42857783 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtySixAH_2
      · exact prime_thirtySixAH_11
      · exact prime_thirtySixAH_17
      · exact prime_thirtySixAH_114593
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 42857783) ^ 21428891 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (5 : ZMod 42857783) ^ 3896162 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (5 : ZMod 42857783) ^ 2521046 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (5 : ZMod 42857783) ^ 374 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide

private theorem prime_thirtySixAH_30429025931 : Nat.Prime 30429025931 := by
  apply lucas_primality 30429025931 (2 : ZMod 30429025931)
  · rw [← thirtySixAHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 1), (71, 1), (42857783, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 1), (71, 1), (42857783, 1)] : List FactorBlock).map factorBlockValue).prod = 30429025931 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtySixAH_2
      · exact prime_thirtySixAH_5
      · exact prime_thirtySixAH_71
      · exact prime_thirtySixAH_42857783
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 30429025931) ^ 15214512965 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (2 : ZMod 30429025931) ^ 6085805186 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (2 : ZMod 30429025931) ^ 428577830 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (2 : ZMod 30429025931) ^ 710 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide

private theorem prime_thirtySixAH_81047 : Nat.Prime 81047 := by norm_num
private theorem prime_thirtySixAH_14999741 : Nat.Prime 14999741 := by norm_num
private theorem prime_thirtySixAH_11655978276633277 : Nat.Prime 11655978276633277 := by
  apply lucas_primality 11655978276633277 (2 : ZMod 11655978276633277)
  · rw [← thirtySixAHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (17, 1), (47, 1), (81047, 1), (14999741, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (17, 1), (47, 1), (81047, 1), (14999741, 1)] : List FactorBlock).map factorBlockValue).prod = 11655978276633277 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtySixAH_2
      · exact prime_thirtySixAH_3
      · exact prime_thirtySixAH_17
      · exact prime_thirtySixAH_47
      · exact prime_thirtySixAH_81047
      · exact prime_thirtySixAH_14999741
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 11655978276633277) ^ 5827989138316638 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (2 : ZMod 11655978276633277) ^ 3885326092211092 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (2 : ZMod 11655978276633277) ^ 685645780978428 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (2 : ZMod 11655978276633277) ^ 247999537800708 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (2 : ZMod 11655978276633277) ^ 143817516708 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (2 : ZMod 11655978276633277) ^ 777078636 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide

private theorem prime_thirtySixAH_116559782766332771 : Nat.Prime 116559782766332771 := by
  apply lucas_primality 116559782766332771 (2 : ZMod 116559782766332771)
  · rw [← thirtySixAHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 1), (11655978276633277, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 1), (11655978276633277, 1)] : List FactorBlock).map factorBlockValue).prod = 116559782766332771 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtySixAH_2
      · exact prime_thirtySixAH_5
      · exact prime_thirtySixAH_11655978276633277
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 116559782766332771) ^ 58279891383166385 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (2 : ZMod 116559782766332771) ^ 23311956553266554 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (2 : ZMod 116559782766332771) ^ 10 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide

private theorem prime_thirtySixAH_89 : Nat.Prime 89 := by norm_num
private theorem prime_thirtySixAH_36637 : Nat.Prime 36637 := by norm_num
private theorem prime_thirtySixAH_57153721 : Nat.Prime 57153721 := by
  apply lucas_primality 57153721 (17 : ZMod 57153721)
  · rw [← thirtySixAHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (3, 1), (5, 1), (13, 1), (36637, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (3, 1), (5, 1), (13, 1), (36637, 1)] : List FactorBlock).map factorBlockValue).prod = 57153721 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtySixAH_2
      · exact prime_thirtySixAH_3
      · exact prime_thirtySixAH_5
      · exact prime_thirtySixAH_13
      · exact prime_thirtySixAH_36637
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (17 : ZMod 57153721) ^ 28576860 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (17 : ZMod 57153721) ^ 19051240 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (17 : ZMod 57153721) ^ 11430744 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (17 : ZMod 57153721) ^ 4396440 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (17 : ZMod 57153721) ^ 1560 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide

private theorem prime_thirtySixAH_2833 : Nat.Prime 2833 := by norm_num
private theorem prime_thirtySixAH_71663569 : Nat.Prime 71663569 := by
  apply lucas_primality 71663569 (11 : ZMod 71663569)
  · rw [← thirtySixAHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 4), (3, 1), (17, 1), (31, 1), (2833, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 4), (3, 1), (17, 1), (31, 1), (2833, 1)] : List FactorBlock).map factorBlockValue).prod = 71663569 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtySixAH_2
      · exact prime_thirtySixAH_3
      · exact prime_thirtySixAH_17
      · exact prime_thirtySixAH_31
      · exact prime_thirtySixAH_2833
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 71663569) ^ 35831784 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (11 : ZMod 71663569) ^ 23887856 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (11 : ZMod 71663569) ^ 4215504 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (11 : ZMod 71663569) ^ 2311728 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (11 : ZMod 71663569) ^ 25296 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide

private theorem prime_thirtySixAH_113 : Nat.Prime 113 := by norm_num
private theorem prime_thirtySixAH_827927 : Nat.Prime 827927 := by norm_num
private theorem prime_thirtySixAH_561334507 : Nat.Prime 561334507 := by
  apply lucas_primality 561334507 (2 : ZMod 561334507)
  · rw [← thirtySixAHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (113, 1), (827927, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (113, 1), (827927, 1)] : List FactorBlock).map factorBlockValue).prod = 561334507 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtySixAH_2
      · exact prime_thirtySixAH_3
      · exact prime_thirtySixAH_113
      · exact prime_thirtySixAH_827927
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 561334507) ^ 280667253 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (2 : ZMod 561334507) ^ 187111502 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (2 : ZMod 561334507) ^ 4967562 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (2 : ZMod 561334507) ^ 678 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide

private theorem prime_thirtySixAH_643635746791607729 : Nat.Prime 643635746791607729 := by
  apply lucas_primality 643635746791607729 (3 : ZMod 643635746791607729)
  · rw [← thirtySixAHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 4), (71663569, 1), (561334507, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 4), (71663569, 1), (561334507, 1)] : List FactorBlock).map factorBlockValue).prod = 643635746791607729 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtySixAH_2
      · exact prime_thirtySixAH_71663569
      · exact prime_thirtySixAH_561334507
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 643635746791607729) ^ 321817873395803864 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (3 : ZMod 643635746791607729) ^ 8981352112 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (3 : ZMod 643635746791607729) ^ 1146617104 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide

private theorem prime_thirtySixAH_4177 : Nat.Prime 4177 := by norm_num
private theorem prime_thirtySixAH_17047 : Nat.Prime 17047 := by norm_num
private theorem prime_thirtySixAH_2431189 : Nat.Prime 2431189 := by norm_num
private theorem prime_thirtySixAH_5024269 : Nat.Prime 5024269 := by norm_num
private theorem prime_thirtySixAH_87849902605848473 : Nat.Prime 87849902605848473 := by
  apply lucas_primality 87849902605848473 (3 : ZMod 87849902605848473)
  · rw [← thirtySixAHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (29, 1), (31, 1), (2431189, 1), (5024269, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (29, 1), (31, 1), (2431189, 1), (5024269, 1)] : List FactorBlock).map factorBlockValue).prod = 87849902605848473 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtySixAH_2
      · exact prime_thirtySixAH_29
      · exact prime_thirtySixAH_31
      · exact prime_thirtySixAH_2431189
      · exact prime_thirtySixAH_5024269
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 87849902605848473) ^ 43924951302924236 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (3 : ZMod 87849902605848473) ^ 3029306986408568 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (3 : ZMod 87849902605848473) ^ 2833867825995112 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (3 : ZMod 87849902605848473) ^ 36134542648 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (3 : ZMod 87849902605848473) ^ 17485111288 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide

private theorem prime_thirtySixAH_42695052666442357879 : Nat.Prime 42695052666442357879 := by
  apply lucas_primality 42695052666442357879 (3 : ZMod 42695052666442357879)
  · rw [← thirtySixAHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 5), (87849902605848473, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 5), (87849902605848473, 1)] : List FactorBlock).map factorBlockValue).prod = 42695052666442357879 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtySixAH_2
      · exact prime_thirtySixAH_3
      · exact prime_thirtySixAH_87849902605848473
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 42695052666442357879) ^ 21347526333221178939 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (3 : ZMod 42695052666442357879) ^ 14231684222147452626 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (3 : ZMod 42695052666442357879) ^ 486 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide

private theorem prime_thirtySixAH_277 : Nat.Prime 277 := by norm_num
private theorem prime_thirtySixAH_1965553 : Nat.Prime 1965553 := by norm_num
private theorem prime_thirtySixAH_66828803 : Nat.Prime 66828803 := by
  apply lucas_primality 66828803 (2 : ZMod 66828803)
  · rw [← thirtySixAHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (17, 1), (1965553, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (17, 1), (1965553, 1)] : List FactorBlock).map factorBlockValue).prod = 66828803 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtySixAH_2
      · exact prime_thirtySixAH_17
      · exact prime_thirtySixAH_1965553
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 66828803) ^ 33414401 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (2 : ZMod 66828803) ^ 3931106 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (2 : ZMod 66828803) ^ 34 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide

private theorem prime_thirtySixAH_111069470587 : Nat.Prime 111069470587 := by
  apply lucas_primality 111069470587 (11 : ZMod 111069470587)
  · rw [← thirtySixAHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (277, 1), (66828803, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (277, 1), (66828803, 1)] : List FactorBlock).map factorBlockValue).prod = 111069470587 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtySixAH_2
      · exact prime_thirtySixAH_3
      · exact prime_thirtySixAH_277
      · exact prime_thirtySixAH_66828803
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 111069470587) ^ 55534735293 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (11 : ZMod 111069470587) ^ 37023156862 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (11 : ZMod 111069470587) ^ 400972818 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (11 : ZMod 111069470587) ^ 1662 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide

private theorem prime_thirtySixAH_6442029294047 : Nat.Prime 6442029294047 := by
  apply lucas_primality 6442029294047 (5 : ZMod 6442029294047)
  · rw [← thirtySixAHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (29, 1), (111069470587, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (29, 1), (111069470587, 1)] : List FactorBlock).map factorBlockValue).prod = 6442029294047 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtySixAH_2
      · exact prime_thirtySixAH_29
      · exact prime_thirtySixAH_111069470587
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 6442029294047) ^ 3221014647023 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (5 : ZMod 6442029294047) ^ 222138941174 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (5 : ZMod 6442029294047) ^ 58 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide

private theorem prime_thirtySixAH_14081 : Nat.Prime 14081 := by norm_num
private theorem prime_thirtySixAH_4603 : Nat.Prime 4603 := by norm_num
private theorem prime_thirtySixAH_8369 : Nat.Prime 8369 := by norm_num
private theorem prime_thirtySixAH_539315099 : Nat.Prime 539315099 := by
  apply lucas_primality 539315099 (2 : ZMod 539315099)
  · rw [← thirtySixAHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (7, 1), (4603, 1), (8369, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (7, 1), (4603, 1), (8369, 1)] : List FactorBlock).map factorBlockValue).prod = 539315099 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtySixAH_2
      · exact prime_thirtySixAH_7
      · exact prime_thirtySixAH_4603
      · exact prime_thirtySixAH_8369
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 539315099) ^ 269657549 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (2 : ZMod 539315099) ^ 77045014 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (2 : ZMod 539315099) ^ 117166 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (2 : ZMod 539315099) ^ 64442 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide

private theorem prime_thirtySixAH_440457562723103 : Nat.Prime 440457562723103 := by
  apply lucas_primality 440457562723103 (5 : ZMod 440457562723103)
  · rw [← thirtySixAHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (29, 1), (14081, 1), (539315099, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (29, 1), (14081, 1), (539315099, 1)] : List FactorBlock).map factorBlockValue).prod = 440457562723103 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtySixAH_2
      · exact prime_thirtySixAH_29
      · exact prime_thirtySixAH_14081
      · exact prime_thirtySixAH_539315099
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 440457562723103) ^ 220228781361551 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (5 : ZMod 440457562723103) ^ 15188191818038 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (5 : ZMod 440457562723103) ^ 31280275742 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (5 : ZMod 440457562723103) ^ 816698 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide

private theorem prime_thirtySixAH_3137 : Nat.Prime 3137 := by norm_num
private theorem prime_thirtySixAH_19309 : Nat.Prime 19309 := by norm_num
private theorem prime_thirtySixAH_821 : Nat.Prime 821 := by norm_num
private theorem prime_thirtySixAH_223 : Nat.Prime 223 := by norm_num
private theorem prime_thirtySixAH_5437 : Nat.Prime 5437 := by norm_num
private theorem prime_thirtySixAH_14347 : Nat.Prime 14347 := by norm_num
private theorem prime_thirtySixAH_312018557 : Nat.Prime 312018557 := by
  apply lucas_primality 312018557 (2 : ZMod 312018557)
  · rw [← thirtySixAHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (5437, 1), (14347, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (5437, 1), (14347, 1)] : List FactorBlock).map factorBlockValue).prod = 312018557 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtySixAH_2
      · exact prime_thirtySixAH_5437
      · exact prime_thirtySixAH_14347
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 312018557) ^ 156009278 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (2 : ZMod 312018557) ^ 57388 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (2 : ZMod 312018557) ^ 21748 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide

private theorem prime_thirtySixAH_4368259799 : Nat.Prime 4368259799 := by
  apply lucas_primality 4368259799 (7 : ZMod 4368259799)
  · rw [← thirtySixAHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (7, 1), (312018557, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (7, 1), (312018557, 1)] : List FactorBlock).map factorBlockValue).prod = 4368259799 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtySixAH_2
      · exact prime_thirtySixAH_7
      · exact prime_thirtySixAH_312018557
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 4368259799) ^ 2184129899 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (7 : ZMod 4368259799) ^ 624037114 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (7 : ZMod 4368259799) ^ 14 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide

private theorem prime_thirtySixAH_52419117589 : Nat.Prime 52419117589 := by
  apply lucas_primality 52419117589 (2 : ZMod 52419117589)
  · rw [← thirtySixAHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (4368259799, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (4368259799, 1)] : List FactorBlock).map factorBlockValue).prod = 52419117589 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtySixAH_2
      · exact prime_thirtySixAH_3
      · exact prime_thirtySixAH_4368259799
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 52419117589) ^ 26209558794 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (2 : ZMod 52419117589) ^ 17473039196 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (2 : ZMod 52419117589) ^ 12 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide

private theorem prime_thirtySixAH_13372745926364969 : Nat.Prime 13372745926364969 := by
  apply lucas_primality 13372745926364969 (3 : ZMod 13372745926364969)
  · rw [← thirtySixAHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (11, 1), (13, 1), (223, 1), (52419117589, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (11, 1), (13, 1), (223, 1), (52419117589, 1)] : List FactorBlock).map factorBlockValue).prod = 13372745926364969 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtySixAH_2
      · exact prime_thirtySixAH_11
      · exact prime_thirtySixAH_13
      · exact prime_thirtySixAH_223
      · exact prime_thirtySixAH_52419117589
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 13372745926364969) ^ 6686372963182484 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (3 : ZMod 13372745926364969) ^ 1215704175124088 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (3 : ZMod 13372745926364969) ^ 1028672763566536 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (3 : ZMod 13372745926364969) ^ 59967470521816 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (3 : ZMod 13372745926364969) ^ 255112 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide

private theorem prime_thirtySixAH_43916097622182558197 : Nat.Prime 43916097622182558197 := by
  apply lucas_primality 43916097622182558197 (2 : ZMod 43916097622182558197)
  · rw [← thirtySixAHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (821, 1), (13372745926364969, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (821, 1), (13372745926364969, 1)] : List FactorBlock).map factorBlockValue).prod = 43916097622182558197 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtySixAH_2
      · exact prime_thirtySixAH_821
      · exact prime_thirtySixAH_13372745926364969
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 43916097622182558197) ^ 21958048811091279098 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (2 : ZMod 43916097622182558197) ^ 53490983705459876 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (2 : ZMod 43916097622182558197) ^ 3284 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide

private theorem prime_thirtySixAH_9473 : Nat.Prime 9473 := by norm_num
private theorem prime_thirtySixAH_8513 : Nat.Prime 8513 := by norm_num
private theorem prime_thirtySixAH_419449 : Nat.Prime 419449 := by norm_num
private theorem prime_thirtySixAH_5387402957 : Nat.Prime 5387402957 := by
  apply lucas_primality 5387402957 (3 : ZMod 5387402957)
  · rw [← thirtySixAHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (13, 2), (19, 1), (419449, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (13, 2), (19, 1), (419449, 1)] : List FactorBlock).map factorBlockValue).prod = 5387402957 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtySixAH_2
      · exact prime_thirtySixAH_13
      · exact prime_thirtySixAH_19
      · exact prime_thirtySixAH_419449
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 5387402957) ^ 2693701478 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (3 : ZMod 5387402957) ^ 414415612 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (3 : ZMod 5387402957) ^ 283547524 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (3 : ZMod 5387402957) ^ 12844 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide

private theorem prime_thirtySixAH_8447447836577 : Nat.Prime 8447447836577 := by
  apply lucas_primality 8447447836577 (3 : ZMod 8447447836577)
  · rw [← thirtySixAHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 5), (7, 2), (5387402957, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 5), (7, 2), (5387402957, 1)] : List FactorBlock).map factorBlockValue).prod = 8447447836577 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtySixAH_2
      · exact prime_thirtySixAH_7
      · exact prime_thirtySixAH_5387402957
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 8447447836577) ^ 4223723918288 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (3 : ZMod 8447447836577) ^ 1206778262368 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (3 : ZMod 8447447836577) ^ 1568 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide

private theorem prime_thirtySixAH_264290508800253361755137 : Nat.Prime 264290508800253361755137 := by
  apply lucas_primality 264290508800253361755137 (3 : ZMod 264290508800253361755137)
  · rw [← thirtySixAHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 10), (37, 1), (97, 1), (8513, 1), (8447447836577, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 10), (37, 1), (97, 1), (8513, 1), (8447447836577, 1)] : List FactorBlock).map factorBlockValue).prod = 264290508800253361755137 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtySixAH_2
      · exact prime_thirtySixAH_37
      · exact prime_thirtySixAH_97
      · exact prime_thirtySixAH_8513
      · exact prime_thirtySixAH_8447447836577
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 264290508800253361755137) ^ 132145254400126680877568 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (3 : ZMod 264290508800253361755137) ^ 7142986724331171939328 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (3 : ZMod 264290508800253361755137) ^ 2724644420621168677888 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (3 : ZMod 264290508800253361755137) ^ 31045519652326249472 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (3 : ZMod 264290508800253361755137) ^ 31286432768 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide

private theorem prime_thirtySixAH_210193 : Nat.Prime 210193 := by norm_num
private theorem prime_thirtySixAH_439 : Nat.Prime 439 := by norm_num
private theorem prime_thirtySixAH_853 : Nat.Prime 853 := by norm_num
private theorem prime_thirtySixAH_479 : Nat.Prime 479 := by norm_num
private theorem prime_thirtySixAH_6343 : Nat.Prime 6343 := by norm_num
private theorem prime_thirtySixAH_44960719007 : Nat.Prime 44960719007 := by
  apply lucas_primality 44960719007 (5 : ZMod 44960719007)
  · rw [← thirtySixAHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (7, 2), (151, 1), (479, 1), (6343, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (7, 2), (151, 1), (479, 1), (6343, 1)] : List FactorBlock).map factorBlockValue).prod = 44960719007 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtySixAH_2
      · exact prime_thirtySixAH_7
      · exact prime_thirtySixAH_151
      · exact prime_thirtySixAH_479
      · exact prime_thirtySixAH_6343
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 44960719007) ^ 22480359503 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (5 : ZMod 44960719007) ^ 6422959858 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (5 : ZMod 44960719007) ^ 297753106 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (5 : ZMod 44960719007) ^ 93863714 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (5 : ZMod 44960719007) ^ 7088242 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide

private theorem prime_thirtySixAH_1348821570211 : Nat.Prime 1348821570211 := by
  apply lucas_primality 1348821570211 (2 : ZMod 1348821570211)
  · rw [← thirtySixAHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (5, 1), (44960719007, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (5, 1), (44960719007, 1)] : List FactorBlock).map factorBlockValue).prod = 1348821570211 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtySixAH_2
      · exact prime_thirtySixAH_3
      · exact prime_thirtySixAH_5
      · exact prime_thirtySixAH_44960719007
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1348821570211) ^ 674410785105 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (2 : ZMod 1348821570211) ^ 449607190070 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (2 : ZMod 1348821570211) ^ 269764314042 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (2 : ZMod 1348821570211) ^ 30 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide

private theorem prime_thirtySixAH_8081426670915240593 : Nat.Prime 8081426670915240593 := by
  apply lucas_primality 8081426670915240593 (3 : ZMod 8081426670915240593)
  · rw [← thirtySixAHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 4), (439, 1), (853, 1), (1348821570211, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 4), (439, 1), (853, 1), (1348821570211, 1)] : List FactorBlock).map factorBlockValue).prod = 8081426670915240593 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtySixAH_2
      · exact prime_thirtySixAH_439
      · exact prime_thirtySixAH_853
      · exact prime_thirtySixAH_1348821570211
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 8081426670915240593) ^ 4040713335457620296 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (3 : ZMod 8081426670915240593) ^ 18408716790239728 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (3 : ZMod 8081426670915240593) ^ 9474122709162064 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (3 : ZMod 8081426670915240593) ^ 5991472 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide

private theorem prime_thirtySixAH_11249345925914014905457 : Nat.Prime 11249345925914014905457 := by
  apply lucas_primality 11249345925914014905457 (5 : ZMod 11249345925914014905457)
  · rw [← thirtySixAHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 4), (3, 1), (29, 1), (8081426670915240593, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 4), (3, 1), (29, 1), (8081426670915240593, 1)] : List FactorBlock).map factorBlockValue).prod = 11249345925914014905457 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtySixAH_2
      · exact prime_thirtySixAH_3
      · exact prime_thirtySixAH_29
      · exact prime_thirtySixAH_8081426670915240593
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 11249345925914014905457) ^ 5624672962957007452728 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (5 : ZMod 11249345925914014905457) ^ 3749781975304671635152 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (5 : ZMod 11249345925914014905457) ^ 387908480203931548464 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (5 : ZMod 11249345925914014905457) ^ 1392 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide

private theorem prime_thirtySixAH_194839 : Nat.Prime 194839 := by norm_num
private theorem prime_thirtySixAH_347 : Nat.Prime 347 := by norm_num
private theorem prime_thirtySixAH_3623 : Nat.Prime 3623 := by norm_num
private theorem prime_thirtySixAH_122963 : Nat.Prime 122963 := by norm_num
private theorem prime_thirtySixAH_977257 : Nat.Prime 977257 := by norm_num
private theorem prime_thirtySixAH_788877859963306117 : Nat.Prime 788877859963306117 := by
  apply lucas_primality 788877859963306117 (5 : ZMod 788877859963306117)
  · rw [← thirtySixAHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (151, 1), (3623, 1), (122963, 1), (977257, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (151, 1), (3623, 1), (122963, 1), (977257, 1)] : List FactorBlock).map factorBlockValue).prod = 788877859963306117 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtySixAH_2
      · exact prime_thirtySixAH_3
      · exact prime_thirtySixAH_151
      · exact prime_thirtySixAH_3623
      · exact prime_thirtySixAH_122963
      · exact prime_thirtySixAH_977257
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 788877859963306117) ^ 394438929981653058 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (5 : ZMod 788877859963306117) ^ 262959286654435372 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (5 : ZMod 788877859963306117) ^ 5224356688498716 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (5 : ZMod 788877859963306117) ^ 217741611913692 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (5 : ZMod 788877859963306117) ^ 6415571025132 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (5 : ZMod 788877859963306117) ^ 807236847588 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide

private theorem prime_thirtySixAH_11497105931105223349159 : Nat.Prime 11497105931105223349159 := by
  apply lucas_primality 11497105931105223349159 (3 : ZMod 11497105931105223349159)
  · rw [← thirtySixAHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (7, 1), (347, 1), (788877859963306117, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (7, 1), (347, 1), (788877859963306117, 1)] : List FactorBlock).map factorBlockValue).prod = 11497105931105223349159 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtySixAH_2
      · exact prime_thirtySixAH_3
      · exact prime_thirtySixAH_7
      · exact prime_thirtySixAH_347
      · exact prime_thirtySixAH_788877859963306117
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 11497105931105223349159) ^ 5748552965552611674579 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (3 : ZMod 11497105931105223349159) ^ 3832368643701741116386 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (3 : ZMod 11497105931105223349159) ^ 1642443704443603335594 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (3 : ZMod 11497105931105223349159) ^ 33132870118458856914 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (3 : ZMod 11497105931105223349159) ^ 14574 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide

private theorem prime_thirtySixAH_3181 : Nat.Prime 3181 := by norm_num
private theorem prime_thirtySixAH_73571 : Nat.Prime 73571 := by norm_num
private theorem prime_thirtySixAH_455881 : Nat.Prime 455881 := by norm_num
private theorem prime_thirtySixAH_7524701 : Nat.Prime 7524701 := by norm_num
private theorem prime_thirtySixAH_8487862729 : Nat.Prime 8487862729 := by
  apply lucas_primality 8487862729 (7 : ZMod 8487862729)
  · rw [← thirtySixAHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (3, 1), (47, 1), (7524701, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (3, 1), (47, 1), (7524701, 1)] : List FactorBlock).map factorBlockValue).prod = 8487862729 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtySixAH_2
      · exact prime_thirtySixAH_3
      · exact prime_thirtySixAH_47
      · exact prime_thirtySixAH_7524701
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 8487862729) ^ 4243931364 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (7 : ZMod 8487862729) ^ 2829287576 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (7 : ZMod 8487862729) ^ 180592824 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (7 : ZMod 8487862729) ^ 1128 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide

private theorem prime_thirtySixAH_19946477413151 : Nat.Prime 19946477413151 := by
  apply lucas_primality 19946477413151 (11 : ZMod 19946477413151)
  · rw [← thirtySixAHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 2), (47, 1), (8487862729, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 2), (47, 1), (8487862729, 1)] : List FactorBlock).map factorBlockValue).prod = 19946477413151 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtySixAH_2
      · exact prime_thirtySixAH_5
      · exact prime_thirtySixAH_47
      · exact prime_thirtySixAH_8487862729
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 19946477413151) ^ 9973238706575 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (11 : ZMod 19946477413151) ^ 3989295482630 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (11 : ZMod 19946477413151) ^ 424393136450 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (11 : ZMod 19946477413151) ^ 2350 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide

private theorem prime_thirtySixAH_8596663 : Nat.Prime 8596663 := by norm_num
private theorem prime_thirtySixAH_12269 : Nat.Prime 12269 := by norm_num
private theorem prime_thirtySixAH_20538307 : Nat.Prime 20538307 := by
  apply lucas_primality 20538307 (2 : ZMod 20538307)
  · rw [← thirtySixAHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 3), (31, 1), (12269, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 3), (31, 1), (12269, 1)] : List FactorBlock).map factorBlockValue).prod = 20538307 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtySixAH_2
      · exact prime_thirtySixAH_3
      · exact prime_thirtySixAH_31
      · exact prime_thirtySixAH_12269
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 20538307) ^ 10269153 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (2 : ZMod 20538307) ^ 6846102 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (2 : ZMod 20538307) ^ 662526 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (2 : ZMod 20538307) ^ 1674 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide

private theorem prime_thirtySixAH_409 : Nat.Prime 409 := by norm_num
private theorem prime_thirtySixAH_827 : Nat.Prime 827 := by norm_num
private theorem prime_thirtySixAH_219857951 : Nat.Prime 219857951 := by
  apply lucas_primality 219857951 (17 : ZMod 219857951)
  · rw [← thirtySixAHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 2), (13, 1), (409, 1), (827, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 2), (13, 1), (409, 1), (827, 1)] : List FactorBlock).map factorBlockValue).prod = 219857951 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtySixAH_2
      · exact prime_thirtySixAH_5
      · exact prime_thirtySixAH_13
      · exact prime_thirtySixAH_409
      · exact prime_thirtySixAH_827
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (17 : ZMod 219857951) ^ 109928975 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (17 : ZMod 219857951) ^ 43971590 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (17 : ZMod 219857951) ^ 16912150 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (17 : ZMod 219857951) ^ 537550 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (17 : ZMod 219857951) ^ 265850 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide

private theorem prime_thirtySixAH_150791 : Nat.Prime 150791 := by norm_num
private theorem prime_thirtySixAH_26171 : Nat.Prime 26171 := by norm_num
private theorem prime_thirtySixAH_2503121 : Nat.Prime 2503121 := by norm_num
private theorem prime_thirtySixAH_5760217 : Nat.Prime 5760217 := by norm_num
private theorem prime_thirtySixAH_576021701 : Nat.Prime 576021701 := by
  apply lucas_primality 576021701 (2 : ZMod 576021701)
  · rw [← thirtySixAHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (5, 2), (5760217, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (5, 2), (5760217, 1)] : List FactorBlock).map factorBlockValue).prod = 576021701 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtySixAH_2
      · exact prime_thirtySixAH_5
      · exact prime_thirtySixAH_5760217
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 576021701) ^ 288010850 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (2 : ZMod 576021701) ^ 115204340 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (2 : ZMod 576021701) ^ 100 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide

private theorem prime_thirtySixAH_75469418233448948783 : Nat.Prime 75469418233448948783 := by
  apply lucas_primality 75469418233448948783 (5 : ZMod 75469418233448948783)
  · rw [← thirtySixAHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (26171, 1), (2503121, 1), (576021701, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (26171, 1), (2503121, 1), (576021701, 1)] : List FactorBlock).map factorBlockValue).prod = 75469418233448948783 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtySixAH_2
      · exact prime_thirtySixAH_26171
      · exact prime_thirtySixAH_2503121
      · exact prime_thirtySixAH_576021701
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 75469418233448948783) ^ 37734709116724474391 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (5 : ZMod 75469418233448948783) ^ 2883704032457642 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (5 : ZMod 75469418233448948783) ^ 30150127873742 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (5 : ZMod 75469418233448948783) ^ 131018359382 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide

private theorem prime_thirtySixAH_12829801099686321293111 : Nat.Prime 12829801099686321293111 := by
  apply lucas_primality 12829801099686321293111 (14 : ZMod 12829801099686321293111)
  · rw [← thirtySixAHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 1), (17, 1), (75469418233448948783, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 1), (17, 1), (75469418233448948783, 1)] : List FactorBlock).map factorBlockValue).prod = 12829801099686321293111 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtySixAH_2
      · exact prime_thirtySixAH_5
      · exact prime_thirtySixAH_17
      · exact prime_thirtySixAH_75469418233448948783
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (14 : ZMod 12829801099686321293111) ^ 6414900549843160646555 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (14 : ZMod 12829801099686321293111) ^ 2565960219937264258622 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (14 : ZMod 12829801099686321293111) ^ 754694182334489487830 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (14 : ZMod 12829801099686321293111) ^ 170 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide

private theorem prime_thirtySixAH_208309 : Nat.Prime 208309 := by norm_num
private theorem prime_thirtySixAH_2639633 : Nat.Prime 2639633 := by norm_num
private theorem prime_thirtySixAH_17613571 : Nat.Prime 17613571 := by norm_num
private theorem prime_thirtySixAH_1327 : Nat.Prime 1327 := by norm_num
private theorem prime_thirtySixAH_71993 : Nat.Prime 71993 := by norm_num
private theorem prime_thirtySixAH_191069423 : Nat.Prime 191069423 := by
  apply lucas_primality 191069423 (5 : ZMod 191069423)
  · rw [← thirtySixAHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (1327, 1), (71993, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (1327, 1), (71993, 1)] : List FactorBlock).map factorBlockValue).prod = 191069423 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtySixAH_2
      · exact prime_thirtySixAH_1327
      · exact prime_thirtySixAH_71993
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 191069423) ^ 95534711 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (5 : ZMod 191069423) ^ 143986 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (5 : ZMod 191069423) ^ 2654 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide

private theorem prime_thirtySixAH_8233 : Nat.Prime 8233 := by norm_num
private theorem prime_thirtySixAH_93811 : Nat.Prime 93811 := by norm_num
private theorem prime_thirtySixAH_8274073 : Nat.Prime 8274073 := by norm_num
private theorem prime_thirtySixAH_1429 : Nat.Prime 1429 := by norm_num
private theorem prime_thirtySixAH_217223 : Nat.Prime 217223 := by norm_num
private theorem prime_thirtySixAH_277508030299 : Nat.Prime 277508030299 := by
  apply lucas_primality 277508030299 (3 : ZMod 277508030299)
  · rw [← thirtySixAHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (149, 1), (1429, 1), (217223, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (149, 1), (1429, 1), (217223, 1)] : List FactorBlock).map factorBlockValue).prod = 277508030299 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtySixAH_2
      · exact prime_thirtySixAH_3
      · exact prime_thirtySixAH_149
      · exact prime_thirtySixAH_1429
      · exact prime_thirtySixAH_217223
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 277508030299) ^ 138754015149 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (3 : ZMod 277508030299) ^ 92502676766 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (3 : ZMod 277508030299) ^ 1862470002 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (3 : ZMod 277508030299) ^ 194197362 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (3 : ZMod 277508030299) ^ 1277526 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide

private theorem prime_thirtySixAH_1297 : Nat.Prime 1297 := by norm_num
private theorem prime_thirtySixAH_1529089 : Nat.Prime 1529089 := by norm_num
private theorem prime_thirtySixAH_3167 : Nat.Prime 3167 := by norm_num
private theorem prime_thirtySixAH_1439549 : Nat.Prime 1439549 := by norm_num
private theorem prime_thirtySixAH_76920319995577 : Nat.Prime 76920319995577 := by
  apply lucas_primality 76920319995577 (5 : ZMod 76920319995577)
  · rw [← thirtySixAHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (3, 1), (19, 1), (37, 1), (3167, 1), (1439549, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (3, 1), (19, 1), (37, 1), (3167, 1), (1439549, 1)] : List FactorBlock).map factorBlockValue).prod = 76920319995577 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtySixAH_2
      · exact prime_thirtySixAH_3
      · exact prime_thirtySixAH_19
      · exact prime_thirtySixAH_37
      · exact prime_thirtySixAH_3167
      · exact prime_thirtySixAH_1439549
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 76920319995577) ^ 38460159997788 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (5 : ZMod 76920319995577) ^ 25640106665192 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (5 : ZMod 76920319995577) ^ 4048437894504 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (5 : ZMod 76920319995577) ^ 2078927567448 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (5 : ZMod 76920319995577) ^ 24288070728 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (5 : ZMod 76920319995577) ^ 53433624 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide

private theorem prime_thirtySixAH_42921538557531967 : Nat.Prime 42921538557531967 := by
  apply lucas_primality 42921538557531967 (3 : ZMod 42921538557531967)
  · rw [← thirtySixAHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 2), (31, 1), (76920319995577, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 2), (31, 1), (76920319995577, 1)] : List FactorBlock).map factorBlockValue).prod = 42921538557531967 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtySixAH_2
      · exact prime_thirtySixAH_3
      · exact prime_thirtySixAH_31
      · exact prime_thirtySixAH_76920319995577
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 42921538557531967) ^ 21460769278765983 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (3 : ZMod 42921538557531967) ^ 14307179519177322 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (3 : ZMod 42921538557531967) ^ 1384565759920386 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (3 : ZMod 42921538557531967) ^ 558 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide

private theorem prime_thirtySixAH_262523409885591991552253 : Nat.Prime 262523409885591991552253 := by
  apply lucas_primality 262523409885591991552253 (2 : ZMod 262523409885591991552253)
  · rw [← thirtySixAHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (1529089, 1), (42921538557531967, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (1529089, 1), (42921538557531967, 1)] : List FactorBlock).map factorBlockValue).prod = 262523409885591991552253 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtySixAH_2
      · exact prime_thirtySixAH_1529089
      · exact prime_thirtySixAH_42921538557531967
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 262523409885591991552253) ^ 131261704942795995776126 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (2 : ZMod 262523409885591991552253) ^ 171686154230127868 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (2 : ZMod 262523409885591991552253) ^ 6116356 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide

private theorem prime_thirtySixAH_10897001 : Nat.Prime 10897001 := by norm_num
private theorem prime_thirtySixAH_421 : Nat.Prime 421 := by norm_num
private theorem prime_thirtySixAH_127 : Nat.Prime 127 := by norm_num
private theorem prime_thirtySixAH_14143 : Nat.Prime 14143 := by norm_num
private theorem prime_thirtySixAH_76679 : Nat.Prime 76679 := by norm_num
private theorem prime_thirtySixAH_104948605941079 : Nat.Prime 104948605941079 := by
  apply lucas_primality 104948605941079 (3 : ZMod 104948605941079)
  · rw [← thirtySixAHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (127, 2), (14143, 1), (76679, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (127, 2), (14143, 1), (76679, 1)] : List FactorBlock).map factorBlockValue).prod = 104948605941079 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtySixAH_2
      · exact prime_thirtySixAH_3
      · exact prime_thirtySixAH_127
      · exact prime_thirtySixAH_14143
      · exact prime_thirtySixAH_76679
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 104948605941079) ^ 52474302970539 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (3 : ZMod 104948605941079) ^ 34982868647026 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (3 : ZMod 104948605941079) ^ 826366975914 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (3 : ZMod 104948605941079) ^ 7420533546 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (3 : ZMod 104948605941079) ^ 1368674682 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide

private theorem prime_thirtySixAH_150223434544060480601 : Nat.Prime 150223434544060480601 := by
  apply lucas_primality 150223434544060480601 (3 : ZMod 150223434544060480601)
  · rw [← thirtySixAHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (5, 2), (17, 1), (421, 1), (104948605941079, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (5, 2), (17, 1), (421, 1), (104948605941079, 1)] : List FactorBlock).map factorBlockValue).prod = 150223434544060480601 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtySixAH_2
      · exact prime_thirtySixAH_5
      · exact prime_thirtySixAH_17
      · exact prime_thirtySixAH_421
      · exact prime_thirtySixAH_104948605941079
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 150223434544060480601) ^ 75111717272030240300 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (3 : ZMod 150223434544060480601) ^ 30044686908812096120 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (3 : ZMod 150223434544060480601) ^ 8836672620238851800 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (3 : ZMod 150223434544060480601) ^ 356825260199668600 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (3 : ZMod 150223434544060480601) ^ 1431400 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide

private theorem prime_thirtySixAH_1576355845470429690015148801 : Nat.Prime 1576355845470429690015148801 := by
  apply lucas_primality 1576355845470429690015148801 (101 : ZMod 1576355845470429690015148801)
  · rw [← thirtySixAHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 8), (3, 2), (5, 2), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 8), (3, 2), (5, 2), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod = 1576355845470429690015148801 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtySixAH_2
      · exact prime_thirtySixAH_3
      · exact prime_thirtySixAH_5
      · exact prime_thirtySixAH_7
      · exact prime_thirtySixAH_11
      · exact prime_thirtySixAH_13
      · exact prime_thirtySixAH_17
      · exact prime_thirtySixAH_19
      · exact prime_thirtySixAH_23
      · exact prime_thirtySixAH_29
      · exact prime_thirtySixAH_31
      · exact prime_thirtySixAH_37
      · exact prime_thirtySixAH_41
      · exact prime_thirtySixAH_43
      · exact prime_thirtySixAH_47
      · exact prime_thirtySixAH_53
      · exact prime_thirtySixAH_59
      · exact prime_thirtySixAH_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (101 : ZMod 1576355845470429690015148801) ^ 788177922735214845007574400 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (101 : ZMod 1576355845470429690015148801) ^ 525451948490143230005049600 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (101 : ZMod 1576355845470429690015148801) ^ 315271169094085938003029760 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (101 : ZMod 1576355845470429690015148801) ^ 225193692210061384287878400 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (101 : ZMod 1576355845470429690015148801) ^ 143305076860948153637740800 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (101 : ZMod 1576355845470429690015148801) ^ 121258141959263822308857600 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (101 : ZMod 1576355845470429690015148801) ^ 92726814439437040589126400 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (101 : ZMod 1576355845470429690015148801) ^ 82966097130022615263955200 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (101 : ZMod 1576355845470429690015148801) ^ 68537210672627377826745600 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (101 : ZMod 1576355845470429690015148801) ^ 54357098119669989310867200 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (101 : ZMod 1576355845470429690015148801) ^ 50850188563562248065004800 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (101 : ZMod 1576355845470429690015148801) ^ 42604212039741342973382400 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (101 : ZMod 1576355845470429690015148801) ^ 38447703548059260732076800 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (101 : ZMod 1576355845470429690015148801) ^ 36659438266754178837561600 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (101 : ZMod 1576355845470429690015148801) ^ 33539486073838929574790400 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (101 : ZMod 1576355845470429690015148801) ^ 29742563122083579056889600 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (101 : ZMod 1576355845470429690015148801) ^ 26717895685939486271443200 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (101 : ZMod 1576355845470429690015148801) ^ 25841899106072617869100800 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide

private theorem prime_thirtySixAH_67 : Nat.Prime 67 := by norm_num
private theorem prime_thirtySixAH_12583 : Nat.Prime 12583 := by norm_num
private theorem prime_thirtySixAH_277259 : Nat.Prime 277259 := by norm_num
private theorem prime_thirtySixAH_2674733 : Nat.Prime 2674733 := by norm_num
private theorem prime_thirtySixAH_239 : Nat.Prime 239 := by norm_num
private theorem prime_thirtySixAH_283 : Nat.Prime 283 := by norm_num
private theorem prime_thirtySixAH_1997 : Nat.Prime 1997 := by norm_num
private theorem prime_thirtySixAH_2431279603 : Nat.Prime 2431279603 := by
  apply lucas_primality 2431279603 (2 : ZMod 2431279603)
  · rw [← thirtySixAHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 2), (239, 1), (283, 1), (1997, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 2), (239, 1), (283, 1), (1997, 1)] : List FactorBlock).map factorBlockValue).prod = 2431279603 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtySixAH_2
      · exact prime_thirtySixAH_3
      · exact prime_thirtySixAH_239
      · exact prime_thirtySixAH_283
      · exact prime_thirtySixAH_1997
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 2431279603) ^ 1215639801 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (2 : ZMod 2431279603) ^ 810426534 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (2 : ZMod 2431279603) ^ 10172718 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (2 : ZMod 2431279603) ^ 8591094 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (2 : ZMod 2431279603) ^ 1217466 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide

private theorem prime_thirtySixAH_9185291 : Nat.Prime 9185291 := by norm_num
private theorem prime_thirtySixAH_229 : Nat.Prime 229 := by norm_num
private theorem prime_thirtySixAH_90523 : Nat.Prime 90523 := by norm_num
private theorem prime_thirtySixAH_463 : Nat.Prime 463 := by norm_num
private theorem prime_thirtySixAH_315636361 : Nat.Prime 315636361 := by
  apply lucas_primality 315636361 (7 : ZMod 315636361)
  · rw [← thirtySixAHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (3, 1), (5, 1), (13, 1), (19, 1), (23, 1), (463, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (3, 1), (5, 1), (13, 1), (19, 1), (23, 1), (463, 1)] : List FactorBlock).map factorBlockValue).prod = 315636361 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtySixAH_2
      · exact prime_thirtySixAH_3
      · exact prime_thirtySixAH_5
      · exact prime_thirtySixAH_13
      · exact prime_thirtySixAH_19
      · exact prime_thirtySixAH_23
      · exact prime_thirtySixAH_463
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 315636361) ^ 157818180 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (7 : ZMod 315636361) ^ 105212120 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (7 : ZMod 315636361) ^ 63127272 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (7 : ZMod 315636361) ^ 24279720 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (7 : ZMod 315636361) ^ 16612440 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (7 : ZMod 315636361) ^ 13723320 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (7 : ZMod 315636361) ^ 681720 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide

private theorem prime_thirtySixAH_770783993563 : Nat.Prime 770783993563 := by
  apply lucas_primality 770783993563 (11 : ZMod 770783993563)
  · rw [← thirtySixAHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (11, 1), (37, 1), (315636361, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (11, 1), (37, 1), (315636361, 1)] : List FactorBlock).map factorBlockValue).prod = 770783993563 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtySixAH_2
      · exact prime_thirtySixAH_3
      · exact prime_thirtySixAH_11
      · exact prime_thirtySixAH_37
      · exact prime_thirtySixAH_315636361
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 770783993563) ^ 385391996781 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (11 : ZMod 770783993563) ^ 256927997854 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (11 : ZMod 770783993563) ^ 70071272142 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (11 : ZMod 770783993563) ^ 20831999826 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (11 : ZMod 770783993563) ^ 2442 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide

private theorem prime_thirtySixAH_159781725938904898211 : Nat.Prime 159781725938904898211 := by
  apply lucas_primality 159781725938904898211 (6 : ZMod 159781725938904898211)
  · rw [← thirtySixAHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 1), (229, 1), (90523, 1), (770783993563, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 1), (229, 1), (90523, 1), (770783993563, 1)] : List FactorBlock).map factorBlockValue).prod = 159781725938904898211 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtySixAH_2
      · exact prime_thirtySixAH_5
      · exact prime_thirtySixAH_229
      · exact prime_thirtySixAH_90523
      · exact prime_thirtySixAH_770783993563
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 159781725938904898211) ^ 79890862969452449105 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (6 : ZMod 159781725938904898211) ^ 31956345187780979642 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (6 : ZMod 159781725938904898211) ^ 697736794493034490 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (6 : ZMod 159781725938904898211) ^ 1765095345259270 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (6 : ZMod 159781725938904898211) ^ 207297670 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide

private theorem prime_thirtySixAH_1049 : Nat.Prime 1049 := by norm_num
private theorem prime_thirtySixAH_139537 : Nat.Prime 139537 := by norm_num
private theorem prime_thirtySixAH_5879 : Nat.Prime 5879 := by norm_num
private theorem prime_thirtySixAH_175593973 : Nat.Prime 175593973 := by
  apply lucas_primality 175593973 (5 : ZMod 175593973)
  · rw [← thirtySixAHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (19, 1), (131, 1), (5879, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (19, 1), (131, 1), (5879, 1)] : List FactorBlock).map factorBlockValue).prod = 175593973 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtySixAH_2
      · exact prime_thirtySixAH_3
      · exact prime_thirtySixAH_19
      · exact prime_thirtySixAH_131
      · exact prime_thirtySixAH_5879
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 175593973) ^ 87796986 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (5 : ZMod 175593973) ^ 58531324 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (5 : ZMod 175593973) ^ 9241788 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (5 : ZMod 175593973) ^ 1340412 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (5 : ZMod 175593973) ^ 29868 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide

private theorem prime_thirtySixAH_372958561 : Nat.Prime 372958561 := by
  apply lucas_primality 372958561 (11 : ZMod 372958561)
  · rw [← thirtySixAHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 5), (3, 3), (5, 1), (13, 1), (29, 1), (229, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 5), (3, 3), (5, 1), (13, 1), (29, 1), (229, 1)] : List FactorBlock).map factorBlockValue).prod = 372958561 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtySixAH_2
      · exact prime_thirtySixAH_3
      · exact prime_thirtySixAH_5
      · exact prime_thirtySixAH_13
      · exact prime_thirtySixAH_29
      · exact prime_thirtySixAH_229
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 372958561) ^ 186479280 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (11 : ZMod 372958561) ^ 124319520 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (11 : ZMod 372958561) ^ 74591712 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (11 : ZMod 372958561) ^ 28689120 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (11 : ZMod 372958561) ^ 12860640 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (11 : ZMod 372958561) ^ 1628640 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide

private theorem prime_thirtySixAH_55197867029 : Nat.Prime 55197867029 := by
  apply lucas_primality 55197867029 (2 : ZMod 55197867029)
  · rw [← thirtySixAHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (37, 1), (372958561, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (37, 1), (372958561, 1)] : List FactorBlock).map factorBlockValue).prod = 55197867029 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtySixAH_2
      · exact prime_thirtySixAH_37
      · exact prime_thirtySixAH_372958561
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 55197867029) ^ 27598933514 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (2 : ZMod 55197867029) ^ 1491834244 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (2 : ZMod 55197867029) ^ 148 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide

private theorem prime_thirtySixAH_163 : Nat.Prime 163 := by norm_num
private theorem prime_thirtySixAH_389 : Nat.Prime 389 := by norm_num
private theorem prime_thirtySixAH_25097 : Nat.Prime 25097 := by norm_num
private theorem prime_thirtySixAH_39050933 : Nat.Prime 39050933 := by
  apply lucas_primality 39050933 (2 : ZMod 39050933)
  · rw [← thirtySixAHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (389, 1), (25097, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (389, 1), (25097, 1)] : List FactorBlock).map factorBlockValue).prod = 39050933 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtySixAH_2
      · exact prime_thirtySixAH_389
      · exact prime_thirtySixAH_25097
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 39050933) ^ 19525466 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (2 : ZMod 39050933) ^ 100388 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (2 : ZMod 39050933) ^ 1556 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide

private theorem prime_thirtySixAH_18041531047 : Nat.Prime 18041531047 := by
  apply lucas_primality 18041531047 (3 : ZMod 18041531047)
  · rw [← thirtySixAHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (7, 1), (11, 1), (39050933, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (7, 1), (11, 1), (39050933, 1)] : List FactorBlock).map factorBlockValue).prod = 18041531047 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtySixAH_2
      · exact prime_thirtySixAH_3
      · exact prime_thirtySixAH_7
      · exact prime_thirtySixAH_11
      · exact prime_thirtySixAH_39050933
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 18041531047) ^ 9020765523 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (3 : ZMod 18041531047) ^ 6013843682 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (3 : ZMod 18041531047) ^ 2577361578 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (3 : ZMod 18041531047) ^ 1640139186 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (3 : ZMod 18041531047) ^ 462 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide

private theorem prime_thirtySixAH_257 : Nat.Prime 257 := by norm_num
private theorem prime_thirtySixAH_496342117 : Nat.Prime 496342117 := by
  apply lucas_primality 496342117 (2 : ZMod 496342117)
  · rw [← thirtySixAHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 2), (23, 1), (31, 1), (61, 1), (317, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 2), (23, 1), (31, 1), (61, 1), (317, 1)] : List FactorBlock).map factorBlockValue).prod = 496342117 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtySixAH_2
      · exact prime_thirtySixAH_3
      · exact prime_thirtySixAH_23
      · exact prime_thirtySixAH_31
      · exact prime_thirtySixAH_61
      · exact prime_thirtySixAH_317
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 496342117) ^ 248171058 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (2 : ZMod 496342117) ^ 165447372 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (2 : ZMod 496342117) ^ 21580092 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (2 : ZMod 496342117) ^ 16011036 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (2 : ZMod 496342117) ^ 8136756 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (2 : ZMod 496342117) ^ 1565748 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide

private theorem prime_thirtySixAH_466869322092541 : Nat.Prime 466869322092541 := by
  apply lucas_primality 466869322092541 (10 : ZMod 466869322092541)
  · rw [← thirtySixAHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (5, 1), (61, 1), (257, 1), (496342117, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (5, 1), (61, 1), (257, 1), (496342117, 1)] : List FactorBlock).map factorBlockValue).prod = 466869322092541 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtySixAH_2
      · exact prime_thirtySixAH_3
      · exact prime_thirtySixAH_5
      · exact prime_thirtySixAH_61
      · exact prime_thirtySixAH_257
      · exact prime_thirtySixAH_496342117
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 466869322092541) ^ 233434661046270 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (10 : ZMod 466869322092541) ^ 155623107364180 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (10 : ZMod 466869322092541) ^ 93373864418508 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (10 : ZMod 466869322092541) ^ 7653595444140 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (10 : ZMod 466869322092541) ^ 1816612148220 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (10 : ZMod 466869322092541) ^ 940620 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide

private theorem prime_thirtySixAH_919 : Nat.Prime 919 := by norm_num
private theorem prime_thirtySixAH_11257 : Nat.Prime 11257 := by norm_num
private theorem prime_thirtySixAH_425291 : Nat.Prime 425291 := by norm_num
private theorem prime_thirtySixAH_443 : Nat.Prime 443 := by norm_num
private theorem prime_thirtySixAH_292231 : Nat.Prime 292231 := by norm_num
private theorem prime_thirtySixAH_4610820719 : Nat.Prime 4610820719 := by
  apply lucas_primality 4610820719 (13 : ZMod 4610820719)
  · rw [← thirtySixAHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (7, 3), (23, 1), (292231, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (7, 3), (23, 1), (292231, 1)] : List FactorBlock).map factorBlockValue).prod = 4610820719 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtySixAH_2
      · exact prime_thirtySixAH_7
      · exact prime_thirtySixAH_23
      · exact prime_thirtySixAH_292231
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (13 : ZMod 4610820719) ^ 2305410359 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (13 : ZMod 4610820719) ^ 658688674 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (13 : ZMod 4610820719) ^ 200470466 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (13 : ZMod 4610820719) ^ 15778 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide

private theorem prime_thirtySixAH_302303849620517 : Nat.Prime 302303849620517 := by
  apply lucas_primality 302303849620517 (2 : ZMod 302303849620517)
  · rw [← thirtySixAHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (37, 1), (443, 1), (4610820719, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (37, 1), (443, 1), (4610820719, 1)] : List FactorBlock).map factorBlockValue).prod = 302303849620517 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtySixAH_2
      · exact prime_thirtySixAH_37
      · exact prime_thirtySixAH_443
      · exact prime_thirtySixAH_4610820719
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 302303849620517) ^ 151151924810258 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (2 : ZMod 302303849620517) ^ 8170374314068 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (2 : ZMod 302303849620517) ^ 682401466412 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (2 : ZMod 302303849620517) ^ 65564 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide

private theorem prime_thirtySixAH_137251 : Nat.Prime 137251 := by norm_num
private theorem prime_thirtySixAH_503 : Nat.Prime 503 := by norm_num
private theorem prime_thirtySixAH_1976731 : Nat.Prime 1976731 := by norm_num
private theorem prime_thirtySixAH_2112239 : Nat.Prime 2112239 := by norm_num
private theorem prime_thirtySixAH_9396985754191469517451 : Nat.Prime 9396985754191469517451 := by
  apply lucas_primality 9396985754191469517451 (2 : ZMod 9396985754191469517451)
  · rw [← thirtySixAHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 2), (5, 2), (61, 1), (163, 1), (503, 1), (1976731, 1), (2112239, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 2), (5, 2), (61, 1), (163, 1), (503, 1), (1976731, 1), (2112239, 1)] : List FactorBlock).map factorBlockValue).prod = 9396985754191469517451 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtySixAH_2
      · exact prime_thirtySixAH_3
      · exact prime_thirtySixAH_5
      · exact prime_thirtySixAH_61
      · exact prime_thirtySixAH_163
      · exact prime_thirtySixAH_503
      · exact prime_thirtySixAH_1976731
      · exact prime_thirtySixAH_2112239
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 9396985754191469517451) ^ 4698492877095734758725 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (2 : ZMod 9396985754191469517451) ^ 3132328584730489839150 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (2 : ZMod 9396985754191469517451) ^ 1879397150838293903490 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (2 : ZMod 9396985754191469517451) ^ 154048946790024090450 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (2 : ZMod 9396985754191469517451) ^ 57650219350867911150 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (2 : ZMod 9396985754191469517451) ^ 18681880227020814150 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (2 : ZMod 9396985754191469517451) ^ 4753800974533950 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (2 : ZMod 9396985754191469517451) ^ 4448826933974550 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide

private theorem prime_thirtySixAH_963499 : Nat.Prime 963499 := by norm_num
private theorem prime_thirtySixAH_101 : Nat.Prime 101 := by norm_num
private theorem prime_thirtySixAH_1146931 : Nat.Prime 1146931 := by norm_num
private theorem prime_thirtySixAH_55052689 : Nat.Prime 55052689 := by
  apply lucas_primality 55052689 (7 : ZMod 55052689)
  · rw [← thirtySixAHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 4), (3, 1), (1146931, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 4), (3, 1), (1146931, 1)] : List FactorBlock).map factorBlockValue).prod = 55052689 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtySixAH_2
      · exact prime_thirtySixAH_3
      · exact prime_thirtySixAH_1146931
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 55052689) ^ 27526344 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (7 : ZMod 55052689) ^ 18350896 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (7 : ZMod 55052689) ^ 48 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide

private theorem prime_thirtySixAH_11120643179 : Nat.Prime 11120643179 := by
  apply lucas_primality 11120643179 (2 : ZMod 11120643179)
  · rw [← thirtySixAHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (101, 1), (55052689, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (101, 1), (55052689, 1)] : List FactorBlock).map factorBlockValue).prod = 11120643179 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtySixAH_2
      · exact prime_thirtySixAH_101
      · exact prime_thirtySixAH_55052689
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 11120643179) ^ 5560321589 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (2 : ZMod 11120643179) ^ 110105378 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (2 : ZMod 11120643179) ^ 202 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide

private theorem prime_thirtySixAH_6914711 : Nat.Prime 6914711 := by norm_num
private theorem prime_thirtySixAH_19471826177 : Nat.Prime 19471826177 := by
  apply lucas_primality 19471826177 (3 : ZMod 19471826177)
  · rw [← thirtySixAHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 8), (11, 1), (6914711, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 8), (11, 1), (6914711, 1)] : List FactorBlock).map factorBlockValue).prod = 19471826177 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtySixAH_2
      · exact prime_thirtySixAH_11
      · exact prime_thirtySixAH_6914711
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 19471826177) ^ 9735913088 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (3 : ZMod 19471826177) ^ 1770166016 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (3 : ZMod 19471826177) ^ 2816 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide

private theorem prime_thirtySixAH_1299235385747572180099 : Nat.Prime 1299235385747572180099 := by
  apply lucas_primality 1299235385747572180099 (2 : ZMod 1299235385747572180099)
  · rw [← thirtySixAHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (11120643179, 1), (19471826177, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (11120643179, 1), (19471826177, 1)] : List FactorBlock).map factorBlockValue).prod = 1299235385747572180099 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtySixAH_2
      · exact prime_thirtySixAH_3
      · exact prime_thirtySixAH_11120643179
      · exact prime_thirtySixAH_19471826177
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1299235385747572180099) ^ 649617692873786090049 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (2 : ZMod 1299235385747572180099) ^ 433078461915857393366 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (2 : ZMod 1299235385747572180099) ^ 116830957062 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (2 : ZMod 1299235385747572180099) ^ 66723859074 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide

private theorem prime_thirtySixAH_2929571 : Nat.Prime 2929571 := by norm_num
private theorem prime_thirtySixAH_1597 : Nat.Prime 1597 := by norm_num
private theorem prime_thirtySixAH_11059 : Nat.Prime 11059 := by norm_num
private theorem prime_thirtySixAH_131543 : Nat.Prime 131543 := by norm_num
private theorem prime_thirtySixAH_217363 : Nat.Prime 217363 := by norm_num
private theorem prime_thirtySixAH_3029879706669817843 : Nat.Prime 3029879706669817843 := by
  apply lucas_primality 3029879706669817843 (17 : ZMod 3029879706669817843)
  · rw [← thirtySixAHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (1597, 1), (11059, 1), (131543, 1), (217363, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (1597, 1), (11059, 1), (131543, 1), (217363, 1)] : List FactorBlock).map factorBlockValue).prod = 3029879706669817843 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtySixAH_2
      · exact prime_thirtySixAH_3
      · exact prime_thirtySixAH_1597
      · exact prime_thirtySixAH_11059
      · exact prime_thirtySixAH_131543
      · exact prime_thirtySixAH_217363
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (17 : ZMod 3029879706669817843) ^ 1514939853334908921 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (17 : ZMod 3029879706669817843) ^ 1009959902223272614 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (17 : ZMod 3029879706669817843) ^ 1897232126906586 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (17 : ZMod 3029879706669817843) ^ 273974112186438 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (17 : ZMod 3029879706669817843) ^ 23033378489694 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (17 : ZMod 3029879706669817843) ^ 13939261542534 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide

private theorem prime_thirtySixAH_103 : Nat.Prime 103 := by norm_num
private theorem prime_thirtySixAH_5009 : Nat.Prime 5009 := by norm_num
private theorem prime_thirtySixAH_107 : Nat.Prime 107 := by norm_num
private theorem prime_thirtySixAH_61717 : Nat.Prime 61717 := by norm_num
private theorem prime_thirtySixAH_35279 : Nat.Prime 35279 := by norm_num
private theorem prime_thirtySixAH_7190123 : Nat.Prime 7190123 := by norm_num
private theorem prime_thirtySixAH_1521962095903 : Nat.Prime 1521962095903 := by
  apply lucas_primality 1521962095903 (3 : ZMod 1521962095903)
  · rw [← thirtySixAHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (35279, 1), (7190123, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (35279, 1), (7190123, 1)] : List FactorBlock).map factorBlockValue).prod = 1521962095903 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtySixAH_2
      · exact prime_thirtySixAH_3
      · exact prime_thirtySixAH_35279
      · exact prime_thirtySixAH_7190123
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1521962095903) ^ 760981047951 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (3 : ZMod 1521962095903) ^ 507320698634 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (3 : ZMod 1521962095903) ^ 43140738 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (3 : ZMod 1521962095903) ^ 211674 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide

private theorem prime_thirtySixAH_563585608037072707 : Nat.Prime 563585608037072707 := by
  apply lucas_primality 563585608037072707 (3 : ZMod 563585608037072707)
  · rw [← thirtySixAHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (61717, 1), (1521962095903, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (61717, 1), (1521962095903, 1)] : List FactorBlock).map factorBlockValue).prod = 563585608037072707 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtySixAH_2
      · exact prime_thirtySixAH_3
      · exact prime_thirtySixAH_61717
      · exact prime_thirtySixAH_1521962095903
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 563585608037072707) ^ 281792804018536353 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (3 : ZMod 563585608037072707) ^ 187861869345690902 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (3 : ZMod 563585608037072707) ^ 9131772575418 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (3 : ZMod 563585608037072707) ^ 370302 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide

private theorem prime_thirtySixAH_2291539082278737626663 : Nat.Prime 2291539082278737626663 := by
  apply lucas_primality 2291539082278737626663 (10 : ZMod 2291539082278737626663)
  · rw [← thirtySixAHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (19, 1), (107, 1), (563585608037072707, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (19, 1), (107, 1), (563585608037072707, 1)] : List FactorBlock).map factorBlockValue).prod = 2291539082278737626663 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtySixAH_2
      · exact prime_thirtySixAH_19
      · exact prime_thirtySixAH_107
      · exact prime_thirtySixAH_563585608037072707
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (10 : ZMod 2291539082278737626663) ^ 1145769541139368813331 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (10 : ZMod 2291539082278737626663) ^ 120607320119933559298 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (10 : ZMod 2291539082278737626663) ^ 21416253105408762866 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (10 : ZMod 2291539082278737626663) ^ 4066 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide

private theorem prime_thirtySixAH_15881 : Nat.Prime 15881 := by norm_num
private theorem prime_thirtySixAH_357283 : Nat.Prime 357283 := by norm_num
private theorem prime_thirtySixAH_227 : Nat.Prime 227 := by norm_num
private theorem prime_thirtySixAH_1723 : Nat.Prime 1723 := by norm_num
private theorem prime_thirtySixAH_10987 : Nat.Prime 10987 := by norm_num
private theorem prime_thirtySixAH_870807647 : Nat.Prime 870807647 := by
  apply lucas_primality 870807647 (5 : ZMod 870807647)
  · rw [← thirtySixAHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (23, 1), (1723, 1), (10987, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (23, 1), (1723, 1), (10987, 1)] : List FactorBlock).map factorBlockValue).prod = 870807647 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtySixAH_2
      · exact prime_thirtySixAH_23
      · exact prime_thirtySixAH_1723
      · exact prime_thirtySixAH_10987
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 870807647) ^ 435403823 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (5 : ZMod 870807647) ^ 37861202 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (5 : ZMod 870807647) ^ 505402 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (5 : ZMod 870807647) ^ 79258 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide

private theorem prime_thirtySixAH_7906933434761 : Nat.Prime 7906933434761 := by
  apply lucas_primality 7906933434761 (3 : ZMod 7906933434761)
  · rw [← thirtySixAHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (5, 1), (227, 1), (870807647, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (5, 1), (227, 1), (870807647, 1)] : List FactorBlock).map factorBlockValue).prod = 7906933434761 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtySixAH_2
      · exact prime_thirtySixAH_5
      · exact prime_thirtySixAH_227
      · exact prime_thirtySixAH_870807647
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 7906933434761) ^ 3953466717380 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (3 : ZMod 7906933434761) ^ 1581386686952 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (3 : ZMod 7906933434761) ^ 34832305880 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (3 : ZMod 7906933434761) ^ 9080 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide

private theorem prime_thirtySixAH_72433330714250756267321 : Nat.Prime 72433330714250756267321 := by
  apply lucas_primality 72433330714250756267321 (3 : ZMod 72433330714250756267321)
  · rw [← thirtySixAHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (5, 1), (641, 1), (357283, 1), (7906933434761, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (5, 1), (641, 1), (357283, 1), (7906933434761, 1)] : List FactorBlock).map factorBlockValue).prod = 72433330714250756267321 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtySixAH_2
      · exact prime_thirtySixAH_5
      · exact prime_thirtySixAH_641
      · exact prime_thirtySixAH_357283
      · exact prime_thirtySixAH_7906933434761
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 72433330714250756267321) ^ 36216665357125378133660 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (3 : ZMod 72433330714250756267321) ^ 14486666142850151253464 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (3 : ZMod 72433330714250756267321) ^ 113000515934868574520 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (3 : ZMod 72433330714250756267321) ^ 202733773267272040 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (3 : ZMod 72433330714250756267321) ^ 9160736120 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide

private theorem prime_thirtySixAH_8713 : Nat.Prime 8713 := by norm_num
private theorem prime_thirtySixAH_712477 : Nat.Prime 712477 := by norm_num
private theorem prime_thirtySixAH_13229 : Nat.Prime 13229 := by norm_num
private theorem prime_thirtySixAH_23415331 : Nat.Prime 23415331 := by
  apply lucas_primality 23415331 (2 : ZMod 23415331)
  · rw [← thirtySixAHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (5, 1), (59, 1), (13229, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (5, 1), (59, 1), (13229, 1)] : List FactorBlock).map factorBlockValue).prod = 23415331 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtySixAH_2
      · exact prime_thirtySixAH_3
      · exact prime_thirtySixAH_5
      · exact prime_thirtySixAH_59
      · exact prime_thirtySixAH_13229
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 23415331) ^ 11707665 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (2 : ZMod 23415331) ^ 7805110 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (2 : ZMod 23415331) ^ 4683066 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (2 : ZMod 23415331) ^ 396870 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (2 : ZMod 23415331) ^ 1770 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide

private theorem prime_thirtySixAH_2383 : Nat.Prime 2383 := by norm_num
private theorem prime_thirtySixAH_8291 : Nat.Prime 8291 := by norm_num
private theorem prime_thirtySixAH_7705406671 : Nat.Prime 7705406671 := by
  apply lucas_primality 7705406671 (6 : ZMod 7705406671)
  · rw [← thirtySixAHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (5, 1), (13, 1), (2383, 1), (8291, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (5, 1), (13, 1), (2383, 1), (8291, 1)] : List FactorBlock).map factorBlockValue).prod = 7705406671 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtySixAH_2
      · exact prime_thirtySixAH_3
      · exact prime_thirtySixAH_5
      · exact prime_thirtySixAH_13
      · exact prime_thirtySixAH_2383
      · exact prime_thirtySixAH_8291
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 7705406671) ^ 3852703335 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (6 : ZMod 7705406671) ^ 2568468890 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (6 : ZMod 7705406671) ^ 1541081334 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (6 : ZMod 7705406671) ^ 592723590 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (6 : ZMod 7705406671) ^ 3233490 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (6 : ZMod 7705406671) ^ 929370 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide

private theorem prime_thirtySixAH_431 : Nat.Prime 431 := by norm_num
private theorem prime_thirtySixAH_11719 : Nat.Prime 11719 := by norm_num
private theorem prime_thirtySixAH_1228273 : Nat.Prime 1228273 := by norm_num
private theorem prime_thirtySixAH_9574219 : Nat.Prime 9574219 := by norm_num
private theorem prime_thirtySixAH_18373307 : Nat.Prime 18373307 := by norm_num
private theorem prime_thirtySixAH_139 : Nat.Prime 139 := by norm_num
private theorem prime_thirtySixAH_577 : Nat.Prime 577 := by norm_num
private theorem prime_thirtySixAH_2303321 : Nat.Prime 2303321 := by norm_num
private theorem prime_thirtySixAH_34057 : Nat.Prime 34057 := by norm_num
private theorem prime_thirtySixAH_20025517 : Nat.Prime 20025517 := by
  apply lucas_primality 20025517 (2 : ZMod 20025517)
  · rw [← thirtySixAHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (7, 2), (34057, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (7, 2), (34057, 1)] : List FactorBlock).map factorBlockValue).prod = 20025517 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtySixAH_2
      · exact prime_thirtySixAH_3
      · exact prime_thirtySixAH_7
      · exact prime_thirtySixAH_34057
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 20025517) ^ 10012758 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (2 : ZMod 20025517) ^ 6675172 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (2 : ZMod 20025517) ^ 2860788 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (2 : ZMod 20025517) ^ 588 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide

private theorem prime_thirtySixAH_2879936805405053 : Nat.Prime 2879936805405053 := by
  apply lucas_primality 2879936805405053 (2 : ZMod 2879936805405053)
  · rw [← thirtySixAHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (19, 1), (61, 1), (67, 1), (463, 1), (20025517, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (19, 1), (61, 1), (67, 1), (463, 1), (20025517, 1)] : List FactorBlock).map factorBlockValue).prod = 2879936805405053 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtySixAH_2
      · exact prime_thirtySixAH_19
      · exact prime_thirtySixAH_61
      · exact prime_thirtySixAH_67
      · exact prime_thirtySixAH_463
      · exact prime_thirtySixAH_20025517
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 2879936805405053) ^ 1439968402702526 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (2 : ZMod 2879936805405053) ^ 151575621337108 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (2 : ZMod 2879936805405053) ^ 47212078777132 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (2 : ZMod 2879936805405053) ^ 42984131423956 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (2 : ZMod 2879936805405053) ^ 6220165886404 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (2 : ZMod 2879936805405053) ^ 143813356 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide

private theorem prime_thirtySixAH_5759873610810107 : Nat.Prime 5759873610810107 := by
  apply lucas_primality 5759873610810107 (2 : ZMod 5759873610810107)
  · rw [← thirtySixAHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (2879936805405053, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (2879936805405053, 1)] : List FactorBlock).map factorBlockValue).prod = 5759873610810107 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_thirtySixAH_2
      · exact prime_thirtySixAH_2879936805405053
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 5759873610810107) ^ 2879936805405053 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (2 : ZMod 5759873610810107) ^ 2 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide

private theorem prime_thirtySixAH_83 : Nat.Prime 83 := by norm_num
private theorem prime_thirtySixAH_269 : Nat.Prime 269 := by norm_num
private theorem prime_thirtySixAH_191 : Nat.Prime 191 := by norm_num
private theorem prime_thirtySixAH_1181 : Nat.Prime 1181 := by norm_num
private theorem prime_thirtySixAH_1657519 : Nat.Prime 1657519 := by norm_num
private theorem prime_thirtySixAH_271 : Nat.Prime 271 := by norm_num
private theorem prime_thirtySixAH_156719 : Nat.Prime 156719 := by norm_num
private theorem prime_thirtySixAH_339766793 : Nat.Prime 339766793 := by
  apply lucas_primality 339766793 (3 : ZMod 339766793)
  · rw [← thirtySixAHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (271, 1), (156719, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (271, 1), (156719, 1)] : List FactorBlock).map factorBlockValue).prod = 339766793 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtySixAH_2
      · exact prime_thirtySixAH_271
      · exact prime_thirtySixAH_156719
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 339766793) ^ 169883396 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (3 : ZMod 339766793) ^ 1253752 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (3 : ZMod 339766793) ^ 2168 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide

private theorem prime_thirtySixAH_46494737125345995421063 : Nat.Prime 46494737125345995421063 := by
  apply lucas_primality 46494737125345995421063 (3 : ZMod 46494737125345995421063)
  · rw [← thirtySixAHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (61, 1), (191, 1), (1181, 1), (1657519, 1), (339766793, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (61, 1), (191, 1), (1181, 1), (1657519, 1), (339766793, 1)] : List FactorBlock).map factorBlockValue).prod = 46494737125345995421063 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtySixAH_2
      · exact prime_thirtySixAH_3
      · exact prime_thirtySixAH_61
      · exact prime_thirtySixAH_191
      · exact prime_thirtySixAH_1181
      · exact prime_thirtySixAH_1657519
      · exact prime_thirtySixAH_339766793
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 46494737125345995421063) ^ 23247368562672997710531 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (3 : ZMod 46494737125345995421063) ^ 15498245708448665140354 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (3 : ZMod 46494737125345995421063) ^ 762208805333540908542 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (3 : ZMod 46494737125345995421063) ^ 243427943064638719482 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (3 : ZMod 46494737125345995421063) ^ 39368956075652832702 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (3 : ZMod 46494737125345995421063) ^ 28050801906551898 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (3 : ZMod 46494737125345995421063) ^ 136843087915734 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide

private theorem prime_thirtySixAH_331 : Nat.Prime 331 := by norm_num
private theorem prime_thirtySixAH_7129 : Nat.Prime 7129 := by norm_num
private theorem prime_thirtySixAH_199 : Nat.Prime 199 := by norm_num
private theorem prime_thirtySixAH_5449 : Nat.Prime 5449 := by norm_num
private theorem prime_thirtySixAH_8089 : Nat.Prime 8089 := by norm_num
private theorem prime_thirtySixAH_4121269 : Nat.Prime 4121269 := by norm_num
private theorem prime_thirtySixAH_123638071 : Nat.Prime 123638071 := by
  apply lucas_primality 123638071 (7 : ZMod 123638071)
  · rw [← thirtySixAHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (5, 1), (4121269, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (5, 1), (4121269, 1)] : List FactorBlock).map factorBlockValue).prod = 123638071 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtySixAH_2
      · exact prime_thirtySixAH_3
      · exact prime_thirtySixAH_5
      · exact prime_thirtySixAH_4121269
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 123638071) ^ 61819035 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (7 : ZMod 123638071) ^ 41212690 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (7 : ZMod 123638071) ^ 24727614 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (7 : ZMod 123638071) ^ 30 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide

private theorem prime_thirtySixAH_741828427 : Nat.Prime 741828427 := by
  apply lucas_primality 741828427 (2 : ZMod 741828427)
  · rw [← thirtySixAHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (123638071, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (123638071, 1)] : List FactorBlock).map factorBlockValue).prod = 741828427 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtySixAH_2
      · exact prime_thirtySixAH_3
      · exact prime_thirtySixAH_123638071
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 741828427) ^ 370914213 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (2 : ZMod 741828427) ^ 247276142 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (2 : ZMod 741828427) ^ 6 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide

private theorem prime_thirtySixAH_429449525106920937499 : Nat.Prime 429449525106920937499 := by
  apply lucas_primality 429449525106920937499 (2 : ZMod 429449525106920937499)
  · rw [← thirtySixAHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (11, 1), (199, 1), (5449, 1), (8089, 1), (741828427, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (11, 1), (199, 1), (5449, 1), (8089, 1), (741828427, 1)] : List FactorBlock).map factorBlockValue).prod = 429449525106920937499 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtySixAH_2
      · exact prime_thirtySixAH_3
      · exact prime_thirtySixAH_11
      · exact prime_thirtySixAH_199
      · exact prime_thirtySixAH_5449
      · exact prime_thirtySixAH_8089
      · exact prime_thirtySixAH_741828427
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 429449525106920937499) ^ 214724762553460468749 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (2 : ZMod 429449525106920937499) ^ 143149841702306979166 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (2 : ZMod 429449525106920937499) ^ 39040865918810994318 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (2 : ZMod 429449525106920937499) ^ 2158037814607642902 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (2 : ZMod 429449525106920937499) ^ 78812539017603402 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (2 : ZMod 429449525106920937499) ^ 53090558178627882 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (2 : ZMod 429449525106920937499) ^ 578906805774 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide

private theorem prime_thirtySixAH_125197 : Nat.Prime 125197 := by norm_num
private theorem prime_thirtySixAH_659 : Nat.Prime 659 := by norm_num
private theorem prime_thirtySixAH_3769 : Nat.Prime 3769 := by norm_num
private theorem prime_thirtySixAH_617 : Nat.Prime 617 := by norm_num
private theorem prime_thirtySixAH_971 : Nat.Prime 971 := by norm_num
private theorem prime_thirtySixAH_32351779 : Nat.Prime 32351779 := by
  apply lucas_primality 32351779 (2 : ZMod 32351779)
  · rw [← thirtySixAHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 3), (617, 1), (971, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 3), (617, 1), (971, 1)] : List FactorBlock).map factorBlockValue).prod = 32351779 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtySixAH_2
      · exact prime_thirtySixAH_3
      · exact prime_thirtySixAH_617
      · exact prime_thirtySixAH_971
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 32351779) ^ 16175889 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (2 : ZMod 32351779) ^ 10783926 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (2 : ZMod 32351779) ^ 52434 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (2 : ZMod 32351779) ^ 33318 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide

private theorem prime_thirtySixAH_30175491767032037771 : Nat.Prime 30175491767032037771 := by
  apply lucas_primality 30175491767032037771 (6 : ZMod 30175491767032037771)
  · rw [← thirtySixAHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 1), (17, 1), (47, 2), (659, 1), (3769, 1), (32351779, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 1), (17, 1), (47, 2), (659, 1), (3769, 1), (32351779, 1)] : List FactorBlock).map factorBlockValue).prod = 30175491767032037771 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtySixAH_2
      · exact prime_thirtySixAH_5
      · exact prime_thirtySixAH_17
      · exact prime_thirtySixAH_47
      · exact prime_thirtySixAH_659
      · exact prime_thirtySixAH_3769
      · exact prime_thirtySixAH_32351779
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 30175491767032037771) ^ 15087745883516018885 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (6 : ZMod 30175491767032037771) ^ 6035098353406407554 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (6 : ZMod 30175491767032037771) ^ 1775028927472472810 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (6 : ZMod 30175491767032037771) ^ 642031739724085910 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (6 : ZMod 30175491767032037771) ^ 45789820587302030 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (6 : ZMod 30175491767032037771) ^ 8006232891226330 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (6 : ZMod 30175491767032037771) ^ 932730523630 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide

private theorem prime_thirtySixAH_60350983534064075543 : Nat.Prime 60350983534064075543 := by
  apply lucas_primality 60350983534064075543 (5 : ZMod 60350983534064075543)
  · rw [← thirtySixAHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (30175491767032037771, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (30175491767032037771, 1)] : List FactorBlock).map factorBlockValue).prod = 60350983534064075543 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_thirtySixAH_2
      · exact prime_thirtySixAH_30175491767032037771
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 60350983534064075543) ^ 30175491767032037771 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (5 : ZMod 60350983534064075543) ^ 2 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide

private theorem prime_thirtySixAH_60793 : Nat.Prime 60793 := by norm_num
private theorem prime_thirtySixAH_33749 : Nat.Prime 33749 := by norm_num
private theorem prime_thirtySixAH_109481 : Nat.Prime 109481 := by norm_num
private theorem prime_thirtySixAH_5205667 : Nat.Prime 5205667 := by norm_num
private theorem prime_thirtySixAH_791051220811877 : Nat.Prime 791051220811877 := by
  apply lucas_primality 791051220811877 (2 : ZMod 791051220811877)
  · rw [← thirtySixAHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (347, 1), (109481, 1), (5205667, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (347, 1), (109481, 1), (5205667, 1)] : List FactorBlock).map factorBlockValue).prod = 791051220811877 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtySixAH_2
      · exact prime_thirtySixAH_347
      · exact prime_thirtySixAH_109481
      · exact prime_thirtySixAH_5205667
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 791051220811877) ^ 395525610405938 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (2 : ZMod 791051220811877) ^ 2279686515308 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (2 : ZMod 791051220811877) ^ 7225465796 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (2 : ZMod 791051220811877) ^ 151959628 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide

private theorem prime_thirtySixAH_106788750604720147493 : Nat.Prime 106788750604720147493 := by
  apply lucas_primality 106788750604720147493 (2 : ZMod 106788750604720147493)
  · rw [← thirtySixAHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (33749, 1), (791051220811877, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (33749, 1), (791051220811877, 1)] : List FactorBlock).map factorBlockValue).prod = 106788750604720147493 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtySixAH_2
      · exact prime_thirtySixAH_33749
      · exact prime_thirtySixAH_791051220811877
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 106788750604720147493) ^ 53394375302360073746 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (2 : ZMod 106788750604720147493) ^ 3164204883247508 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (2 : ZMod 106788750604720147493) ^ 134996 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide

private theorem prime_thirtySixAH_1013 : Nat.Prime 1013 := by norm_num
private theorem prime_thirtySixAH_7220867 : Nat.Prime 7220867 := by norm_num
private theorem prime_thirtySixAH_144417341 : Nat.Prime 144417341 := by
  apply lucas_primality 144417341 (2 : ZMod 144417341)
  · rw [← thirtySixAHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (5, 1), (7220867, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (5, 1), (7220867, 1)] : List FactorBlock).map factorBlockValue).prod = 144417341 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtySixAH_2
      · exact prime_thirtySixAH_5
      · exact prime_thirtySixAH_7220867
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 144417341) ^ 72208670 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (2 : ZMod 144417341) ^ 28883468 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (2 : ZMod 144417341) ^ 20 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide

private theorem prime_thirtySixAH_373 : Nat.Prime 373 := by norm_num
private theorem prime_thirtySixAH_277100209 : Nat.Prime 277100209 := by
  apply lucas_primality 277100209 (17 : ZMod 277100209)
  · rw [← thirtySixAHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 4), (3, 2), (7, 1), (11, 1), (67, 1), (373, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 4), (3, 2), (7, 1), (11, 1), (67, 1), (373, 1)] : List FactorBlock).map factorBlockValue).prod = 277100209 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtySixAH_2
      · exact prime_thirtySixAH_3
      · exact prime_thirtySixAH_7
      · exact prime_thirtySixAH_11
      · exact prime_thirtySixAH_67
      · exact prime_thirtySixAH_373
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (17 : ZMod 277100209) ^ 138550104 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (17 : ZMod 277100209) ^ 92366736 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (17 : ZMod 277100209) ^ 39585744 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (17 : ZMod 277100209) ^ 25190928 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (17 : ZMod 277100209) ^ 4135824 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (17 : ZMod 277100209) ^ 742896 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide

private theorem prime_thirtySixAH_60421700572451 : Nat.Prime 60421700572451 := by
  apply lucas_primality 60421700572451 (2 : ZMod 60421700572451)
  · rw [← thirtySixAHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 2), (7, 2), (89, 1), (277100209, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 2), (7, 2), (89, 1), (277100209, 1)] : List FactorBlock).map factorBlockValue).prod = 60421700572451 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtySixAH_2
      · exact prime_thirtySixAH_5
      · exact prime_thirtySixAH_7
      · exact prime_thirtySixAH_89
      · exact prime_thirtySixAH_277100209
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 60421700572451) ^ 30210850286225 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (2 : ZMod 60421700572451) ^ 12084340114490 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (2 : ZMod 60421700572451) ^ 8631671510350 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (2 : ZMod 60421700572451) ^ 678895512050 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (2 : ZMod 60421700572451) ^ 218050 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide

private theorem prime_thirtySixAH_328103 : Nat.Prime 328103 := by norm_num
private theorem prime_thirtySixAH_1289 : Nat.Prime 1289 := by norm_num
private theorem prime_thirtySixAH_11821 : Nat.Prime 11821 := by norm_num
private theorem prime_thirtySixAH_8699 : Nat.Prime 8699 := by norm_num
private theorem prime_thirtySixAH_68713 : Nat.Prime 68713 := by norm_num
private theorem prime_thirtySixAH_158997346943 : Nat.Prime 158997346943 := by
  apply lucas_primality 158997346943 (5 : ZMod 158997346943)
  · rw [← thirtySixAHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (7, 1), (19, 1), (8699, 1), (68713, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (7, 1), (19, 1), (8699, 1), (68713, 1)] : List FactorBlock).map factorBlockValue).prod = 158997346943 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtySixAH_2
      · exact prime_thirtySixAH_7
      · exact prime_thirtySixAH_19
      · exact prime_thirtySixAH_8699
      · exact prime_thirtySixAH_68713
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 158997346943) ^ 79498673471 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (5 : ZMod 158997346943) ^ 22713906706 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (5 : ZMod 158997346943) ^ 8368281418 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (5 : ZMod 158997346943) ^ 18277658 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (5 : ZMod 158997346943) ^ 2313934 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide

private theorem prime_thirtySixAH_1093873445440084147 : Nat.Prime 1093873445440084147 := by
  apply lucas_primality 1093873445440084147 (5 : ZMod 1093873445440084147)
  · rw [← thirtySixAHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (97, 1), (11821, 1), (158997346943, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (97, 1), (11821, 1), (158997346943, 1)] : List FactorBlock).map factorBlockValue).prod = 1093873445440084147 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtySixAH_2
      · exact prime_thirtySixAH_3
      · exact prime_thirtySixAH_97
      · exact prime_thirtySixAH_11821
      · exact prime_thirtySixAH_158997346943
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 1093873445440084147) ^ 546936722720042073 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (5 : ZMod 1093873445440084147) ^ 364624481813361382 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (5 : ZMod 1093873445440084147) ^ 11277045829279218 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (5 : ZMod 1093873445440084147) ^ 92536455920826 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (5 : ZMod 1093873445440084147) ^ 6879822 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide

private theorem prime_thirtySixAH_2820005742344536930967 : Nat.Prime 2820005742344536930967 := by
  apply lucas_primality 2820005742344536930967 (5 : ZMod 2820005742344536930967)
  · rw [← thirtySixAHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (1289, 1), (1093873445440084147, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (1289, 1), (1093873445440084147, 1)] : List FactorBlock).map factorBlockValue).prod = 2820005742344536930967 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtySixAH_2
      · exact prime_thirtySixAH_1289
      · exact prime_thirtySixAH_1093873445440084147
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 2820005742344536930967) ^ 1410002871172268465483 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (5 : ZMod 2820005742344536930967) ^ 2187746890880168294 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (5 : ZMod 2820005742344536930967) ^ 2578 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide

private theorem prime_thirtySixAH_905566123993651098519340801 : Nat.Prime 905566123993651098519340801 := by
  apply lucas_primality 905566123993651098519340801 (127 : ZMod 905566123993651098519340801)
  · rw [← thirtySixAHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 8), (3, 5), (5, 2), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 8), (3, 5), (5, 2), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod = 905566123993651098519340801 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtySixAH_2
      · exact prime_thirtySixAH_3
      · exact prime_thirtySixAH_5
      · exact prime_thirtySixAH_7
      · exact prime_thirtySixAH_11
      · exact prime_thirtySixAH_13
      · exact prime_thirtySixAH_17
      · exact prime_thirtySixAH_19
      · exact prime_thirtySixAH_23
      · exact prime_thirtySixAH_29
      · exact prime_thirtySixAH_31
      · exact prime_thirtySixAH_37
      · exact prime_thirtySixAH_41
      · exact prime_thirtySixAH_43
      · exact prime_thirtySixAH_53
      · exact prime_thirtySixAH_59
      · exact prime_thirtySixAH_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (127 : ZMod 905566123993651098519340801) ^ 452783061996825549259670400 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (127 : ZMod 905566123993651098519340801) ^ 301855374664550366173113600 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (127 : ZMod 905566123993651098519340801) ^ 181113224798730219703868160 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (127 : ZMod 905566123993651098519340801) ^ 129366589141950156931334400 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (127 : ZMod 905566123993651098519340801) ^ 82324193090331918047212800 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (127 : ZMod 905566123993651098519340801) ^ 69658932614896238347641600 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (127 : ZMod 905566123993651098519340801) ^ 53268595529038299912902400 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (127 : ZMod 905566123993651098519340801) ^ 47661374947034268343123200 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (127 : ZMod 905566123993651098519340801) ^ 39372440173637004283449600 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (127 : ZMod 905566123993651098519340801) ^ 31226418068746589604115200 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (127 : ZMod 905566123993651098519340801) ^ 29211810451408099952236800 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (127 : ZMod 905566123993651098519340801) ^ 24474760107936516176198400 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (127 : ZMod 905566123993651098519340801) ^ 22086978633991490207788800 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (127 : ZMod 905566123993651098519340801) ^ 21059677302177932523705600 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (127 : ZMod 905566123993651098519340801) ^ 17086153282899077330553600 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (127 : ZMod 905566123993651098519340801) ^ 15348578372773747432531200 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (127 : ZMod 905566123993651098519340801) ^ 14845346294977886860972800 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide

private theorem prime_thirtySixAH_769 : Nat.Prime 769 := by norm_num
private theorem prime_thirtySixAH_2143 : Nat.Prime 2143 := by norm_num
private theorem prime_thirtySixAH_8597 : Nat.Prime 8597 := by norm_num
private theorem prime_thirtySixAH_9792301 : Nat.Prime 9792301 := by norm_num
private theorem prime_thirtySixAH_161017 : Nat.Prime 161017 := by norm_num
private theorem prime_thirtySixAH_6391408799 : Nat.Prime 6391408799 := by
  apply lucas_primality 6391408799 (23 : ZMod 6391408799)
  · rw [← thirtySixAHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (89, 1), (223, 1), (161017, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (89, 1), (223, 1), (161017, 1)] : List FactorBlock).map factorBlockValue).prod = 6391408799 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtySixAH_2
      · exact prime_thirtySixAH_89
      · exact prime_thirtySixAH_223
      · exact prime_thirtySixAH_161017
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (23 : ZMod 6391408799) ^ 3195704399 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (23 : ZMod 6391408799) ^ 71813582 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (23 : ZMod 6391408799) ^ 28661026 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (23 : ZMod 6391408799) ^ 39694 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide

private theorem prime_thirtySixAH_14051 : Nat.Prime 14051 := by norm_num
private theorem prime_thirtySixAH_114299 : Nat.Prime 114299 := by norm_num
private theorem prime_thirtySixAH_2141048869 : Nat.Prime 2141048869 := by
  apply lucas_primality 2141048869 (2 : ZMod 2141048869)
  · rw [← thirtySixAHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (7, 1), (223, 1), (114299, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (7, 1), (223, 1), (114299, 1)] : List FactorBlock).map factorBlockValue).prod = 2141048869 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtySixAH_2
      · exact prime_thirtySixAH_3
      · exact prime_thirtySixAH_7
      · exact prime_thirtySixAH_223
      · exact prime_thirtySixAH_114299
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 2141048869) ^ 1070524434 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (2 : ZMod 2141048869) ^ 713682956 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (2 : ZMod 2141048869) ^ 305864124 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (2 : ZMod 2141048869) ^ 9601116 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (2 : ZMod 2141048869) ^ 18732 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide

private theorem prime_thirtySixAH_9349 : Nat.Prime 9349 := by norm_num
private theorem prime_thirtySixAH_8257553 : Nat.Prime 8257553 := by norm_num
private theorem prime_thirtySixAH_28872748760879 : Nat.Prime 28872748760879 := by
  apply lucas_primality 28872748760879 (7 : ZMod 28872748760879)
  · rw [← thirtySixAHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (11, 1), (17, 1), (9349, 1), (8257553, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (11, 1), (17, 1), (9349, 1), (8257553, 1)] : List FactorBlock).map factorBlockValue).prod = 28872748760879 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtySixAH_2
      · exact prime_thirtySixAH_11
      · exact prime_thirtySixAH_17
      · exact prime_thirtySixAH_9349
      · exact prime_thirtySixAH_8257553
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 28872748760879) ^ 14436374380439 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (7 : ZMod 28872748760879) ^ 2624795341898 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (7 : ZMod 28872748760879) ^ 1698396985934 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (7 : ZMod 28872748760879) ^ 3088324822 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (7 : ZMod 28872748760879) ^ 3496526 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide

private theorem prime_thirtySixAH_24421 : Nat.Prime 24421 := by norm_num
private theorem prime_thirtySixAH_2273 : Nat.Prime 2273 := by norm_num
private theorem prime_thirtySixAH_3307 : Nat.Prime 3307 := by norm_num
private theorem prime_thirtySixAH_1399 : Nat.Prime 1399 := by norm_num
private theorem prime_thirtySixAH_385607 : Nat.Prime 385607 := by norm_num
private theorem prime_thirtySixAH_1078928387 : Nat.Prime 1078928387 := by
  apply lucas_primality 1078928387 (2 : ZMod 1078928387)
  · rw [← thirtySixAHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (1399, 1), (385607, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (1399, 1), (385607, 1)] : List FactorBlock).map factorBlockValue).prod = 1078928387 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtySixAH_2
      · exact prime_thirtySixAH_1399
      · exact prime_thirtySixAH_385607
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 1078928387) ^ 539464193 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (2 : ZMod 1078928387) ^ 771214 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (2 : ZMod 1078928387) ^ 2798 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide

private theorem prime_thirtySixAH_28544129406473 : Nat.Prime 28544129406473 := by
  apply lucas_primality 28544129406473 (3 : ZMod 28544129406473)
  · rw [← thirtySixAHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (3307, 1), (1078928387, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (3307, 1), (1078928387, 1)] : List FactorBlock).map factorBlockValue).prod = 28544129406473 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtySixAH_2
      · exact prime_thirtySixAH_3307
      · exact prime_thirtySixAH_1078928387
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 28544129406473) ^ 14272064703236 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (3 : ZMod 28544129406473) ^ 8631427096 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (3 : ZMod 28544129406473) ^ 26456 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide

private theorem prime_thirtySixAH_3139854234712031 : Nat.Prime 3139854234712031 := by
  apply lucas_primality 3139854234712031 (7 : ZMod 3139854234712031)
  · rw [← thirtySixAHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 1), (11, 1), (28544129406473, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 1), (11, 1), (28544129406473, 1)] : List FactorBlock).map factorBlockValue).prod = 3139854234712031 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtySixAH_2
      · exact prime_thirtySixAH_5
      · exact prime_thirtySixAH_11
      · exact prime_thirtySixAH_28544129406473
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 3139854234712031) ^ 1569927117356015 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (7 : ZMod 3139854234712031) ^ 627970846942406 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (7 : ZMod 3139854234712031) ^ 285441294064730 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (7 : ZMod 3139854234712031) ^ 110 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide

private theorem prime_thirtySixAH_34856564291144180525293 : Nat.Prime 34856564291144180525293 := by
  apply lucas_primality 34856564291144180525293 (5 : ZMod 34856564291144180525293)
  · rw [← thirtySixAHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (11, 1), (37, 1), (2273, 1), (3139854234712031, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (11, 1), (37, 1), (2273, 1), (3139854234712031, 1)] : List FactorBlock).map factorBlockValue).prod = 34856564291144180525293 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtySixAH_2
      · exact prime_thirtySixAH_3
      · exact prime_thirtySixAH_11
      · exact prime_thirtySixAH_37
      · exact prime_thirtySixAH_2273
      · exact prime_thirtySixAH_3139854234712031
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 34856564291144180525293) ^ 17428282145572090262646 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (5 : ZMod 34856564291144180525293) ^ 11618854763714726841764 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (5 : ZMod 34856564291144180525293) ^ 3168778571922198229572 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (5 : ZMod 34856564291144180525293) ^ 942069305166058933116 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (5 : ZMod 34856564291144180525293) ^ 15335048082333559404 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (5 : ZMod 34856564291144180525293) ^ 11101332 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide

private theorem prime_thirtySixAH_607 : Nat.Prime 607 := by norm_num
private theorem prime_thirtySixAH_8526929 : Nat.Prime 8526929 := by norm_num
private theorem prime_thirtySixAH_324023303 : Nat.Prime 324023303 := by
  apply lucas_primality 324023303 (5 : ZMod 324023303)
  · rw [← thirtySixAHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (19, 1), (8526929, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (19, 1), (8526929, 1)] : List FactorBlock).map factorBlockValue).prod = 324023303 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtySixAH_2
      · exact prime_thirtySixAH_19
      · exact prime_thirtySixAH_8526929
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 324023303) ^ 162011651 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (5 : ZMod 324023303) ^ 17053858 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (5 : ZMod 324023303) ^ 38 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide

private theorem prime_thirtySixAH_4817 : Nat.Prime 4817 := by norm_num
private theorem prime_thirtySixAH_557 : Nat.Prime 557 := by norm_num
private theorem prime_thirtySixAH_1109 : Nat.Prime 1109 := by norm_num
private theorem prime_thirtySixAH_710369951 : Nat.Prime 710369951 := by
  apply lucas_primality 710369951 (7 : ZMod 710369951)
  · rw [← thirtySixAHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 2), (23, 1), (557, 1), (1109, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 2), (23, 1), (557, 1), (1109, 1)] : List FactorBlock).map factorBlockValue).prod = 710369951 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtySixAH_2
      · exact prime_thirtySixAH_5
      · exact prime_thirtySixAH_23
      · exact prime_thirtySixAH_557
      · exact prime_thirtySixAH_1109
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 710369951) ^ 355184975 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (7 : ZMod 710369951) ^ 142073990 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (7 : ZMod 710369951) ^ 30885650 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (7 : ZMod 710369951) ^ 1275350 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (7 : ZMod 710369951) ^ 640550 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide

private theorem prime_thirtySixAH_4243096546919081 : Nat.Prime 4243096546919081 := by
  apply lucas_primality 4243096546919081 (3 : ZMod 4243096546919081)
  · rw [← thirtySixAHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (5, 1), (31, 1), (4817, 1), (710369951, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (5, 1), (31, 1), (4817, 1), (710369951, 1)] : List FactorBlock).map factorBlockValue).prod = 4243096546919081 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtySixAH_2
      · exact prime_thirtySixAH_5
      · exact prime_thirtySixAH_31
      · exact prime_thirtySixAH_4817
      · exact prime_thirtySixAH_710369951
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 4243096546919081) ^ 2121548273459540 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (3 : ZMod 4243096546919081) ^ 848619309383816 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (3 : ZMod 4243096546919081) ^ 136874082158680 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (3 : ZMod 4243096546919081) ^ 880858739240 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (3 : ZMod 4243096546919081) ^ 5973080 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide

private theorem prime_thirtySixAH_11489 : Nat.Prime 11489 := by norm_num
private theorem prime_thirtySixAH_193 : Nat.Prime 193 := by norm_num
private theorem prime_thirtySixAH_7723 : Nat.Prime 7723 := by norm_num
private theorem prime_thirtySixAH_21580023643 : Nat.Prime 21580023643 := by
  apply lucas_primality 21580023643 (2 : ZMod 21580023643)
  · rw [← thirtySixAHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (19, 1), (127, 1), (193, 1), (7723, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (19, 1), (127, 1), (193, 1), (7723, 1)] : List FactorBlock).map factorBlockValue).prod = 21580023643 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtySixAH_2
      · exact prime_thirtySixAH_3
      · exact prime_thirtySixAH_19
      · exact prime_thirtySixAH_127
      · exact prime_thirtySixAH_193
      · exact prime_thirtySixAH_7723
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 21580023643) ^ 10790011821 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (2 : ZMod 21580023643) ^ 7193341214 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (2 : ZMod 21580023643) ^ 1135790718 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (2 : ZMod 21580023643) ^ 169921446 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (2 : ZMod 21580023643) ^ 111813594 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (2 : ZMod 21580023643) ^ 2794254 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide

private theorem prime_thirtySixAH_167 : Nat.Prime 167 := by norm_num
private theorem prime_thirtySixAH_18679 : Nat.Prime 18679 := by norm_num
private theorem prime_thirtySixAH_77218987 : Nat.Prime 77218987 := by
  apply lucas_primality 77218987 (5 : ZMod 77218987)
  · rw [← thirtySixAHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (13, 1), (53, 1), (18679, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (13, 1), (53, 1), (18679, 1)] : List FactorBlock).map factorBlockValue).prod = 77218987 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtySixAH_2
      · exact prime_thirtySixAH_3
      · exact prime_thirtySixAH_13
      · exact prime_thirtySixAH_53
      · exact prime_thirtySixAH_18679
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 77218987) ^ 38609493 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (5 : ZMod 77218987) ^ 25739662 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (5 : ZMod 77218987) ^ 5939922 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (5 : ZMod 77218987) ^ 1456962 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (5 : ZMod 77218987) ^ 4134 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide

private theorem prime_thirtySixAH_103164566633 : Nat.Prime 103164566633 := by
  apply lucas_primality 103164566633 (3 : ZMod 103164566633)
  · rw [← thirtySixAHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (167, 1), (77218987, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (167, 1), (77218987, 1)] : List FactorBlock).map factorBlockValue).prod = 103164566633 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtySixAH_2
      · exact prime_thirtySixAH_167
      · exact prime_thirtySixAH_77218987
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 103164566633) ^ 51582283316 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (3 : ZMod 103164566633) ^ 617751896 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (3 : ZMod 103164566633) ^ 1336 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide

private theorem prime_thirtySixAH_71241401185919644928609 : Nat.Prime 71241401185919644928609 := by
  apply lucas_primality 71241401185919644928609 (3 : ZMod 71241401185919644928609)
  · rw [← thirtySixAHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 5), (21580023643, 1), (103164566633, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 5), (21580023643, 1), (103164566633, 1)] : List FactorBlock).map factorBlockValue).prod = 71241401185919644928609 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtySixAH_2
      · exact prime_thirtySixAH_21580023643
      · exact prime_thirtySixAH_103164566633
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 71241401185919644928609) ^ 35620700592959822464304 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (3 : ZMod 71241401185919644928609) ^ 3301266132256 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (3 : ZMod 71241401185919644928609) ^ 690560756576 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide

private theorem prime_thirtySixAH_803049204296256634536019201 : Nat.Prime 803049204296256634536019201 := by
  apply lucas_primality 803049204296256634536019201 (67 : ZMod 803049204296256634536019201)
  · rw [← thirtySixAHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 8), (3, 5), (5, 2), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 8), (3, 5), (5, 2), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod = 803049204296256634536019201 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtySixAH_2
      · exact prime_thirtySixAH_3
      · exact prime_thirtySixAH_5
      · exact prime_thirtySixAH_7
      · exact prime_thirtySixAH_11
      · exact prime_thirtySixAH_13
      · exact prime_thirtySixAH_17
      · exact prime_thirtySixAH_19
      · exact prime_thirtySixAH_23
      · exact prime_thirtySixAH_29
      · exact prime_thirtySixAH_31
      · exact prime_thirtySixAH_37
      · exact prime_thirtySixAH_41
      · exact prime_thirtySixAH_43
      · exact prime_thirtySixAH_47
      · exact prime_thirtySixAH_59
      · exact prime_thirtySixAH_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (67 : ZMod 803049204296256634536019201) ^ 401524602148128317268009600 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (67 : ZMod 803049204296256634536019201) ^ 267683068098752211512006400 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (67 : ZMod 803049204296256634536019201) ^ 160609840859251326907203840 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (67 : ZMod 803049204296256634536019201) ^ 114721314899465233505145600 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (67 : ZMod 803049204296256634536019201) ^ 73004473117841512230547200 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (67 : ZMod 803049204296256634536019201) ^ 61773015715096664195078400 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (67 : ZMod 803049204296256634536019201) ^ 47238188488015096149177600 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (67 : ZMod 803049204296256634536019201) ^ 42265747594539822870316800 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (67 : ZMod 803049204296256634536019201) ^ 34915182795489418892870400 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (67 : ZMod 803049204296256634536019201) ^ 27691351872284711535724800 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (67 : ZMod 803049204296256634536019201) ^ 25904813041814730146323200 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (67 : ZMod 803049204296256634536019201) ^ 21704032548547476609081600 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (67 : ZMod 803049204296256634536019201) ^ 19586565958445283769171200 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (67 : ZMod 803049204296256634536019201) ^ 18675562890610619407814400 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (67 : ZMod 803049204296256634536019201) ^ 17086153282899077330553600 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (67 : ZMod 803049204296256634536019201) ^ 13611003462648417534508800 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (67 : ZMod 803049204296256634536019201) ^ 13164741054036994008787200 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide

private theorem prime_thirtySixAH_1483 : Nat.Prime 1483 := by norm_num
private theorem prime_thirtySixAH_2072201 : Nat.Prime 2072201 := by norm_num
private theorem prime_thirtySixAH_2567179 : Nat.Prime 2567179 := by norm_num
private theorem prime_thirtySixAH_811 : Nat.Prime 811 := by norm_num
private theorem prime_thirtySixAH_237308333 : Nat.Prime 237308333 := by
  apply lucas_primality 237308333 (2 : ZMod 237308333)
  · rw [← thirtySixAHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (191, 1), (383, 1), (811, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (191, 1), (383, 1), (811, 1)] : List FactorBlock).map factorBlockValue).prod = 237308333 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtySixAH_2
      · exact prime_thirtySixAH_191
      · exact prime_thirtySixAH_383
      · exact prime_thirtySixAH_811
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 237308333) ^ 118654166 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (2 : ZMod 237308333) ^ 1242452 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (2 : ZMod 237308333) ^ 619604 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (2 : ZMod 237308333) ^ 292612 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide

private theorem prime_thirtySixAH_773847415049120029643800321 : Nat.Prime 773847415049120029643800321 := by
  apply lucas_primality 773847415049120029643800321 (22 : ZMod 773847415049120029643800321)
  · rw [← thirtySixAHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 8), (3, 5), (5, 1), (7, 2), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 8), (3, 5), (5, 1), (7, 2), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod = 773847415049120029643800321 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtySixAH_2
      · exact prime_thirtySixAH_3
      · exact prime_thirtySixAH_5
      · exact prime_thirtySixAH_7
      · exact prime_thirtySixAH_13
      · exact prime_thirtySixAH_17
      · exact prime_thirtySixAH_19
      · exact prime_thirtySixAH_23
      · exact prime_thirtySixAH_29
      · exact prime_thirtySixAH_31
      · exact prime_thirtySixAH_37
      · exact prime_thirtySixAH_41
      · exact prime_thirtySixAH_43
      · exact prime_thirtySixAH_47
      · exact prime_thirtySixAH_53
      · exact prime_thirtySixAH_59
      · exact prime_thirtySixAH_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (22 : ZMod 773847415049120029643800321) ^ 386923707524560014821900160 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (22 : ZMod 773847415049120029643800321) ^ 257949138349706676547933440 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (22 : ZMod 773847415049120029643800321) ^ 154769483009824005928760064 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (22 : ZMod 773847415049120029643800321) ^ 110549630721302861377685760 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (22 : ZMod 773847415049120029643800321) ^ 59526724234547694587984640 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (22 : ZMod 773847415049120029643800321) ^ 45520436179360001743752960 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (22 : ZMod 773847415049120029643800321) ^ 40728811318374738402305280 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (22 : ZMod 773847415049120029643800321) ^ 33645539784744349114947840 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (22 : ZMod 773847415049120029643800321) ^ 26684393622383449298062080 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (22 : ZMod 773847415049120029643800321) ^ 24962819840294194504638720 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (22 : ZMod 773847415049120029643800321) ^ 20914795001327568368751360 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (22 : ZMod 773847415049120029643800321) ^ 18874327196320000723019520 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (22 : ZMod 773847415049120029643800321) ^ 17996451512770233247530240 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (22 : ZMod 773847415049120029643800321) ^ 16464838618066383609442560 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (22 : ZMod 773847415049120029643800321) ^ 14600894623568302446109440 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (22 : ZMod 773847415049120029643800321) ^ 13116057882188475078708480 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (22 : ZMod 773847415049120029643800321) ^ 12686023197526557863013120 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide

private theorem prime_thirtySixAH_76543 : Nat.Prime 76543 := by norm_num
private theorem prime_thirtySixAH_6810796141 : Nat.Prime 6810796141 := by
  apply lucas_primality 6810796141 (2 : ZMod 6810796141)
  · rw [← thirtySixAHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (5, 1), (1483, 1), (76543, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (5, 1), (1483, 1), (76543, 1)] : List FactorBlock).map factorBlockValue).prod = 6810796141 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtySixAH_2
      · exact prime_thirtySixAH_3
      · exact prime_thirtySixAH_5
      · exact prime_thirtySixAH_1483
      · exact prime_thirtySixAH_76543
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 6810796141) ^ 3405398070 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (2 : ZMod 6810796141) ^ 2270265380 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (2 : ZMod 6810796141) ^ 1362159228 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (2 : ZMod 6810796141) ^ 4592580 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (2 : ZMod 6810796141) ^ 88980 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide

private theorem prime_thirtySixAH_55291 : Nat.Prime 55291 := by norm_num
private theorem prime_thirtySixAH_756933791 : Nat.Prime 756933791 := by
  apply lucas_primality 756933791 (11 : ZMod 756933791)
  · rw [← thirtySixAHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 1), (37, 2), (55291, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 1), (37, 2), (55291, 1)] : List FactorBlock).map factorBlockValue).prod = 756933791 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtySixAH_2
      · exact prime_thirtySixAH_5
      · exact prime_thirtySixAH_37
      · exact prime_thirtySixAH_55291
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 756933791) ^ 378466895 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (11 : ZMod 756933791) ^ 151386758 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (11 : ZMod 756933791) ^ 20457670 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (11 : ZMod 756933791) ^ 13690 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide

private theorem prime_thirtySixAH_1513867583 : Nat.Prime 1513867583 := by
  apply lucas_primality 1513867583 (5 : ZMod 1513867583)
  · rw [← thirtySixAHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (756933791, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (756933791, 1)] : List FactorBlock).map factorBlockValue).prod = 1513867583 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_thirtySixAH_2
      · exact prime_thirtySixAH_756933791
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 1513867583) ^ 756933791 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (5 : ZMod 1513867583) ^ 2 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide

private theorem prime_thirtySixAH_108998465977 : Nat.Prime 108998465977 := by
  apply lucas_primality 108998465977 (5 : ZMod 108998465977)
  · rw [← thirtySixAHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (3, 2), (1513867583, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (3, 2), (1513867583, 1)] : List FactorBlock).map factorBlockValue).prod = 108998465977 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtySixAH_2
      · exact prime_thirtySixAH_3
      · exact prime_thirtySixAH_1513867583
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 108998465977) ^ 54499232988 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (5 : ZMod 108998465977) ^ 36332821992 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (5 : ZMod 108998465977) ^ 72 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide

private theorem prime_thirtySixAH_402858330250993 : Nat.Prime 402858330250993 := by
  apply lucas_primality 402858330250993 (5 : ZMod 402858330250993)
  · rw [← thirtySixAHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 4), (3, 1), (7, 1), (11, 1), (108998465977, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 4), (3, 1), (7, 1), (11, 1), (108998465977, 1)] : List FactorBlock).map factorBlockValue).prod = 402858330250993 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtySixAH_2
      · exact prime_thirtySixAH_3
      · exact prime_thirtySixAH_7
      · exact prime_thirtySixAH_11
      · exact prime_thirtySixAH_108998465977
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 402858330250993) ^ 201429165125496 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (5 : ZMod 402858330250993) ^ 134286110083664 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (5 : ZMod 402858330250993) ^ 57551190035856 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (5 : ZMod 402858330250993) ^ 36623484568272 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (5 : ZMod 402858330250993) ^ 3696 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide

private theorem prime_thirtySixAH_119737 : Nat.Prime 119737 := by norm_num
private theorem prime_thirtySixAH_8573 : Nat.Prime 8573 := by norm_num
private theorem prime_thirtySixAH_21706837 : Nat.Prime 21706837 := by
  apply lucas_primality 21706837 (2 : ZMod 21706837)
  · rw [← thirtySixAHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (211, 1), (8573, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (211, 1), (8573, 1)] : List FactorBlock).map factorBlockValue).prod = 21706837 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtySixAH_2
      · exact prime_thirtySixAH_3
      · exact prime_thirtySixAH_211
      · exact prime_thirtySixAH_8573
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 21706837) ^ 10853418 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (2 : ZMod 21706837) ^ 7235612 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (2 : ZMod 21706837) ^ 102876 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (2 : ZMod 21706837) ^ 2532 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide

private theorem prime_thirtySixAH_14467279 : Nat.Prime 14467279 := by norm_num
private theorem prime_thirtySixAH_752298509 : Nat.Prime 752298509 := by
  apply lucas_primality 752298509 (2 : ZMod 752298509)
  · rw [← thirtySixAHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (13, 1), (14467279, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (13, 1), (14467279, 1)] : List FactorBlock).map factorBlockValue).prod = 752298509 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtySixAH_2
      · exact prime_thirtySixAH_13
      · exact prime_thirtySixAH_14467279
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 752298509) ^ 376149254 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (2 : ZMod 752298509) ^ 57869116 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (2 : ZMod 752298509) ^ 52 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide

private theorem prime_thirtySixAH_6131 : Nat.Prime 6131 := by norm_num
private theorem prime_thirtySixAH_344429 : Nat.Prime 344429 := by norm_num
private theorem prime_thirtySixAH_126749873 : Nat.Prime 126749873 := by
  apply lucas_primality 126749873 (3 : ZMod 126749873)
  · rw [← thirtySixAHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 4), (23, 1), (344429, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 4), (23, 1), (344429, 1)] : List FactorBlock).map factorBlockValue).prod = 126749873 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtySixAH_2
      · exact prime_thirtySixAH_23
      · exact prime_thirtySixAH_344429
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 126749873) ^ 63374936 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (3 : ZMod 126749873) ^ 5510864 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (3 : ZMod 126749873) ^ 368 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide

private theorem prime_thirtySixAH_5701 : Nat.Prime 5701 := by norm_num
private theorem prime_thirtySixAH_43541 : Nat.Prime 43541 := by norm_num
private theorem prime_thirtySixAH_634031 : Nat.Prime 634031 := by norm_num
private theorem prime_thirtySixAH_944302595030827 : Nat.Prime 944302595030827 := by
  apply lucas_primality 944302595030827 (2 : ZMod 944302595030827)
  · rw [← thirtySixAHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (5701, 1), (43541, 1), (634031, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (5701, 1), (43541, 1), (634031, 1)] : List FactorBlock).map factorBlockValue).prod = 944302595030827 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtySixAH_2
      · exact prime_thirtySixAH_3
      · exact prime_thirtySixAH_5701
      · exact prime_thirtySixAH_43541
      · exact prime_thirtySixAH_634031
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 944302595030827) ^ 472151297515413 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (2 : ZMod 944302595030827) ^ 314767531676942 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (2 : ZMod 944302595030827) ^ 165638062626 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (2 : ZMod 944302595030827) ^ 21687664386 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (2 : ZMod 944302595030827) ^ 1489363446 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide

private theorem prime_thirtySixAH_3583 : Nat.Prime 3583 := by norm_num
private theorem prime_thirtySixAH_757 : Nat.Prime 757 := by norm_num
private theorem prime_thirtySixAH_1789 : Nat.Prime 1789 := by norm_num
private theorem prime_thirtySixAH_4457 : Nat.Prime 4457 := by norm_num
private theorem prime_thirtySixAH_6733 : Nat.Prime 6733 := by norm_num
private theorem prime_thirtySixAH_10007 : Nat.Prime 10007 := by norm_num
private theorem prime_thirtySixAH_4066880097272106911 : Nat.Prime 4066880097272106911 := by
  apply lucas_primality 4066880097272106911 (11 : ZMod 4066880097272106911)
  · rw [← thirtySixAHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 1), (757, 1), (1789, 1), (4457, 1), (6733, 1), (10007, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 1), (757, 1), (1789, 1), (4457, 1), (6733, 1), (10007, 1)] : List FactorBlock).map factorBlockValue).prod = 4066880097272106911 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtySixAH_2
      · exact prime_thirtySixAH_5
      · exact prime_thirtySixAH_757
      · exact prime_thirtySixAH_1789
      · exact prime_thirtySixAH_4457
      · exact prime_thirtySixAH_6733
      · exact prime_thirtySixAH_10007
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 4066880097272106911) ^ 2033440048636053455 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (11 : ZMod 4066880097272106911) ^ 813376019454421382 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (11 : ZMod 4066880097272106911) ^ 5372364725590630 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (11 : ZMod 4066880097272106911) ^ 2273270037603190 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (11 : ZMod 4066880097272106911) ^ 912470293307630 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (11 : ZMod 4066880097272106911) ^ 604021995733270 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (11 : ZMod 4066880097272106911) ^ 406403527258130 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide

private theorem prime_thirtySixAH_3234902168252762911789087 : Nat.Prime 3234902168252762911789087 := by
  apply lucas_primality 3234902168252762911789087 (13 : ZMod 3234902168252762911789087)
  · rw [← thirtySixAHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (37, 1), (3583, 1), (4066880097272106911, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (37, 1), (3583, 1), (4066880097272106911, 1)] : List FactorBlock).map factorBlockValue).prod = 3234902168252762911789087 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtySixAH_2
      · exact prime_thirtySixAH_3
      · exact prime_thirtySixAH_37
      · exact prime_thirtySixAH_3583
      · exact prime_thirtySixAH_4066880097272106911
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 3234902168252762911789087) ^ 1617451084126381455894543 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (13 : ZMod 3234902168252762911789087) ^ 1078300722750920970596362 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (13 : ZMod 3234902168252762911789087) ^ 87429788331155754372678 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (13 : ZMod 3234902168252762911789087) ^ 902847381594407734242 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (13 : ZMod 3234902168252762911789087) ^ 795426 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide

private theorem prime_thirtySixAH_281 : Nat.Prime 281 := by norm_num
private theorem prime_thirtySixAH_8443 : Nat.Prime 8443 := by norm_num
private theorem prime_thirtySixAH_84294913 : Nat.Prime 84294913 := by
  apply lucas_primality 84294913 (14 : ZMod 84294913)
  · rw [← thirtySixAHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 8), (3, 1), (13, 1), (8443, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 8), (3, 1), (13, 1), (8443, 1)] : List FactorBlock).map factorBlockValue).prod = 84294913 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtySixAH_2
      · exact prime_thirtySixAH_3
      · exact prime_thirtySixAH_13
      · exact prime_thirtySixAH_8443
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (14 : ZMod 84294913) ^ 42147456 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (14 : ZMod 84294913) ^ 28098304 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (14 : ZMod 84294913) ^ 6484224 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (14 : ZMod 84294913) ^ 9984 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide

private theorem prime_thirtySixAH_3540386347 : Nat.Prime 3540386347 := by
  apply lucas_primality 3540386347 (11 : ZMod 3540386347)
  · rw [← thirtySixAHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (7, 1), (84294913, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (7, 1), (84294913, 1)] : List FactorBlock).map factorBlockValue).prod = 3540386347 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtySixAH_2
      · exact prime_thirtySixAH_3
      · exact prime_thirtySixAH_7
      · exact prime_thirtySixAH_84294913
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 3540386347) ^ 1770193173 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (11 : ZMod 3540386347) ^ 1180128782 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (11 : ZMod 3540386347) ^ 505769478 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (11 : ZMod 3540386347) ^ 42 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide

private theorem prime_thirtySixAH_1509031 : Nat.Prime 1509031 := by norm_num
private theorem prime_thirtySixAH_9277522589 : Nat.Prime 9277522589 := by
  apply lucas_primality 9277522589 (2 : ZMod 9277522589)
  · rw [← thirtySixAHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (29, 1), (53, 1), (1509031, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (29, 1), (53, 1), (1509031, 1)] : List FactorBlock).map factorBlockValue).prod = 9277522589 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtySixAH_2
      · exact prime_thirtySixAH_29
      · exact prime_thirtySixAH_53
      · exact prime_thirtySixAH_1509031
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 9277522589) ^ 4638761294 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (2 : ZMod 9277522589) ^ 319914572 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (2 : ZMod 9277522589) ^ 175047596 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (2 : ZMod 9277522589) ^ 6148 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide

private theorem prime_thirtySixAH_964862349257 : Nat.Prime 964862349257 := by
  apply lucas_primality 964862349257 (5 : ZMod 964862349257)
  · rw [← thirtySixAHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (13, 1), (9277522589, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (13, 1), (9277522589, 1)] : List FactorBlock).map factorBlockValue).prod = 964862349257 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtySixAH_2
      · exact prime_thirtySixAH_13
      · exact prime_thirtySixAH_9277522589
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 964862349257) ^ 482431174628 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (5 : ZMod 964862349257) ^ 74220180712 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (5 : ZMod 964862349257) ^ 104 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide

private theorem prime_thirtySixAH_14557 : Nat.Prime 14557 := by norm_num
private theorem prime_thirtySixAH_4044633337 : Nat.Prime 4044633337 := by
  apply lucas_primality 4044633337 (7 : ZMod 4044633337)
  · rw [← thirtySixAHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (3, 2), (17, 1), (227, 1), (14557, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (3, 2), (17, 1), (227, 1), (14557, 1)] : List FactorBlock).map factorBlockValue).prod = 4044633337 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtySixAH_2
      · exact prime_thirtySixAH_3
      · exact prime_thirtySixAH_17
      · exact prime_thirtySixAH_227
      · exact prime_thirtySixAH_14557
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 4044633337) ^ 2022316668 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (7 : ZMod 4044633337) ^ 1348211112 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (7 : ZMod 4044633337) ^ 237919608 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (7 : ZMod 4044633337) ^ 17817768 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (7 : ZMod 4044633337) ^ 277848 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide

private theorem prime_thirtySixAH_1965691801783 : Nat.Prime 1965691801783 := by
  apply lucas_primality 1965691801783 (3 : ZMod 1965691801783)
  · rw [← thirtySixAHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 5), (4044633337, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 5), (4044633337, 1)] : List FactorBlock).map factorBlockValue).prod = 1965691801783 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtySixAH_2
      · exact prime_thirtySixAH_3
      · exact prime_thirtySixAH_4044633337
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 1965691801783) ^ 982845900891 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (3 : ZMod 1965691801783) ^ 655230600594 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (3 : ZMod 1965691801783) ^ 486 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide

private theorem prime_thirtySixAH_701 : Nat.Prime 701 := by norm_num
private theorem prime_thirtySixAH_929 : Nat.Prime 929 := by norm_num
private theorem prime_thirtySixAH_1121509 : Nat.Prime 1121509 := by norm_num
private theorem prime_thirtySixAH_354954563696647 : Nat.Prime 354954563696647 := by
  apply lucas_primality 354954563696647 (13 : ZMod 354954563696647)
  · rw [← thirtySixAHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 5), (701, 1), (929, 1), (1121509, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 5), (701, 1), (929, 1), (1121509, 1)] : List FactorBlock).map factorBlockValue).prod = 354954563696647 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtySixAH_2
      · exact prime_thirtySixAH_3
      · exact prime_thirtySixAH_701
      · exact prime_thirtySixAH_929
      · exact prime_thirtySixAH_1121509
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 354954563696647) ^ 177477281848323 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (13 : ZMod 354954563696647) ^ 118318187898882 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (13 : ZMod 354954563696647) ^ 506354584446 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (13 : ZMod 354954563696647) ^ 382082415174 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (13 : ZMod 354954563696647) ^ 316497294 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide

private theorem prime_thirtySixAH_686477545608090348877564801 : Nat.Prime 686477545608090348877564801 := by
  apply lucas_primality 686477545608090348877564801 (83 : ZMod 686477545608090348877564801)
  · rw [← thirtySixAHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 7), (3, 5), (5, 2), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 7), (3, 5), (5, 2), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod = 686477545608090348877564801 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtySixAH_2
      · exact prime_thirtySixAH_3
      · exact prime_thirtySixAH_5
      · exact prime_thirtySixAH_7
      · exact prime_thirtySixAH_11
      · exact prime_thirtySixAH_13
      · exact prime_thirtySixAH_17
      · exact prime_thirtySixAH_19
      · exact prime_thirtySixAH_23
      · exact prime_thirtySixAH_29
      · exact prime_thirtySixAH_37
      · exact prime_thirtySixAH_41
      · exact prime_thirtySixAH_43
      · exact prime_thirtySixAH_47
      · exact prime_thirtySixAH_53
      · exact prime_thirtySixAH_59
      · exact prime_thirtySixAH_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (83 : ZMod 686477545608090348877564801) ^ 343238772804045174438782400 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (83 : ZMod 686477545608090348877564801) ^ 228825848536030116292521600 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (83 : ZMod 686477545608090348877564801) ^ 137295509121618069775512960 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (83 : ZMod 686477545608090348877564801) ^ 98068220801155764125366400 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (83 : ZMod 686477545608090348877564801) ^ 62407049600735486261596800 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (83 : ZMod 686477545608090348877564801) ^ 52805965046776180682889600 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (83 : ZMod 686477545608090348877564801) ^ 40381032094593549933974400 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (83 : ZMod 686477545608090348877564801) ^ 36130397137267913098819200 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (83 : ZMod 686477545608090348877564801) ^ 29846849809047406472937600 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (83 : ZMod 686477545608090348877564801) ^ 23671639503727253409571200 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (83 : ZMod 686477545608090348877564801) ^ 18553447178597036456150400 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (83 : ZMod 686477545608090348877564801) ^ 16743354770929032899452800 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (83 : ZMod 686477545608090348877564801) ^ 15964594083909077880873600 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (83 : ZMod 686477545608090348877564801) ^ 14605905225704049976118400 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (83 : ZMod 686477545608090348877564801) ^ 12952406520907365073161600 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (83 : ZMod 686477545608090348877564801) ^ 11635212637425260150467200 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (83 : ZMod 686477545608090348877564801) ^ 11253730255870333588156800 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide

private theorem prime_thirtySixAH_1087 : Nat.Prime 1087 := by norm_num
private theorem prime_thirtySixAH_3061 : Nat.Prime 3061 := by norm_num
private theorem prime_thirtySixAH_61379 : Nat.Prime 61379 := by norm_num
private theorem prime_thirtySixAH_382747 : Nat.Prime 382747 := by norm_num
private theorem prime_thirtySixAH_163987 : Nat.Prime 163987 := by norm_num
private theorem prime_thirtySixAH_1440461809 : Nat.Prime 1440461809 := by
  apply lucas_primality 1440461809 (7 : ZMod 1440461809)
  · rw [← thirtySixAHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 4), (3, 2), (61, 1), (163987, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 4), (3, 2), (61, 1), (163987, 1)] : List FactorBlock).map factorBlockValue).prod = 1440461809 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtySixAH_2
      · exact prime_thirtySixAH_3
      · exact prime_thirtySixAH_61
      · exact prime_thirtySixAH_163987
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 1440461809) ^ 720230904 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (7 : ZMod 1440461809) ^ 480153936 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (7 : ZMod 1440461809) ^ 23614128 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (7 : ZMod 1440461809) ^ 8784 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide

private theorem prime_thirtySixAH_621509730110564998034623 : Nat.Prime 621509730110564998034623 := by
  apply lucas_primality 621509730110564998034623 (5 : ZMod 621509730110564998034623)
  · rw [← thirtySixAHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (3061, 1), (61379, 1), (382747, 1), (1440461809, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (3061, 1), (61379, 1), (382747, 1), (1440461809, 1)] : List FactorBlock).map factorBlockValue).prod = 621509730110564998034623 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtySixAH_2
      · exact prime_thirtySixAH_3
      · exact prime_thirtySixAH_3061
      · exact prime_thirtySixAH_61379
      · exact prime_thirtySixAH_382747
      · exact prime_thirtySixAH_1440461809
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 621509730110564998034623) ^ 310754865055282499017311 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (5 : ZMod 621509730110564998034623) ^ 207169910036854999344874 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (5 : ZMod 621509730110564998034623) ^ 203041401538897418502 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (5 : ZMod 621509730110564998034623) ^ 10125771519747226218 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (5 : ZMod 621509730110564998034623) ^ 1623813459310105626 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (5 : ZMod 621509730110564998034623) ^ 431465607923358 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide

private theorem prime_thirtySixAH_25913 : Nat.Prime 25913 := by norm_num
private theorem prime_thirtySixAH_79 : Nat.Prime 79 := by norm_num
private theorem prime_thirtySixAH_644701 : Nat.Prime 644701 := by norm_num
private theorem prime_thirtySixAH_1731666887 : Nat.Prime 1731666887 := by
  apply lucas_primality 1731666887 (5 : ZMod 1731666887)
  · rw [← thirtySixAHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (17, 1), (79, 1), (644701, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (17, 1), (79, 1), (644701, 1)] : List FactorBlock).map factorBlockValue).prod = 1731666887 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtySixAH_2
      · exact prime_thirtySixAH_17
      · exact prime_thirtySixAH_79
      · exact prime_thirtySixAH_644701
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 1731666887) ^ 865833443 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (5 : ZMod 1731666887) ^ 101862758 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (5 : ZMod 1731666887) ^ 21919834 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (5 : ZMod 1731666887) ^ 2686 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide

private theorem prime_thirtySixAH_9281 : Nat.Prime 9281 := by norm_num
private theorem prime_thirtySixAH_7603997 : Nat.Prime 7603997 := by norm_num
private theorem prime_thirtySixAH_14820266192971 : Nat.Prime 14820266192971 := by
  apply lucas_primality 14820266192971 (3 : ZMod 14820266192971)
  · rw [← thirtySixAHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (5, 1), (7, 1), (9281, 1), (7603997, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (5, 1), (7, 1), (9281, 1), (7603997, 1)] : List FactorBlock).map factorBlockValue).prod = 14820266192971 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtySixAH_2
      · exact prime_thirtySixAH_3
      · exact prime_thirtySixAH_5
      · exact prime_thirtySixAH_7
      · exact prime_thirtySixAH_9281
      · exact prime_thirtySixAH_7603997
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 14820266192971) ^ 7410133096485 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (3 : ZMod 14820266192971) ^ 4940088730990 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (3 : ZMod 14820266192971) ^ 2964053238594 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (3 : ZMod 14820266192971) ^ 2117180884710 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (3 : ZMod 14820266192971) ^ 1596839370 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (3 : ZMod 14820266192971) ^ 1949010 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide

private theorem prime_thirtySixAH_16103797 : Nat.Prime 16103797 := by norm_num
private theorem prime_thirtySixAH_161037971 : Nat.Prime 161037971 := by
  apply lucas_primality 161037971 (2 : ZMod 161037971)
  · rw [← thirtySixAHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 1), (16103797, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 1), (16103797, 1)] : List FactorBlock).map factorBlockValue).prod = 161037971 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtySixAH_2
      · exact prime_thirtySixAH_5
      · exact prime_thirtySixAH_16103797
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 161037971) ^ 80518985 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (2 : ZMod 161037971) ^ 32207594 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (2 : ZMod 161037971) ^ 10 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide

private theorem prime_thirtySixAH_967 : Nat.Prime 967 := by norm_num
private theorem prime_thirtySixAH_517189 : Nat.Prime 517189 := by norm_num
private theorem prime_thirtySixAH_57268793044601101 : Nat.Prime 57268793044601101 := by
  apply lucas_primality 57268793044601101 (2 : ZMod 57268793044601101)
  · rw [← thirtySixAHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 4), (5, 2), (67, 1), (211, 1), (967, 1), (517189, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 4), (5, 2), (67, 1), (211, 1), (967, 1), (517189, 1)] : List FactorBlock).map factorBlockValue).prod = 57268793044601101 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtySixAH_2
      · exact prime_thirtySixAH_3
      · exact prime_thirtySixAH_5
      · exact prime_thirtySixAH_67
      · exact prime_thirtySixAH_211
      · exact prime_thirtySixAH_967
      · exact prime_thirtySixAH_517189
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 57268793044601101) ^ 28634396522300550 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (2 : ZMod 57268793044601101) ^ 19089597681533700 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (2 : ZMod 57268793044601101) ^ 11453758608920220 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (2 : ZMod 57268793044601101) ^ 854758105143300 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (2 : ZMod 57268793044601101) ^ 271416080780100 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (2 : ZMod 57268793044601101) ^ 59223157233300 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (2 : ZMod 57268793044601101) ^ 110730879900 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide

private theorem prime_thirtySixAH_97327 : Nat.Prime 97327 := by norm_num
private theorem prime_thirtySixAH_208223 : Nat.Prime 208223 := by norm_num
private theorem prime_thirtySixAH_4129087 : Nat.Prime 4129087 := by norm_num
private theorem prime_thirtySixAH_1929523 : Nat.Prime 1929523 := by norm_num
private theorem prime_thirtySixAH_7706514863 : Nat.Prime 7706514863 := by
  apply lucas_primality 7706514863 (5 : ZMod 7706514863)
  · rw [← thirtySixAHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (1997, 1), (1929523, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (1997, 1), (1929523, 1)] : List FactorBlock).map factorBlockValue).prod = 7706514863 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtySixAH_2
      · exact prime_thirtySixAH_1997
      · exact prime_thirtySixAH_1929523
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 7706514863) ^ 3853257431 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (5 : ZMod 7706514863) ^ 3859046 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (5 : ZMod 7706514863) ^ 3994 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide

private theorem prime_thirtySixAH_508033 : Nat.Prime 508033 := by norm_num
private theorem prime_thirtySixAH_5191489 : Nat.Prime 5191489 := by norm_num
private theorem prime_thirtySixAH_5873239 : Nat.Prime 5873239 := by norm_num
private theorem prime_thirtySixAH_890927 : Nat.Prime 890927 := by norm_num
private theorem prime_thirtySixAH_2747618869 : Nat.Prime 2747618869 := by
  apply lucas_primality 2747618869 (2 : ZMod 2747618869)
  · rw [← thirtySixAHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (257, 1), (890927, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (257, 1), (890927, 1)] : List FactorBlock).map factorBlockValue).prod = 2747618869 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtySixAH_2
      · exact prime_thirtySixAH_3
      · exact prime_thirtySixAH_257
      · exact prime_thirtySixAH_890927
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 2747618869) ^ 1373809434 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (2 : ZMod 2747618869) ^ 915872956 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (2 : ZMod 2747618869) ^ 10691124 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (2 : ZMod 2747618869) ^ 3084 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide

private theorem prime_thirtySixAH_625905997466200023976603201 : Nat.Prime 625905997466200023976603201 := by
  apply lucas_primality 625905997466200023976603201 (79 : ZMod 625905997466200023976603201)
  · rw [← thirtySixAHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 6), (3, 5), (5, 2), (7, 2), (11, 1), (13, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 6), (3, 5), (5, 2), (7, 2), (11, 1), (13, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod = 625905997466200023976603201 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtySixAH_2
      · exact prime_thirtySixAH_3
      · exact prime_thirtySixAH_5
      · exact prime_thirtySixAH_7
      · exact prime_thirtySixAH_11
      · exact prime_thirtySixAH_13
      · exact prime_thirtySixAH_19
      · exact prime_thirtySixAH_23
      · exact prime_thirtySixAH_29
      · exact prime_thirtySixAH_31
      · exact prime_thirtySixAH_37
      · exact prime_thirtySixAH_41
      · exact prime_thirtySixAH_43
      · exact prime_thirtySixAH_47
      · exact prime_thirtySixAH_53
      · exact prime_thirtySixAH_59
      · exact prime_thirtySixAH_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (79 : ZMod 625905997466200023976603201) ^ 312952998733100011988301600 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (79 : ZMod 625905997466200023976603201) ^ 208635332488733341325534400 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (79 : ZMod 625905997466200023976603201) ^ 125181199493240004795320640 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (79 : ZMod 625905997466200023976603201) ^ 89415142495171431996657600 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (79 : ZMod 625905997466200023976603201) ^ 56900545224200002179691200 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (79 : ZMod 625905997466200023976603201) ^ 48146615189707694152046400 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (79 : ZMod 625905997466200023976603201) ^ 32942420919273685472452800 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (79 : ZMod 625905997466200023976603201) ^ 27213304237660870607678400 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (79 : ZMod 625905997466200023976603201) ^ 21582965429868966344020800 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (79 : ZMod 625905997466200023976603201) ^ 20190516047296774966987200 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (79 : ZMod 625905997466200023976603201) ^ 16916378309897297945313600 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (79 : ZMod 625905997466200023976603201) ^ 15265999938200000584795200 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (79 : ZMod 625905997466200023976603201) ^ 14555953429446512185502400 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (79 : ZMod 625905997466200023976603201) ^ 13317148882259574978225600 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (79 : ZMod 625905997466200023976603201) ^ 11809547122003774037294400 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (79 : ZMod 625905997466200023976603201) ^ 10608576228240678372484800 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (79 : ZMod 625905997466200023976603201) ^ 10260754056822951212731200 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide

private theorem prime_thirtySixAH_449 : Nat.Prime 449 := by norm_num
private theorem prime_thirtySixAH_128239 : Nat.Prime 128239 := by norm_num
private theorem prime_thirtySixAH_4613533 : Nat.Prime 4613533 := by norm_num
private theorem prime_thirtySixAH_73816529 : Nat.Prime 73816529 := by
  apply lucas_primality 73816529 (3 : ZMod 73816529)
  · rw [← thirtySixAHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 4), (4613533, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 4), (4613533, 1)] : List FactorBlock).map factorBlockValue).prod = 73816529 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_thirtySixAH_2
      · exact prime_thirtySixAH_4613533
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 73816529) ^ 36908264 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (3 : ZMod 73816529) ^ 16 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide

private theorem prime_thirtySixAH_3209 : Nat.Prime 3209 := by norm_num
private theorem prime_thirtySixAH_40597 : Nat.Prime 40597 := by norm_num
private theorem prime_thirtySixAH_260551547 : Nat.Prime 260551547 := by
  apply lucas_primality 260551547 (2 : ZMod 260551547)
  · rw [← thirtySixAHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3209, 1), (40597, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3209, 1), (40597, 1)] : List FactorBlock).map factorBlockValue).prod = 260551547 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtySixAH_2
      · exact prime_thirtySixAH_3209
      · exact prime_thirtySixAH_40597
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 260551547) ^ 130275773 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (2 : ZMod 260551547) ^ 81194 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (2 : ZMod 260551547) ^ 6418 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide

private theorem prime_thirtySixAH_33493 : Nat.Prime 33493 := by norm_num
private theorem prime_thirtySixAH_50587 : Nat.Prime 50587 := by norm_num
private theorem prime_thirtySixAH_197 : Nat.Prime 197 := by norm_num
private theorem prime_thirtySixAH_613 : Nat.Prime 613 := by norm_num
private theorem prime_thirtySixAH_3301 : Nat.Prime 3301 := by norm_num
private theorem prime_thirtySixAH_1784738467 : Nat.Prime 1784738467 := by
  apply lucas_primality 1784738467 (3 : ZMod 1784738467)
  · rw [← thirtySixAHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 2), (7, 2), (613, 1), (3301, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 2), (7, 2), (613, 1), (3301, 1)] : List FactorBlock).map factorBlockValue).prod = 1784738467 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtySixAH_2
      · exact prime_thirtySixAH_3
      · exact prime_thirtySixAH_7
      · exact prime_thirtySixAH_613
      · exact prime_thirtySixAH_3301
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1784738467) ^ 892369233 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (3 : ZMod 1784738467) ^ 594912822 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (3 : ZMod 1784738467) ^ 254962638 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (3 : ZMod 1784738467) ^ 2911482 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (3 : ZMod 1784738467) ^ 540666 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide

private theorem prime_thirtySixAH_28555815473 : Nat.Prime 28555815473 := by
  apply lucas_primality 28555815473 (3 : ZMod 28555815473)
  · rw [← thirtySixAHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 4), (1784738467, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 4), (1784738467, 1)] : List FactorBlock).map factorBlockValue).prod = 28555815473 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_thirtySixAH_2
      · exact prime_thirtySixAH_1784738467
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 28555815473) ^ 14277907736 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (3 : ZMod 28555815473) ^ 16 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide

private theorem prime_thirtySixAH_67505947778173 : Nat.Prime 67505947778173 := by
  apply lucas_primality 67505947778173 (2 : ZMod 67505947778173)
  · rw [← thirtySixAHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (197, 1), (28555815473, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (197, 1), (28555815473, 1)] : List FactorBlock).map factorBlockValue).prod = 67505947778173 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtySixAH_2
      · exact prime_thirtySixAH_3
      · exact prime_thirtySixAH_197
      · exact prime_thirtySixAH_28555815473
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 67505947778173) ^ 33752973889086 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (2 : ZMod 67505947778173) ^ 22501982592724 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (2 : ZMod 67505947778173) ^ 342669785676 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (2 : ZMod 67505947778173) ^ 2364 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide

private theorem prime_thirtySixAH_18153732689432590021117 : Nat.Prime 18153732689432590021117 := by
  apply lucas_primality 18153732689432590021117 (2 : ZMod 18153732689432590021117)
  · rw [← thirtySixAHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (443, 1), (50587, 1), (67505947778173, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (443, 1), (50587, 1), (67505947778173, 1)] : List FactorBlock).map factorBlockValue).prod = 18153732689432590021117 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtySixAH_2
      · exact prime_thirtySixAH_3
      · exact prime_thirtySixAH_443
      · exact prime_thirtySixAH_50587
      · exact prime_thirtySixAH_67505947778173
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 18153732689432590021117) ^ 9076866344716295010558 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (2 : ZMod 18153732689432590021117) ^ 6051244229810863340372 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (2 : ZMod 18153732689432590021117) ^ 40979080563053250612 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (2 : ZMod 18153732689432590021117) ^ 358861618388767668 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (2 : ZMod 18153732689432590021117) ^ 268920492 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide

private theorem prime_thirtySixAH_433 : Nat.Prime 433 := by norm_num
private theorem prime_thirtySixAH_7043 : Nat.Prime 7043 := by norm_num
private theorem prime_thirtySixAH_552179 : Nat.Prime 552179 := by norm_num
private theorem prime_thirtySixAH_1997617 : Nat.Prime 1997617 := by norm_num
private theorem prime_thirtySixAH_10009981 : Nat.Prime 10009981 := by norm_num
private theorem prime_thirtySixAH_160159697 : Nat.Prime 160159697 := by
  apply lucas_primality 160159697 (3 : ZMod 160159697)
  · rw [← thirtySixAHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 4), (10009981, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 4), (10009981, 1)] : List FactorBlock).map factorBlockValue).prod = 160159697 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_thirtySixAH_2
      · exact prime_thirtySixAH_10009981
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 160159697) ^ 80079848 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (3 : ZMod 160159697) ^ 16 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide

private theorem prime_thirtySixAH_37309 : Nat.Prime 37309 := by norm_num
private theorem prime_thirtySixAH_1222615931 : Nat.Prime 1222615931 := by
  apply lucas_primality 1222615931 (2 : ZMod 1222615931)
  · rw [← thirtySixAHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 1), (29, 1), (113, 1), (37309, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 1), (29, 1), (113, 1), (37309, 1)] : List FactorBlock).map factorBlockValue).prod = 1222615931 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtySixAH_2
      · exact prime_thirtySixAH_5
      · exact prime_thirtySixAH_29
      · exact prime_thirtySixAH_113
      · exact prime_thirtySixAH_37309
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1222615931) ^ 611307965 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (2 : ZMod 1222615931) ^ 244523186 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (2 : ZMod 1222615931) ^ 42159170 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (2 : ZMod 1222615931) ^ 10819610 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (2 : ZMod 1222615931) ^ 32770 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide

private theorem prime_thirtySixAH_2531 : Nat.Prime 2531 := by norm_num
private theorem prime_thirtySixAH_6763 : Nat.Prime 6763 := by norm_num
private theorem prime_thirtySixAH_462094662389 : Nat.Prime 462094662389 := by
  apply lucas_primality 462094662389 (2 : ZMod 462094662389)
  · rw [← thirtySixAHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (17, 1), (397, 1), (2531, 1), (6763, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (17, 1), (397, 1), (2531, 1), (6763, 1)] : List FactorBlock).map factorBlockValue).prod = 462094662389 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtySixAH_2
      · exact prime_thirtySixAH_17
      · exact prime_thirtySixAH_397
      · exact prime_thirtySixAH_2531
      · exact prime_thirtySixAH_6763
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 462094662389) ^ 231047331194 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (2 : ZMod 462094662389) ^ 27182038964 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (2 : ZMod 462094662389) ^ 1163966404 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (2 : ZMod 462094662389) ^ 182573948 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (2 : ZMod 462094662389) ^ 68326876 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide

private theorem prime_thirtySixAH_1667237541899513 : Nat.Prime 1667237541899513 := by
  apply lucas_primality 1667237541899513 (3 : ZMod 1667237541899513)
  · rw [← thirtySixAHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (11, 1), (41, 1), (462094662389, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (11, 1), (41, 1), (462094662389, 1)] : List FactorBlock).map factorBlockValue).prod = 1667237541899513 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtySixAH_2
      · exact prime_thirtySixAH_11
      · exact prime_thirtySixAH_41
      · exact prime_thirtySixAH_462094662389
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1667237541899513) ^ 833618770949756 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (3 : ZMod 1667237541899513) ^ 151567049263592 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (3 : ZMod 1667237541899513) ^ 40664330290232 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (3 : ZMod 1667237541899513) ^ 3608 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide

private theorem prime_thirtySixAH_483498887150858771 : Nat.Prime 483498887150858771 := by
  apply lucas_primality 483498887150858771 (2 : ZMod 483498887150858771)
  · rw [← thirtySixAHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 1), (29, 1), (1667237541899513, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 1), (29, 1), (1667237541899513, 1)] : List FactorBlock).map factorBlockValue).prod = 483498887150858771 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtySixAH_2
      · exact prime_thirtySixAH_5
      · exact prime_thirtySixAH_29
      · exact prime_thirtySixAH_1667237541899513
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 483498887150858771) ^ 241749443575429385 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (2 : ZMod 483498887150858771) ^ 96699777430171754 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (2 : ZMod 483498887150858771) ^ 16672375418995130 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (2 : ZMod 483498887150858771) ^ 290 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide

private theorem prime_thirtySixAH_1009 : Nat.Prime 1009 := by norm_num
private theorem prime_thirtySixAH_15227 : Nat.Prime 15227 := by norm_num
private theorem prime_thirtySixAH_17443 : Nat.Prime 17443 := by norm_num
private theorem prime_thirtySixAH_2846009 : Nat.Prime 2846009 := by norm_num
private theorem prime_thirtySixAH_1187089 : Nat.Prime 1187089 := by norm_num
private theorem prime_thirtySixAH_61728629 : Nat.Prime 61728629 := by
  apply lucas_primality 61728629 (2 : ZMod 61728629)
  · rw [← thirtySixAHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (13, 1), (1187089, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (13, 1), (1187089, 1)] : List FactorBlock).map factorBlockValue).prod = 61728629 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtySixAH_2
      · exact prime_thirtySixAH_13
      · exact prime_thirtySixAH_1187089
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 61728629) ^ 30864314 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (2 : ZMod 61728629) ^ 4748356 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (2 : ZMod 61728629) ^ 52 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide

private theorem prime_thirtySixAH_373291770768408234126569 : Nat.Prime 373291770768408234126569 := by
  apply lucas_primality 373291770768408234126569 (3 : ZMod 373291770768408234126569)
  · rw [← thirtySixAHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (15227, 1), (17443, 1), (2846009, 1), (61728629, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (15227, 1), (17443, 1), (2846009, 1), (61728629, 1)] : List FactorBlock).map factorBlockValue).prod = 373291770768408234126569 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtySixAH_2
      · exact prime_thirtySixAH_15227
      · exact prime_thirtySixAH_17443
      · exact prime_thirtySixAH_2846009
      · exact prime_thirtySixAH_61728629
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 373291770768408234126569) ^ 186645885384204117063284 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (3 : ZMod 373291770768408234126569) ^ 24515122530269142584 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (3 : ZMod 373291770768408234126569) ^ 21400663347383376376 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (3 : ZMod 373291770768408234126569) ^ 131163243253414952 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (3 : ZMod 373291770768408234126569) ^ 6047303768376392 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide

private theorem prime_thirtySixAH_28463 : Nat.Prime 28463 := by norm_num
private theorem prime_thirtySixAH_100103 : Nat.Prime 100103 := by norm_num
private theorem prime_thirtySixAH_546353 : Nat.Prime 546353 := by norm_num
private theorem prime_thirtySixAH_5119 : Nat.Prime 5119 := by norm_num
private theorem prime_thirtySixAH_6449 : Nat.Prime 6449 := by norm_num
private theorem prime_thirtySixAH_369475127753 : Nat.Prime 369475127753 := by
  apply lucas_primality 369475127753 (3 : ZMod 369475127753)
  · rw [← thirtySixAHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (1399, 1), (5119, 1), (6449, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (1399, 1), (5119, 1), (6449, 1)] : List FactorBlock).map factorBlockValue).prod = 369475127753 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtySixAH_2
      · exact prime_thirtySixAH_1399
      · exact prime_thirtySixAH_5119
      · exact prime_thirtySixAH_6449
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 369475127753) ^ 184737563876 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (3 : ZMod 369475127753) ^ 264099448 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (3 : ZMod 369475127753) ^ 72177208 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (3 : ZMod 369475127753) ^ 57291848 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide

private theorem prime_thirtySixAH_65129 : Nat.Prime 65129 := by norm_num
private theorem prime_thirtySixAH_182467 : Nat.Prime 182467 := by norm_num
private theorem prime_thirtySixAH_2207 : Nat.Prime 2207 := by norm_num
private theorem prime_thirtySixAH_5400053 : Nat.Prime 5400053 := by norm_num
private theorem prime_thirtySixAH_170545391855011 : Nat.Prime 170545391855011 := by
  apply lucas_primality 170545391855011 (2 : ZMod 170545391855011)
  · rw [← thirtySixAHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 3), (5, 1), (53, 1), (2207, 1), (5400053, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 3), (5, 1), (53, 1), (2207, 1), (5400053, 1)] : List FactorBlock).map factorBlockValue).prod = 170545391855011 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtySixAH_2
      · exact prime_thirtySixAH_3
      · exact prime_thirtySixAH_5
      · exact prime_thirtySixAH_53
      · exact prime_thirtySixAH_2207
      · exact prime_thirtySixAH_5400053
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 170545391855011) ^ 85272695927505 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (2 : ZMod 170545391855011) ^ 56848463951670 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (2 : ZMod 170545391855011) ^ 34109078371002 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (2 : ZMod 170545391855011) ^ 3217837582170 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (2 : ZMod 170545391855011) ^ 77274758430 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (2 : ZMod 170545391855011) ^ 31582170 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide

private theorem prime_thirtySixAH_8713293684370321798361 : Nat.Prime 8713293684370321798361 := by
  apply lucas_primality 8713293684370321798361 (3 : ZMod 8713293684370321798361)
  · rw [← thirtySixAHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (5, 1), (7, 1), (182467, 1), (170545391855011, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (5, 1), (7, 1), (182467, 1), (170545391855011, 1)] : List FactorBlock).map factorBlockValue).prod = 8713293684370321798361 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtySixAH_2
      · exact prime_thirtySixAH_5
      · exact prime_thirtySixAH_7
      · exact prime_thirtySixAH_182467
      · exact prime_thirtySixAH_170545391855011
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 8713293684370321798361) ^ 4356646842185160899180 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (3 : ZMod 8713293684370321798361) ^ 1742658736874064359672 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (3 : ZMod 8713293684370321798361) ^ 1244756240624331685480 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (3 : ZMod 8713293684370321798361) ^ 47752709719403080 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (3 : ZMod 8713293684370321798361) ^ 51090760 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide

private theorem prime_thirtySixAH_3691 : Nat.Prime 3691 := by norm_num
private theorem prime_thirtySixAH_401987 : Nat.Prime 401987 := by norm_num
private theorem prime_thirtySixAH_86843 : Nat.Prime 86843 := by norm_num
private theorem prime_thirtySixAH_171877 : Nat.Prime 171877 := by norm_num
private theorem prime_thirtySixAH_3074820748067 : Nat.Prime 3074820748067 := by
  apply lucas_primality 3074820748067 (2 : ZMod 3074820748067)
  · rw [← thirtySixAHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (103, 1), (86843, 1), (171877, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (103, 1), (86843, 1), (171877, 1)] : List FactorBlock).map factorBlockValue).prod = 3074820748067 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtySixAH_2
      · exact prime_thirtySixAH_103
      · exact prime_thirtySixAH_86843
      · exact prime_thirtySixAH_171877
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 3074820748067) ^ 1537410374033 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (2 : ZMod 3074820748067) ^ 29852628622 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (2 : ZMod 3074820748067) ^ 35406662 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (2 : ZMod 3074820748067) ^ 17889658 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide

private theorem prime_thirtySixAH_43047490472939 : Nat.Prime 43047490472939 := by
  apply lucas_primality 43047490472939 (7 : ZMod 43047490472939)
  · rw [← thirtySixAHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (7, 1), (3074820748067, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (7, 1), (3074820748067, 1)] : List FactorBlock).map factorBlockValue).prod = 43047490472939 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtySixAH_2
      · exact prime_thirtySixAH_7
      · exact prime_thirtySixAH_3074820748067
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 43047490472939) ^ 21523745236469 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (7 : ZMod 43047490472939) ^ 6149641496134 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (7 : ZMod 43047490472939) ^ 14 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide

private theorem prime_thirtySixAH_377440396466729153 : Nat.Prime 377440396466729153 := by
  apply lucas_primality 377440396466729153 (3 : ZMod 377440396466729153)
  · rw [← thirtySixAHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 6), (137, 1), (43047490472939, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 6), (137, 1), (43047490472939, 1)] : List FactorBlock).map factorBlockValue).prod = 377440396466729153 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtySixAH_2
      · exact prime_thirtySixAH_137
      · exact prime_thirtySixAH_43047490472939
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 377440396466729153) ^ 188720198233364576 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (3 : ZMod 377440396466729153) ^ 2755039390268096 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (3 : ZMod 377440396466729153) ^ 8768 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide

private theorem prime_thirtySixAH_353 : Nat.Prime 353 := by norm_num
private theorem prime_thirtySixAH_2267 : Nat.Prime 2267 := by norm_num
private theorem prime_thirtySixAH_22407029 : Nat.Prime 22407029 := by
  apply lucas_primality 22407029 (2 : ZMod 22407029)
  · rw [← thirtySixAHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (7, 1), (353, 1), (2267, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (7, 1), (353, 1), (2267, 1)] : List FactorBlock).map factorBlockValue).prod = 22407029 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtySixAH_2
      · exact prime_thirtySixAH_7
      · exact prime_thirtySixAH_353
      · exact prime_thirtySixAH_2267
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 22407029) ^ 11203514 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (2 : ZMod 22407029) ^ 3201004 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (2 : ZMod 22407029) ^ 63476 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (2 : ZMod 22407029) ^ 9884 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide

private theorem prime_thirtySixAH_985909277 : Nat.Prime 985909277 := by
  apply lucas_primality 985909277 (3 : ZMod 985909277)
  · rw [← thirtySixAHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (11, 1), (22407029, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (11, 1), (22407029, 1)] : List FactorBlock).map factorBlockValue).prod = 985909277 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtySixAH_2
      · exact prime_thirtySixAH_11
      · exact prime_thirtySixAH_22407029
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 985909277) ^ 492954638 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (3 : ZMod 985909277) ^ 89628116 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (3 : ZMod 985909277) ^ 44 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide

private theorem prime_thirtySixAH_109751 : Nat.Prime 109751 := by norm_num
private theorem prime_thirtySixAH_199172033 : Nat.Prime 199172033 := by
  apply lucas_primality 199172033 (3 : ZMod 199172033)
  · rw [← thirtySixAHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 6), (73, 1), (89, 1), (479, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 6), (73, 1), (89, 1), (479, 1)] : List FactorBlock).map factorBlockValue).prod = 199172033 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtySixAH_2
      · exact prime_thirtySixAH_73
      · exact prime_thirtySixAH_89
      · exact prime_thirtySixAH_479
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 199172033) ^ 99586016 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (3 : ZMod 199172033) ^ 2728384 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (3 : ZMod 199172033) ^ 2237888 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (3 : ZMod 199172033) ^ 415808 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide

private theorem prime_thirtySixAH_2448244936903697 : Nat.Prime 2448244936903697 := by
  apply lucas_primality 2448244936903697 (3 : ZMod 2448244936903697)
  · rw [← thirtySixAHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 4), (7, 1), (109751, 1), (199172033, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 4), (7, 1), (109751, 1), (199172033, 1)] : List FactorBlock).map factorBlockValue).prod = 2448244936903697 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtySixAH_2
      · exact prime_thirtySixAH_7
      · exact prime_thirtySixAH_109751
      · exact prime_thirtySixAH_199172033
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 2448244936903697) ^ 1224122468451848 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (3 : ZMod 2448244936903697) ^ 349749276700528 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (3 : ZMod 2448244936903697) ^ 22307267696 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (3 : ZMod 2448244936903697) ^ 12292112 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide

private theorem prime_thirtySixAH_545661638816687200389859201 : Nat.Prime 545661638816687200389859201 := by
  apply lucas_primality 545661638816687200389859201 (13 : ZMod 545661638816687200389859201)
  · rw [← thirtySixAHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 7), (3, 4), (5, 2), (7, 2), (11, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 7), (3, 4), (5, 2), (7, 2), (11, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod = 545661638816687200389859201 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtySixAH_2
      · exact prime_thirtySixAH_3
      · exact prime_thirtySixAH_5
      · exact prime_thirtySixAH_7
      · exact prime_thirtySixAH_11
      · exact prime_thirtySixAH_17
      · exact prime_thirtySixAH_19
      · exact prime_thirtySixAH_23
      · exact prime_thirtySixAH_29
      · exact prime_thirtySixAH_31
      · exact prime_thirtySixAH_37
      · exact prime_thirtySixAH_41
      · exact prime_thirtySixAH_43
      · exact prime_thirtySixAH_47
      · exact prime_thirtySixAH_53
      · exact prime_thirtySixAH_59
      · exact prime_thirtySixAH_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 545661638816687200389859201) ^ 272830819408343600194929600 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (13 : ZMod 545661638816687200389859201) ^ 181887212938895733463286400 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (13 : ZMod 545661638816687200389859201) ^ 109132327763337440077971840 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (13 : ZMod 545661638816687200389859201) ^ 77951662688098171484265600 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (13 : ZMod 545661638816687200389859201) ^ 49605603528789745489987200 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (13 : ZMod 545661638816687200389859201) ^ 32097743459805129434697600 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (13 : ZMod 545661638816687200389859201) ^ 28719033621930905283676800 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (13 : ZMod 545661638816687200389859201) ^ 23724419078986400016950400 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (13 : ZMod 545661638816687200389859201) ^ 18815918579885765530684800 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (13 : ZMod 545661638816687200389859201) ^ 17601988348925393560963200 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (13 : ZMod 545661638816687200389859201) ^ 14747611859910464875401600 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (13 : ZMod 545661638816687200389859201) ^ 13308820458943590253411200 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (13 : ZMod 545661638816687200389859201) ^ 12689805553876446520694400 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (13 : ZMod 545661638816687200389859201) ^ 11609822102482706391273600 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (13 : ZMod 545661638816687200389859201) ^ 10295502619182777365846400 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (13 : ZMod 545661638816687200389859201) ^ 9248502352825206786268800 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (13 : ZMod 545661638816687200389859201) ^ 8945272767486675416227200 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide

private theorem prime_thirtySixAH_62171 : Nat.Prime 62171 := by norm_num
private theorem prime_thirtySixAH_107339 : Nat.Prime 107339 := by norm_num
private theorem prime_thirtySixAH_599 : Nat.Prime 599 := by norm_num
private theorem prime_thirtySixAH_3539 : Nat.Prime 3539 := by norm_num
private theorem prime_thirtySixAH_9068347 : Nat.Prime 9068347 := by norm_num
private theorem prime_thirtySixAH_6377825430320497591 : Nat.Prime 6377825430320497591 := by
  apply lucas_primality 6377825430320497591 (11 : ZMod 6377825430320497591)
  · rw [← thirtySixAHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (5, 1), (599, 1), (3539, 1), (11059, 1), (9068347, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (5, 1), (599, 1), (3539, 1), (11059, 1), (9068347, 1)] : List FactorBlock).map factorBlockValue).prod = 6377825430320497591 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtySixAH_2
      · exact prime_thirtySixAH_3
      · exact prime_thirtySixAH_5
      · exact prime_thirtySixAH_599
      · exact prime_thirtySixAH_3539
      · exact prime_thirtySixAH_11059
      · exact prime_thirtySixAH_9068347
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 6377825430320497591) ^ 3188912715160248795 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (11 : ZMod 6377825430320497591) ^ 2125941810106832530 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (11 : ZMod 6377825430320497591) ^ 1275565086064099518 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (11 : ZMod 6377825430320497591) ^ 10647454808548410 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (11 : ZMod 6377825430320497591) ^ 1802154685029810 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (11 : ZMod 6377825430320497591) ^ 576709054193010 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (11 : ZMod 6377825430320497591) ^ 703306283970 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide

private theorem prime_thirtySixAH_11953 : Nat.Prime 11953 := by norm_num
private theorem prime_thirtySixAH_339907 : Nat.Prime 339907 := by norm_num
private theorem prime_thirtySixAH_26921 : Nat.Prime 26921 := by norm_num
private theorem prime_thirtySixAH_96293 : Nat.Prime 96293 := by norm_num
private theorem prime_thirtySixAH_115327 : Nat.Prime 115327 := by norm_num
private theorem prime_thirtySixAH_1793775758729587 : Nat.Prime 1793775758729587 := by
  apply lucas_primality 1793775758729587 (2 : ZMod 1793775758729587)
  · rw [← thirtySixAHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (26921, 1), (96293, 1), (115327, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (26921, 1), (96293, 1), (115327, 1)] : List FactorBlock).map factorBlockValue).prod = 1793775758729587 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtySixAH_2
      · exact prime_thirtySixAH_3
      · exact prime_thirtySixAH_26921
      · exact prime_thirtySixAH_96293
      · exact prime_thirtySixAH_115327
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1793775758729587) ^ 896887879364793 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (2 : ZMod 1793775758729587) ^ 597925252909862 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (2 : ZMod 1793775758729587) ^ 66631096866 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (2 : ZMod 1793775758729587) ^ 18628309002 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (2 : ZMod 1793775758729587) ^ 15553823118 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide

private theorem prime_thirtySixAH_525451948490143230005049601 : Nat.Prime 525451948490143230005049601 := by
  apply lucas_primality 525451948490143230005049601 (179 : ZMod 525451948490143230005049601)
  · rw [← thirtySixAHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 8), (3, 1), (5, 2), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 8), (3, 1), (5, 2), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod = 525451948490143230005049601 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtySixAH_2
      · exact prime_thirtySixAH_3
      · exact prime_thirtySixAH_5
      · exact prime_thirtySixAH_7
      · exact prime_thirtySixAH_11
      · exact prime_thirtySixAH_13
      · exact prime_thirtySixAH_17
      · exact prime_thirtySixAH_19
      · exact prime_thirtySixAH_23
      · exact prime_thirtySixAH_29
      · exact prime_thirtySixAH_31
      · exact prime_thirtySixAH_37
      · exact prime_thirtySixAH_41
      · exact prime_thirtySixAH_43
      · exact prime_thirtySixAH_47
      · exact prime_thirtySixAH_53
      · exact prime_thirtySixAH_59
      · exact prime_thirtySixAH_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (179 : ZMod 525451948490143230005049601) ^ 262725974245071615002524800 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (179 : ZMod 525451948490143230005049601) ^ 175150649496714410001683200 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (179 : ZMod 525451948490143230005049601) ^ 105090389698028646001009920 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (179 : ZMod 525451948490143230005049601) ^ 75064564070020461429292800 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (179 : ZMod 525451948490143230005049601) ^ 47768358953649384545913600 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (179 : ZMod 525451948490143230005049601) ^ 40419380653087940769619200 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (179 : ZMod 525451948490143230005049601) ^ 30908938146479013529708800 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (179 : ZMod 525451948490143230005049601) ^ 27655365710007538421318400 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (179 : ZMod 525451948490143230005049601) ^ 22845736890875792608915200 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (179 : ZMod 525451948490143230005049601) ^ 18119032706556663103622400 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (179 : ZMod 525451948490143230005049601) ^ 16950062854520749355001600 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (179 : ZMod 525451948490143230005049601) ^ 14201404013247114324460800 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (179 : ZMod 525451948490143230005049601) ^ 12815901182686420244025600 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (179 : ZMod 525451948490143230005049601) ^ 12219812755584726279187200 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (179 : ZMod 525451948490143230005049601) ^ 11179828691279643191596800 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (179 : ZMod 525451948490143230005049601) ^ 9914187707361193018963200 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (179 : ZMod 525451948490143230005049601) ^ 8905965228646495423814400 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (179 : ZMod 525451948490143230005049601) ^ 8613966368690872623033600 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide

private theorem prime_thirtySixAH_37223 : Nat.Prime 37223 := by norm_num
private theorem prime_thirtySixAH_312401611 : Nat.Prime 312401611 := by
  apply lucas_primality 312401611 (10 : ZMod 312401611)
  · rw [← thirtySixAHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 4), (5, 1), (19, 1), (53, 1), (383, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 4), (5, 1), (19, 1), (53, 1), (383, 1)] : List FactorBlock).map factorBlockValue).prod = 312401611 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtySixAH_2
      · exact prime_thirtySixAH_3
      · exact prime_thirtySixAH_5
      · exact prime_thirtySixAH_19
      · exact prime_thirtySixAH_53
      · exact prime_thirtySixAH_383
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 312401611) ^ 156200805 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (10 : ZMod 312401611) ^ 104133870 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (10 : ZMod 312401611) ^ 62480322 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (10 : ZMod 312401611) ^ 16442190 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (10 : ZMod 312401611) ^ 5894370 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (10 : ZMod 312401611) ^ 815670 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide

private theorem prime_thirtySixAH_34313 : Nat.Prime 34313 := by norm_num
private theorem prime_thirtySixAH_603181227149 : Nat.Prime 603181227149 := by
  apply lucas_primality 603181227149 (2 : ZMod 603181227149)
  · rw [← thirtySixAHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (1213, 1), (3623, 1), (34313, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (1213, 1), (3623, 1), (34313, 1)] : List FactorBlock).map factorBlockValue).prod = 603181227149 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtySixAH_2
      · exact prime_thirtySixAH_1213
      · exact prime_thirtySixAH_3623
      · exact prime_thirtySixAH_34313
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 603181227149) ^ 301590613574 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (2 : ZMod 603181227149) ^ 497263996 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (2 : ZMod 603181227149) ^ 166486676 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (2 : ZMod 603181227149) ^ 17578796 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide

private theorem prime_thirtySixAH_13944174244386535740887 : Nat.Prime 13944174244386535740887 := by
  apply lucas_primality 13944174244386535740887 (5 : ZMod 13944174244386535740887)
  · rw [← thirtySixAHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (37, 1), (312401611, 1), (603181227149, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (37, 1), (312401611, 1), (603181227149, 1)] : List FactorBlock).map factorBlockValue).prod = 13944174244386535740887 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtySixAH_2
      · exact prime_thirtySixAH_37
      · exact prime_thirtySixAH_312401611
      · exact prime_thirtySixAH_603181227149
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 13944174244386535740887) ^ 6972087122193267870443 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (5 : ZMod 13944174244386535740887) ^ 376869574172609074078 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (5 : ZMod 13944174244386535740887) ^ 44635410809026 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (5 : ZMod 13944174244386535740887) ^ 23117719214 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide

private theorem prime_thirtySixAH_157 : Nat.Prime 157 := by norm_num
private theorem prime_thirtySixAH_3496613 : Nat.Prime 3496613 := by norm_num
private theorem prime_thirtySixAH_6230057 : Nat.Prime 6230057 := by norm_num
private theorem prime_thirtySixAH_683 : Nat.Prime 683 := by norm_num
private theorem prime_thirtySixAH_12361199 : Nat.Prime 12361199 := by norm_num
private theorem prime_thirtySixAH_12444538203659 : Nat.Prime 12444538203659 := by
  apply lucas_primality 12444538203659 (2 : ZMod 12444538203659)
  · rw [← thirtySixAHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (11, 1), (67, 1), (683, 1), (12361199, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (11, 1), (67, 1), (683, 1), (12361199, 1)] : List FactorBlock).map factorBlockValue).prod = 12444538203659 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtySixAH_2
      · exact prime_thirtySixAH_11
      · exact prime_thirtySixAH_67
      · exact prime_thirtySixAH_683
      · exact prime_thirtySixAH_12361199
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 12444538203659) ^ 6222269101829 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (2 : ZMod 12444538203659) ^ 1131321654878 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (2 : ZMod 12444538203659) ^ 185739376174 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (2 : ZMod 12444538203659) ^ 18220407326 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (2 : ZMod 12444538203659) ^ 1006742 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide

private theorem prime_thirtySixAH_727 : Nat.Prime 727 := by norm_num
private theorem prime_thirtySixAH_517267 : Nat.Prime 517267 := by norm_num
private theorem prime_thirtySixAH_40346827 : Nat.Prime 40346827 := by
  apply lucas_primality 40346827 (2 : ZMod 40346827)
  · rw [← thirtySixAHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (13, 1), (517267, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (13, 1), (517267, 1)] : List FactorBlock).map factorBlockValue).prod = 40346827 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtySixAH_2
      · exact prime_thirtySixAH_3
      · exact prime_thirtySixAH_13
      · exact prime_thirtySixAH_517267
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 40346827) ^ 20173413 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (2 : ZMod 40346827) ^ 13448942 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (2 : ZMod 40346827) ^ 3103602 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (2 : ZMod 40346827) ^ 78 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide

private theorem prime_thirtySixAH_4159 : Nat.Prime 4159 := by norm_num
private theorem prime_thirtySixAH_173 : Nat.Prime 173 := by norm_num
private theorem prime_thirtySixAH_16453 : Nat.Prime 16453 := by norm_num
private theorem prime_thirtySixAH_910838081 : Nat.Prime 910838081 := by
  apply lucas_primality 910838081 (3 : ZMod 910838081)
  · rw [← thirtySixAHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 6), (5, 1), (173, 1), (16453, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 6), (5, 1), (173, 1), (16453, 1)] : List FactorBlock).map factorBlockValue).prod = 910838081 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtySixAH_2
      · exact prime_thirtySixAH_5
      · exact prime_thirtySixAH_173
      · exact prime_thirtySixAH_16453
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 910838081) ^ 455419040 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (3 : ZMod 910838081) ^ 182167616 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (3 : ZMod 910838081) ^ 5264960 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (3 : ZMod 910838081) ^ 55360 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide

private theorem prime_thirtySixAH_75763511577581 : Nat.Prime 75763511577581 := by
  apply lucas_primality 75763511577581 (3 : ZMod 75763511577581)
  · rw [← thirtySixAHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (5, 1), (4159, 1), (910838081, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (5, 1), (4159, 1), (910838081, 1)] : List FactorBlock).map factorBlockValue).prod = 75763511577581 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtySixAH_2
      · exact prime_thirtySixAH_5
      · exact prime_thirtySixAH_4159
      · exact prime_thirtySixAH_910838081
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 75763511577581) ^ 37881755788790 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (3 : ZMod 75763511577581) ^ 15152702315516 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (3 : ZMod 75763511577581) ^ 18216761620 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (3 : ZMod 75763511577581) ^ 83180 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide

private theorem prime_thirtySixAH_17274080639688469 : Nat.Prime 17274080639688469 := by
  apply lucas_primality 17274080639688469 (2 : ZMod 17274080639688469)
  · rw [← thirtySixAHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (19, 1), (75763511577581, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (19, 1), (75763511577581, 1)] : List FactorBlock).map factorBlockValue).prod = 17274080639688469 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtySixAH_2
      · exact prime_thirtySixAH_3
      · exact prime_thirtySixAH_19
      · exact prime_thirtySixAH_75763511577581
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 17274080639688469) ^ 8637040319844234 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (2 : ZMod 17274080639688469) ^ 5758026879896156 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (2 : ZMod 17274080639688469) ^ 909162138930972 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (2 : ZMod 17274080639688469) ^ 228 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide

private theorem prime_thirtySixAH_500724797972960019181282561 : Nat.Prime 500724797972960019181282561 := by
  apply lucas_primality 500724797972960019181282561 (127 : ZMod 500724797972960019181282561)
  · rw [← thirtySixAHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 8), (3, 5), (5, 1), (7, 2), (11, 1), (13, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 8), (3, 5), (5, 1), (7, 2), (11, 1), (13, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod = 500724797972960019181282561 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtySixAH_2
      · exact prime_thirtySixAH_3
      · exact prime_thirtySixAH_5
      · exact prime_thirtySixAH_7
      · exact prime_thirtySixAH_11
      · exact prime_thirtySixAH_13
      · exact prime_thirtySixAH_19
      · exact prime_thirtySixAH_23
      · exact prime_thirtySixAH_29
      · exact prime_thirtySixAH_31
      · exact prime_thirtySixAH_37
      · exact prime_thirtySixAH_41
      · exact prime_thirtySixAH_43
      · exact prime_thirtySixAH_47
      · exact prime_thirtySixAH_53
      · exact prime_thirtySixAH_59
      · exact prime_thirtySixAH_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (127 : ZMod 500724797972960019181282561) ^ 250362398986480009590641280 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (127 : ZMod 500724797972960019181282561) ^ 166908265990986673060427520 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (127 : ZMod 500724797972960019181282561) ^ 100144959594592003836256512 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (127 : ZMod 500724797972960019181282561) ^ 71532113996137145597326080 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (127 : ZMod 500724797972960019181282561) ^ 45520436179360001743752960 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (127 : ZMod 500724797972960019181282561) ^ 38517292151766155321637120 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (127 : ZMod 500724797972960019181282561) ^ 26353936735418948377962240 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (127 : ZMod 500724797972960019181282561) ^ 21770643390128696486142720 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (127 : ZMod 500724797972960019181282561) ^ 17266372343895173075216640 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (127 : ZMod 500724797972960019181282561) ^ 16152412837837419973589760 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (127 : ZMod 500724797972960019181282561) ^ 13533102647917838356250880 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (127 : ZMod 500724797972960019181282561) ^ 12212799950560000467836160 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (127 : ZMod 500724797972960019181282561) ^ 11644762743557209748401920 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (127 : ZMod 500724797972960019181282561) ^ 10653719105807659982580480 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (127 : ZMod 500724797972960019181282561) ^ 9447637697603019229835520 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (127 : ZMod 500724797972960019181282561) ^ 8486860982592542697987840 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (127 : ZMod 500724797972960019181282561) ^ 8208603245458360970184960 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide

private theorem prime_thirtySixAH_2801 : Nat.Prime 2801 := by norm_num
private theorem prime_thirtySixAH_7829 : Nat.Prime 7829 := by norm_num
private theorem prime_thirtySixAH_1319 : Nat.Prime 1319 := by norm_num
private theorem prime_thirtySixAH_169369 : Nat.Prime 169369 := by norm_num
private theorem prime_thirtySixAH_164287931 : Nat.Prime 164287931 := by
  apply lucas_primality 164287931 (2 : ZMod 164287931)
  · rw [← thirtySixAHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 1), (97, 1), (169369, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 1), (97, 1), (169369, 1)] : List FactorBlock).map factorBlockValue).prod = 164287931 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtySixAH_2
      · exact prime_thirtySixAH_5
      · exact prime_thirtySixAH_97
      · exact prime_thirtySixAH_169369
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 164287931) ^ 82143965 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (2 : ZMod 164287931) ^ 32857586 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (2 : ZMod 164287931) ^ 1693690 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (2 : ZMod 164287931) ^ 970 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide

private theorem prime_thirtySixAH_87814665071106317 : Nat.Prime 87814665071106317 := by
  apply lucas_primality 87814665071106317 (2 : ZMod 87814665071106317)
  · rw [← thirtySixAHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (7, 1), (41, 1), (353, 1), (1319, 1), (164287931, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (7, 1), (41, 1), (353, 1), (1319, 1), (164287931, 1)] : List FactorBlock).map factorBlockValue).prod = 87814665071106317 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtySixAH_2
      · exact prime_thirtySixAH_7
      · exact prime_thirtySixAH_41
      · exact prime_thirtySixAH_353
      · exact prime_thirtySixAH_1319
      · exact prime_thirtySixAH_164287931
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 87814665071106317) ^ 43907332535553158 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (2 : ZMod 87814665071106317) ^ 12544952153015188 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (2 : ZMod 87814665071106317) ^ 2141821099295276 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (2 : ZMod 87814665071106317) ^ 248766756575372 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (2 : ZMod 87814665071106317) ^ 66576698310164 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (2 : ZMod 87814665071106317) ^ 534516836 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide

private theorem prime_thirtySixAH_16831 : Nat.Prime 16831 := by norm_num
private theorem prime_thirtySixAH_57427 : Nat.Prime 57427 := by norm_num
private theorem prime_thirtySixAH_10976629 : Nat.Prime 10976629 := by norm_num
private theorem prime_thirtySixAH_205745933977 : Nat.Prime 205745933977 := by
  apply lucas_primality 205745933977 (5 : ZMod 205745933977)
  · rw [← thirtySixAHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (3, 1), (11, 1), (71, 1), (10976629, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (3, 1), (11, 1), (71, 1), (10976629, 1)] : List FactorBlock).map factorBlockValue).prod = 205745933977 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtySixAH_2
      · exact prime_thirtySixAH_3
      · exact prime_thirtySixAH_11
      · exact prime_thirtySixAH_71
      · exact prime_thirtySixAH_10976629
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 205745933977) ^ 102872966988 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (5 : ZMod 205745933977) ^ 68581977992 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (5 : ZMod 205745933977) ^ 18704175816 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (5 : ZMod 205745933977) ^ 2897830056 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (5 : ZMod 205745933977) ^ 18744 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide

private theorem prime_thirtySixAH_506142404437043173 : Nat.Prime 506142404437043173 := by
  apply lucas_primality 506142404437043173 (5 : ZMod 506142404437043173)
  · rw [← thirtySixAHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (17, 1), (31, 1), (389, 1), (205745933977, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (17, 1), (31, 1), (389, 1), (205745933977, 1)] : List FactorBlock).map factorBlockValue).prod = 506142404437043173 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtySixAH_2
      · exact prime_thirtySixAH_3
      · exact prime_thirtySixAH_17
      · exact prime_thirtySixAH_31
      · exact prime_thirtySixAH_389
      · exact prime_thirtySixAH_205745933977
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 506142404437043173) ^ 253071202218521586 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (5 : ZMod 506142404437043173) ^ 168714134812347724 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (5 : ZMod 506142404437043173) ^ 29773082613943716 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (5 : ZMod 506142404437043173) ^ 16327174336678812 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (5 : ZMod 506142404437043173) ^ 1301137286470548 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (5 : ZMod 506142404437043173) ^ 2460036 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide

private theorem prime_thirtySixAH_1277 : Nat.Prime 1277 := by norm_num
private theorem prime_thirtySixAH_23539 : Nat.Prime 23539 := by norm_num
private theorem prime_thirtySixAH_8521 : Nat.Prime 8521 := by norm_num
private theorem prime_thirtySixAH_1192327 : Nat.Prime 1192327 := by norm_num
private theorem prime_thirtySixAH_101598183671 : Nat.Prime 101598183671 := by
  apply lucas_primality 101598183671 (17 : ZMod 101598183671)
  · rw [← thirtySixAHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 1), (8521, 1), (1192327, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 1), (8521, 1), (1192327, 1)] : List FactorBlock).map factorBlockValue).prod = 101598183671 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtySixAH_2
      · exact prime_thirtySixAH_5
      · exact prime_thirtySixAH_8521
      · exact prime_thirtySixAH_1192327
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (17 : ZMod 101598183671) ^ 50799091835 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (17 : ZMod 101598183671) ^ 20319636734 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (17 : ZMod 101598183671) ^ 11923270 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (17 : ZMod 101598183671) ^ 85210 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide

private theorem prime_thirtySixAH_203196367343 : Nat.Prime 203196367343 := by
  apply lucas_primality 203196367343 (5 : ZMod 203196367343)
  · rw [← thirtySixAHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (101598183671, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (101598183671, 1)] : List FactorBlock).map factorBlockValue).prod = 203196367343 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_thirtySixAH_2
      · exact prime_thirtySixAH_101598183671
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 203196367343) ^ 101598183671 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (5 : ZMod 203196367343) ^ 2 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide

private theorem prime_thirtySixAH_1211050349364281 : Nat.Prime 1211050349364281 := by
  apply lucas_primality 1211050349364281 (3 : ZMod 1211050349364281)
  · rw [← thirtySixAHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (5, 1), (149, 1), (203196367343, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (5, 1), (149, 1), (203196367343, 1)] : List FactorBlock).map factorBlockValue).prod = 1211050349364281 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtySixAH_2
      · exact prime_thirtySixAH_5
      · exact prime_thirtySixAH_149
      · exact prime_thirtySixAH_203196367343
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1211050349364281) ^ 605525174682140 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (3 : ZMod 1211050349364281) ^ 242210069872856 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (3 : ZMod 1211050349364281) ^ 8127854693720 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (3 : ZMod 1211050349364281) ^ 5960 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide

private theorem prime_thirtySixAH_16090014941653837367 : Nat.Prime 16090014941653837367 := by
  apply lucas_primality 16090014941653837367 (5 : ZMod 16090014941653837367)
  · rw [← thirtySixAHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (7, 1), (13, 1), (73, 1), (1211050349364281, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (7, 1), (13, 1), (73, 1), (1211050349364281, 1)] : List FactorBlock).map factorBlockValue).prod = 16090014941653837367 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtySixAH_2
      · exact prime_thirtySixAH_7
      · exact prime_thirtySixAH_13
      · exact prime_thirtySixAH_73
      · exact prime_thirtySixAH_1211050349364281
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 16090014941653837367) ^ 8045007470826918683 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (5 : ZMod 16090014941653837367) ^ 2298573563093405338 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (5 : ZMod 16090014941653837367) ^ 1237693457050295182 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (5 : ZMod 16090014941653837367) ^ 220411163584299142 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (5 : ZMod 16090014941653837367) ^ 13286 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide

private theorem prime_thirtySixAH_359 : Nat.Prime 359 := by norm_num
private theorem prime_thirtySixAH_17851 : Nat.Prime 17851 := by norm_num
private theorem prime_thirtySixAH_21493 : Nat.Prime 21493 := by norm_num
private theorem prime_thirtySixAH_16236509 : Nat.Prime 16236509 := by norm_num
private theorem prime_thirtySixAH_937 : Nat.Prime 937 := by norm_num
private theorem prime_thirtySixAH_70486763 : Nat.Prime 70486763 := by
  apply lucas_primality 70486763 (2 : ZMod 70486763)
  · rw [← thirtySixAHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (29, 1), (937, 1), (1297, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (29, 1), (937, 1), (1297, 1)] : List FactorBlock).map factorBlockValue).prod = 70486763 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtySixAH_2
      · exact prime_thirtySixAH_29
      · exact prime_thirtySixAH_937
      · exact prime_thirtySixAH_1297
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 70486763) ^ 35243381 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (2 : ZMod 70486763) ^ 2430578 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (2 : ZMod 70486763) ^ 75226 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (2 : ZMod 70486763) ^ 54346 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide

private theorem prime_thirtySixAH_118556010662121453009495871 : Nat.Prime 118556010662121453009495871 := by
  apply lucas_primality 118556010662121453009495871 (3 : ZMod 118556010662121453009495871)
  · rw [← thirtySixAHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 3), (5, 1), (17851, 1), (21493, 1), (16236509, 1), (70486763, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 3), (5, 1), (17851, 1), (21493, 1), (16236509, 1), (70486763, 1)] : List FactorBlock).map factorBlockValue).prod = 118556010662121453009495871 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtySixAH_2
      · exact prime_thirtySixAH_3
      · exact prime_thirtySixAH_5
      · exact prime_thirtySixAH_17851
      · exact prime_thirtySixAH_21493
      · exact prime_thirtySixAH_16236509
      · exact prime_thirtySixAH_70486763
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 118556010662121453009495871) ^ 59278005331060726504747935 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (3 : ZMod 118556010662121453009495871) ^ 39518670220707151003165290 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (3 : ZMod 118556010662121453009495871) ^ 23711202132424290601899174 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (3 : ZMod 118556010662121453009495871) ^ 6641421245987421041370 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (3 : ZMod 118556010662121453009495871) ^ 5516028970461147955590 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (3 : ZMod 118556010662121453009495871) ^ 7301816582747033430 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (3 : ZMod 118556010662121453009495871) ^ 1681961344460114490 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide

private theorem prime_thirtySixAH_4327 : Nat.Prime 4327 := by norm_num
private theorem prime_thirtySixAH_1214459 : Nat.Prime 1214459 := by norm_num
private theorem prime_thirtySixAH_983 : Nat.Prime 983 := by norm_num
private theorem prime_thirtySixAH_6079 : Nat.Prime 6079 := by norm_num
private theorem prime_thirtySixAH_35853943 : Nat.Prime 35853943 := by
  apply lucas_primality 35853943 (3 : ZMod 35853943)
  · rw [← thirtySixAHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (983, 1), (6079, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (983, 1), (6079, 1)] : List FactorBlock).map factorBlockValue).prod = 35853943 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtySixAH_2
      · exact prime_thirtySixAH_3
      · exact prime_thirtySixAH_983
      · exact prime_thirtySixAH_6079
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 35853943) ^ 17926971 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (3 : ZMod 35853943) ^ 11951314 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (3 : ZMod 35853943) ^ 36474 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (3 : ZMod 35853943) ^ 5898 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide

private theorem prime_thirtySixAH_376537177183483 : Nat.Prime 376537177183483 := by
  apply lucas_primality 376537177183483 (2 : ZMod 376537177183483)
  · rw [← thirtySixAHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 7), (7, 4), (35853943, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 7), (7, 4), (35853943, 1)] : List FactorBlock).map factorBlockValue).prod = 376537177183483 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtySixAH_2
      · exact prime_thirtySixAH_3
      · exact prime_thirtySixAH_7
      · exact prime_thirtySixAH_35853943
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 376537177183483) ^ 188268588591741 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (2 : ZMod 376537177183483) ^ 125512392394494 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (2 : ZMod 376537177183483) ^ 53791025311926 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (2 : ZMod 376537177183483) ^ 10501974 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide

private theorem prime_thirtySixAH_943429 : Nat.Prime 943429 := by norm_num
private theorem prime_thirtySixAH_15959 : Nat.Prime 15959 := by norm_num
private theorem prime_thirtySixAH_336221 : Nat.Prime 336221 := by norm_num
private theorem prime_thirtySixAH_9326927 : Nat.Prime 9326927 := by norm_num
private theorem prime_thirtySixAH_300275803849406719 : Nat.Prime 300275803849406719 := by
  apply lucas_primality 300275803849406719 (3 : ZMod 300275803849406719)
  · rw [← thirtySixAHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (15959, 1), (336221, 1), (9326927, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (15959, 1), (336221, 1), (9326927, 1)] : List FactorBlock).map factorBlockValue).prod = 300275803849406719 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtySixAH_2
      · exact prime_thirtySixAH_3
      · exact prime_thirtySixAH_15959
      · exact prime_thirtySixAH_336221
      · exact prime_thirtySixAH_9326927
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 300275803849406719) ^ 150137901924703359 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (3 : ZMod 300275803849406719) ^ 100091934616468906 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (3 : ZMod 300275803849406719) ^ 18815452337202 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (3 : ZMod 300275803849406719) ^ 893090567958 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (3 : ZMod 300275803849406719) ^ 32194505634 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide

private theorem prime_thirtySixAH_12941 : Nat.Prime 12941 := by norm_num
private theorem prime_thirtySixAH_17389 : Nat.Prime 17389 := by norm_num
private theorem prime_thirtySixAH_25214051 : Nat.Prime 25214051 := by
  apply lucas_primality 25214051 (6 : ZMod 25214051)
  · rw [← thirtySixAHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 2), (29, 1), (17389, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 2), (29, 1), (17389, 1)] : List FactorBlock).map factorBlockValue).prod = 25214051 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtySixAH_2
      · exact prime_thirtySixAH_5
      · exact prime_thirtySixAH_29
      · exact prime_thirtySixAH_17389
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 25214051) ^ 12607025 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (6 : ZMod 25214051) ^ 5042810 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (6 : ZMod 25214051) ^ 869450 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (6 : ZMod 25214051) ^ 1450 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide

private theorem prime_thirtySixAH_2773545611 : Nat.Prime 2773545611 := by
  apply lucas_primality 2773545611 (2 : ZMod 2773545611)
  · rw [← thirtySixAHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 1), (11, 1), (25214051, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 1), (11, 1), (25214051, 1)] : List FactorBlock).map factorBlockValue).prod = 2773545611 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtySixAH_2
      · exact prime_thirtySixAH_5
      · exact prime_thirtySixAH_11
      · exact prime_thirtySixAH_25214051
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 2773545611) ^ 1386772805 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (2 : ZMod 2773545611) ^ 554709122 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (2 : ZMod 2773545611) ^ 252140510 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (2 : ZMod 2773545611) ^ 110 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide

private theorem prime_thirtySixAH_11970622857077 : Nat.Prime 11970622857077 := by
  apply lucas_primality 11970622857077 (2 : ZMod 11970622857077)
  · rw [← thirtySixAHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (13, 1), (83, 1), (2773545611, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (13, 1), (83, 1), (2773545611, 1)] : List FactorBlock).map factorBlockValue).prod = 11970622857077 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtySixAH_2
      · exact prime_thirtySixAH_13
      · exact prime_thirtySixAH_83
      · exact prime_thirtySixAH_2773545611
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 11970622857077) ^ 5985311428538 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (2 : ZMod 11970622857077) ^ 920817142852 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (2 : ZMod 11970622857077) ^ 144224371772 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (2 : ZMod 11970622857077) ^ 4316 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide

private theorem prime_thirtySixAH_55113911370054181597633 : Nat.Prime 55113911370054181597633 := by
  apply lucas_primality 55113911370054181597633 (5 : ZMod 55113911370054181597633)
  · rw [← thirtySixAHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 6), (3, 1), (17, 1), (109, 1), (12941, 1), (11970622857077, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 6), (3, 1), (17, 1), (109, 1), (12941, 1), (11970622857077, 1)] : List FactorBlock).map factorBlockValue).prod = 55113911370054181597633 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtySixAH_2
      · exact prime_thirtySixAH_3
      · exact prime_thirtySixAH_17
      · exact prime_thirtySixAH_109
      · exact prime_thirtySixAH_12941
      · exact prime_thirtySixAH_11970622857077
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 55113911370054181597633) ^ 27556955685027090798816 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (5 : ZMod 55113911370054181597633) ^ 18371303790018060532544 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (5 : ZMod 55113911370054181597633) ^ 3241994786473775388096 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (5 : ZMod 55113911370054181597633) ^ 505632214404166803648 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (5 : ZMod 55113911370054181597633) ^ 4258860317599426752 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (5 : ZMod 55113911370054181597633) ^ 4604097216 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide

private theorem prime_thirtySixAH_330683468220325089585799 : Nat.Prime 330683468220325089585799 := by
  apply lucas_primality 330683468220325089585799 (6 : ZMod 330683468220325089585799)
  · rw [← thirtySixAHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (55113911370054181597633, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (55113911370054181597633, 1)] : List FactorBlock).map factorBlockValue).prod = 330683468220325089585799 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtySixAH_2
      · exact prime_thirtySixAH_3
      · exact prime_thirtySixAH_55113911370054181597633
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (6 : ZMod 330683468220325089585799) ^ 165341734110162544792899 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (6 : ZMod 330683468220325089585799) ^ 110227822740108363195266 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (6 : ZMod 330683468220325089585799) ^ 6 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide

private theorem prime_thirtySixAH_44983 : Nat.Prime 44983 := by norm_num
private theorem prime_thirtySixAH_62011 : Nat.Prime 62011 := by norm_num
private theorem prime_thirtySixAH_367 : Nat.Prime 367 := by norm_num
private theorem prime_thirtySixAH_15787 : Nat.Prime 15787 := by norm_num
private theorem prime_thirtySixAH_69525949 : Nat.Prime 69525949 := by
  apply lucas_primality 69525949 (2 : ZMod 69525949)
  · rw [← thirtySixAHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (367, 1), (15787, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (367, 1), (15787, 1)] : List FactorBlock).map factorBlockValue).prod = 69525949 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtySixAH_2
      · exact prime_thirtySixAH_3
      · exact prime_thirtySixAH_367
      · exact prime_thirtySixAH_15787
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 69525949) ^ 34762974 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (2 : ZMod 69525949) ^ 23175316 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (2 : ZMod 69525949) ^ 189444 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (2 : ZMod 69525949) ^ 4404 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide

private theorem prime_thirtySixAH_6118283513 : Nat.Prime 6118283513 := by
  apply lucas_primality 6118283513 (3 : ZMod 6118283513)
  · rw [← thirtySixAHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (11, 1), (69525949, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (11, 1), (69525949, 1)] : List FactorBlock).map factorBlockValue).prod = 6118283513 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtySixAH_2
      · exact prime_thirtySixAH_11
      · exact prime_thirtySixAH_69525949
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 6118283513) ^ 3059141756 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (3 : ZMod 6118283513) ^ 556207592 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (3 : ZMod 6118283513) ^ 88 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide

private theorem prime_thirtySixAH_104885372978717557351 : Nat.Prime 104885372978717557351 := by
  apply lucas_primality 104885372978717557351 (6 : ZMod 104885372978717557351)
  · rw [← thirtySixAHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (5, 2), (19, 1), (97, 1), (62011, 1), (6118283513, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (5, 2), (19, 1), (97, 1), (62011, 1), (6118283513, 1)] : List FactorBlock).map factorBlockValue).prod = 104885372978717557351 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtySixAH_2
      · exact prime_thirtySixAH_3
      · exact prime_thirtySixAH_5
      · exact prime_thirtySixAH_19
      · exact prime_thirtySixAH_97
      · exact prime_thirtySixAH_62011
      · exact prime_thirtySixAH_6118283513
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 104885372978717557351) ^ 52442686489358778675 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (6 : ZMod 104885372978717557351) ^ 34961790992905852450 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (6 : ZMod 104885372978717557351) ^ 20977074595743511470 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (6 : ZMod 104885372978717557351) ^ 5520282788353555650 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (6 : ZMod 104885372978717557351) ^ 1081292504935232550 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (6 : ZMod 104885372978717557351) ^ 1691399477168850 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (6 : ZMod 104885372978717557351) ^ 17142940950 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide

private theorem prime_thirtySixAH_4691 : Nat.Prime 4691 := by norm_num
private theorem prime_thirtySixAH_4885104199 : Nat.Prime 4885104199 := by
  apply lucas_primality 4885104199 (3 : ZMod 4885104199)
  · rw [← thirtySixAHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (13, 3), (79, 1), (4691, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (13, 3), (79, 1), (4691, 1)] : List FactorBlock).map factorBlockValue).prod = 4885104199 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtySixAH_2
      · exact prime_thirtySixAH_3
      · exact prime_thirtySixAH_13
      · exact prime_thirtySixAH_79
      · exact prime_thirtySixAH_4691
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 4885104199) ^ 2442552099 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (3 : ZMod 4885104199) ^ 1628368066 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (3 : ZMod 4885104199) ^ 375777246 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (3 : ZMod 4885104199) ^ 61836762 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (3 : ZMod 4885104199) ^ 1041378 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide

private theorem prime_thirtySixAH_117242500777 : Nat.Prime 117242500777 := by
  apply lucas_primality 117242500777 (5 : ZMod 117242500777)
  · rw [← thirtySixAHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (3, 1), (4885104199, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (3, 1), (4885104199, 1)] : List FactorBlock).map factorBlockValue).prod = 117242500777 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtySixAH_2
      · exact prime_thirtySixAH_3
      · exact prime_thirtySixAH_4885104199
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 117242500777) ^ 58621250388 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (5 : ZMod 117242500777) ^ 39080833592 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (5 : ZMod 117242500777) ^ 24 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide

private theorem prime_thirtySixAH_7517 : Nat.Prime 7517 := by norm_num
private theorem prime_thirtySixAH_76303 : Nat.Prime 76303 := by norm_num
private theorem prime_thirtySixAH_1147139303 : Nat.Prime 1147139303 := by
  apply lucas_primality 1147139303 (5 : ZMod 1147139303)
  · rw [← thirtySixAHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (7517, 1), (76303, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (7517, 1), (76303, 1)] : List FactorBlock).map factorBlockValue).prod = 1147139303 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtySixAH_2
      · exact prime_thirtySixAH_7517
      · exact prime_thirtySixAH_76303
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 1147139303) ^ 573569651 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (5 : ZMod 1147139303) ^ 152606 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (5 : ZMod 1147139303) ^ 15034 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide

private theorem prime_thirtySixAH_22323330836381 : Nat.Prime 22323330836381 := by
  apply lucas_primality 22323330836381 (2 : ZMod 22323330836381)
  · rw [← thirtySixAHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (5, 1), (7, 1), (139, 1), (1147139303, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (5, 1), (7, 1), (139, 1), (1147139303, 1)] : List FactorBlock).map factorBlockValue).prod = 22323330836381 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtySixAH_2
      · exact prime_thirtySixAH_5
      · exact prime_thirtySixAH_7
      · exact prime_thirtySixAH_139
      · exact prime_thirtySixAH_1147139303
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 22323330836381) ^ 11161665418190 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (2 : ZMod 22323330836381) ^ 4464666167276 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (2 : ZMod 22323330836381) ^ 3189047262340 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (2 : ZMod 22323330836381) ^ 160599502420 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (2 : ZMod 22323330836381) ^ 19460 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide

private theorem prime_thirtySixAH_233 : Nat.Prime 233 := by norm_num
private theorem prime_thirtySixAH_2467 : Nat.Prime 2467 := by norm_num
private theorem prime_thirtySixAH_2429293 : Nat.Prime 2429293 := by norm_num
private theorem prime_thirtySixAH_178569389500477 : Nat.Prime 178569389500477 := by
  apply lucas_primality 178569389500477 (2 : ZMod 178569389500477)
  · rw [← thirtySixAHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (13, 1), (191, 1), (2467, 1), (2429293, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (13, 1), (191, 1), (2467, 1), (2429293, 1)] : List FactorBlock).map factorBlockValue).prod = 178569389500477 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtySixAH_2
      · exact prime_thirtySixAH_3
      · exact prime_thirtySixAH_13
      · exact prime_thirtySixAH_191
      · exact prime_thirtySixAH_2467
      · exact prime_thirtySixAH_2429293
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 178569389500477) ^ 89284694750238 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (2 : ZMod 178569389500477) ^ 59523129833492 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (2 : ZMod 178569389500477) ^ 13736106884652 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (2 : ZMod 178569389500477) ^ 934918269636 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (2 : ZMod 178569389500477) ^ 72383214228 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (2 : ZMod 178569389500477) ^ 73506732 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide

private theorem prime_thirtySixAH_409982818435830158611 : Nat.Prime 409982818435830158611 := by
  apply lucas_primality 409982818435830158611 (3 : ZMod 409982818435830158611)
  · rw [← thirtySixAHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (5, 1), (7, 1), (13, 1), (29, 2), (178569389500477, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (5, 1), (7, 1), (13, 1), (29, 2), (178569389500477, 1)] : List FactorBlock).map factorBlockValue).prod = 409982818435830158611 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtySixAH_2
      · exact prime_thirtySixAH_3
      · exact prime_thirtySixAH_5
      · exact prime_thirtySixAH_7
      · exact prime_thirtySixAH_13
      · exact prime_thirtySixAH_29
      · exact prime_thirtySixAH_178569389500477
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 409982818435830158611) ^ 204991409217915079305 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (3 : ZMod 409982818435830158611) ^ 136660939478610052870 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (3 : ZMod 409982818435830158611) ^ 81996563687166031722 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (3 : ZMod 409982818435830158611) ^ 58568974062261451230 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (3 : ZMod 409982818435830158611) ^ 31537139879679242970 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (3 : ZMod 409982818435830158611) ^ 14137338566752764090 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (3 : ZMod 409982818435830158611) ^ 2295930 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide

private theorem prime_thirtySixAH_28698797290508111102771 : Nat.Prime 28698797290508111102771 := by
  apply lucas_primality 28698797290508111102771 (2 : ZMod 28698797290508111102771)
  · rw [← thirtySixAHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 1), (7, 1), (409982818435830158611, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 1), (7, 1), (409982818435830158611, 1)] : List FactorBlock).map factorBlockValue).prod = 28698797290508111102771 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtySixAH_2
      · exact prime_thirtySixAH_5
      · exact prime_thirtySixAH_7
      · exact prime_thirtySixAH_409982818435830158611
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 28698797290508111102771) ^ 14349398645254055551385 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (2 : ZMod 28698797290508111102771) ^ 5739759458101622220554 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (2 : ZMod 28698797290508111102771) ^ 4099828184358301586110 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (2 : ZMod 28698797290508111102771) ^ 70 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide

private theorem prime_thirtySixAH_55249 : Nat.Prime 55249 := by norm_num
private theorem prime_thirtySixAH_157429 : Nat.Prime 157429 := by norm_num
private theorem prime_thirtySixAH_773027 : Nat.Prime 773027 := by norm_num
private theorem prime_thirtySixAH_17678041 : Nat.Prime 17678041 := by norm_num
private theorem prime_thirtySixAH_176780411 : Nat.Prime 176780411 := by
  apply lucas_primality 176780411 (2 : ZMod 176780411)
  · rw [← thirtySixAHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 1), (17678041, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 1), (17678041, 1)] : List FactorBlock).map factorBlockValue).prod = 176780411 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtySixAH_2
      · exact prime_thirtySixAH_5
      · exact prime_thirtySixAH_17678041
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 176780411) ^ 88390205 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (2 : ZMod 176780411) ^ 35356082 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (2 : ZMod 176780411) ^ 10 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide

private theorem prime_thirtySixAH_17909 : Nat.Prime 17909 := by norm_num
private theorem prime_thirtySixAH_42043 : Nat.Prime 42043 := by norm_num
private theorem prime_thirtySixAH_3075547 : Nat.Prime 3075547 := by norm_num
private theorem prime_thirtySixAH_55359847 : Nat.Prime 55359847 := by
  apply lucas_primality 55359847 (3 : ZMod 55359847)
  · rw [← thirtySixAHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 2), (3075547, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 2), (3075547, 1)] : List FactorBlock).map factorBlockValue).prod = 55359847 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtySixAH_2
      · exact prime_thirtySixAH_3
      · exact prime_thirtySixAH_3075547
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 55359847) ^ 27679923 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (3 : ZMod 55359847) ^ 18453282 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (3 : ZMod 55359847) ^ 18 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide

private theorem prime_thirtySixAH_95661815617 : Nat.Prime 95661815617 := by
  apply lucas_primality 95661815617 (10 : ZMod 95661815617)
  · rw [← thirtySixAHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 6), (3, 3), (55359847, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 6), (3, 3), (55359847, 1)] : List FactorBlock).map factorBlockValue).prod = 95661815617 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtySixAH_2
      · exact prime_thirtySixAH_3
      · exact prime_thirtySixAH_55359847
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (10 : ZMod 95661815617) ^ 47830907808 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (10 : ZMod 95661815617) ^ 31887271872 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (10 : ZMod 95661815617) ^ 1728 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide

private theorem prime_thirtySixAH_295950872210625241 : Nat.Prime 295950872210625241 := by
  apply lucas_primality 295950872210625241 (17 : ZMod 295950872210625241)
  · rw [← thirtySixAHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (3, 1), (5, 1), (7, 1), (29, 1), (127, 1), (95661815617, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (3, 1), (5, 1), (7, 1), (29, 1), (127, 1), (95661815617, 1)] : List FactorBlock).map factorBlockValue).prod = 295950872210625241 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtySixAH_2
      · exact prime_thirtySixAH_3
      · exact prime_thirtySixAH_5
      · exact prime_thirtySixAH_7
      · exact prime_thirtySixAH_29
      · exact prime_thirtySixAH_127
      · exact prime_thirtySixAH_95661815617
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (17 : ZMod 295950872210625241) ^ 147975436105312620 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (17 : ZMod 295950872210625241) ^ 98650290736875080 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (17 : ZMod 295950872210625241) ^ 59190174442125048 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (17 : ZMod 295950872210625241) ^ 42278696030089320 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (17 : ZMod 295950872210625241) ^ 10205202490021560 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (17 : ZMod 295950872210625241) ^ 2330321828430120 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (17 : ZMod 295950872210625241) ^ 3093720 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide

private theorem prime_thirtySixAH_434302120690832669698051201 : Nat.Prime 434302120690832669698051201 := by
  apply lucas_primality 434302120690832669698051201 (14 : ZMod 434302120690832669698051201)
  · rw [← thirtySixAHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 7), (3, 5), (5, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 7), (3, 5), (5, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod = 434302120690832669698051201 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtySixAH_2
      · exact prime_thirtySixAH_3
      · exact prime_thirtySixAH_5
      · exact prime_thirtySixAH_11
      · exact prime_thirtySixAH_13
      · exact prime_thirtySixAH_17
      · exact prime_thirtySixAH_19
      · exact prime_thirtySixAH_23
      · exact prime_thirtySixAH_29
      · exact prime_thirtySixAH_31
      · exact prime_thirtySixAH_37
      · exact prime_thirtySixAH_41
      · exact prime_thirtySixAH_43
      · exact prime_thirtySixAH_47
      · exact prime_thirtySixAH_53
      · exact prime_thirtySixAH_59
      · exact prime_thirtySixAH_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (14 : ZMod 434302120690832669698051201) ^ 217151060345416334849025600 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (14 : ZMod 434302120690832669698051201) ^ 144767373563610889899350400 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (14 : ZMod 434302120690832669698051201) ^ 86860424138166533939610240 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (14 : ZMod 434302120690832669698051201) ^ 39482010971893879063459200 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (14 : ZMod 434302120690832669698051201) ^ 33407855437756359207542400 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (14 : ZMod 434302120690832669698051201) ^ 25547183570048980570473600 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (14 : ZMod 434302120690832669698051201) ^ 22858006352149087878844800 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (14 : ZMod 434302120690832669698051201) ^ 18882700899601420421654400 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (14 : ZMod 434302120690832669698051201) ^ 14975935196235609299932800 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (14 : ZMod 434302120690832669698051201) ^ 14009745828736537732195200 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (14 : ZMod 434302120690832669698051201) ^ 11737895153806288370217600 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (14 : ZMod 434302120690832669698051201) ^ 10592734650995918773123200 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (14 : ZMod 434302120690832669698051201) ^ 10100049318391457434838400 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (14 : ZMod 434302120690832669698051201) ^ 9240470652996439780809600 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (14 : ZMod 434302120690832669698051201) ^ 8194379635676088107510400 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (14 : ZMod 434302120690832669698051201) ^ 7361052893064960503356800 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (14 : ZMod 434302120690832669698051201) ^ 7119706896571027372099200 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide

private theorem prime_thirtySixAH_5573 : Nat.Prime 5573 := by norm_num
private theorem prime_thirtySixAH_12097 : Nat.Prime 12097 := by norm_num
private theorem prime_thirtySixAH_133260553 : Nat.Prime 133260553 := by
  apply lucas_primality 133260553 (7 : ZMod 133260553)
  · rw [← thirtySixAHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (3, 4), (17, 1), (12097, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (3, 4), (17, 1), (12097, 1)] : List FactorBlock).map factorBlockValue).prod = 133260553 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtySixAH_2
      · exact prime_thirtySixAH_3
      · exact prime_thirtySixAH_17
      · exact prime_thirtySixAH_12097
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 133260553) ^ 66630276 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (7 : ZMod 133260553) ^ 44420184 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (7 : ZMod 133260553) ^ 7838856 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (7 : ZMod 133260553) ^ 11016 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide

private theorem prime_thirtySixAH_3198253273 : Nat.Prime 3198253273 := by
  apply lucas_primality 3198253273 (7 : ZMod 3198253273)
  · rw [← thirtySixAHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (3, 1), (133260553, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (3, 1), (133260553, 1)] : List FactorBlock).map factorBlockValue).prod = 3198253273 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtySixAH_2
      · exact prime_thirtySixAH_3
      · exact prime_thirtySixAH_133260553
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 3198253273) ^ 1599126636 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (7 : ZMod 3198253273) ^ 1066084424 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (7 : ZMod 3198253273) ^ 24 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide

private theorem prime_thirtySixAH_9739 : Nat.Prime 9739 := by norm_num
private theorem prime_thirtySixAH_60427 : Nat.Prime 60427 := by norm_num
private theorem prime_thirtySixAH_2192745608479 : Nat.Prime 2192745608479 := by
  apply lucas_primality 2192745608479 (6 : ZMod 2192745608479)
  · rw [← thirtySixAHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 4), (23, 1), (9739, 1), (60427, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 4), (23, 1), (9739, 1), (60427, 1)] : List FactorBlock).map factorBlockValue).prod = 2192745608479 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtySixAH_2
      · exact prime_thirtySixAH_3
      · exact prime_thirtySixAH_23
      · exact prime_thirtySixAH_9739
      · exact prime_thirtySixAH_60427
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 2192745608479) ^ 1096372804239 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (6 : ZMod 2192745608479) ^ 730915202826 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (6 : ZMod 2192745608479) ^ 95336765586 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (6 : ZMod 2192745608479) ^ 225151002 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide
    · change (6 : ZMod 2192745608479) ^ 36287514 ≠ 1
      rw [← thirtySixAHFastPow_eq_pow]
      decide

private theorem phi_thirtySixAH_42561607827701601630409017600 : Nat.totient 42561607827701601630409017600 = 5600569264536983017881600000 := by
  rw [← show ((([(2, 8), (3, 5), (5, 2), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 42561607827701601630409017600 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtySixAH_2, prime_thirtySixAH_3, prime_thirtySixAH_5, prime_thirtySixAH_7, prime_thirtySixAH_11, prime_thirtySixAH_13, prime_thirtySixAH_17, prime_thirtySixAH_19, prime_thirtySixAH_23, prime_thirtySixAH_29, prime_thirtySixAH_31, prime_thirtySixAH_37, prime_thirtySixAH_41, prime_thirtySixAH_43, prime_thirtySixAH_47, prime_thirtySixAH_53, prime_thirtySixAH_59, prime_thirtySixAH_61]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtySixAH_42561607827701601630409017601 : Nat.totient 42561607827701601630409017601 = 42523292341727183165923204800 := by
  rw [← show ((([(1151, 1), (31793, 1), (1163084296342727269807, 1)] : List FactorBlock).map factorBlockValue).prod) = 42561607827701601630409017601 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtySixAH_1151, prime_thirtySixAH_31793, prime_thirtySixAH_1163084296342727269807]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtySixAH_42561607827701601630409017602 : Nat.totient 42561607827701601630409017602 = 21279454888297731959293893888 := by
  rw [← show ((([(2, 1), (26417, 1), (39157, 1), (20572881415656670829, 1)] : List FactorBlock).map factorBlockValue).prod) = 42561607827701601630409017602 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtySixAH_2, prime_thirtySixAH_26417, prime_thirtySixAH_39157, prime_thirtySixAH_20572881415656670829]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtySixAH_42561607827701601630409017603 : Nat.totient 42561607827701601630409017603 = 28128625909797388044427269120 := by
  rw [← show ((([(3, 1), (181, 1), (317, 1), (247262885986263959602913, 1)] : List FactorBlock).map factorBlockValue).prod) = 42561607827701601630409017603 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtySixAH_3, prime_thirtySixAH_181, prime_thirtySixAH_317, prime_thirtySixAH_247262885986263959602913]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtySixAH_42561607827701601630409017604 : Nat.totient 42561607827701601630409017604 = 21208173183769398764640670304 := by
  rw [← show ((([(2, 2), (293, 1), (36315365040701025281918957, 1)] : List FactorBlock).map factorBlockValue).prod) = 42561607827701601630409017604 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtySixAH_2, prime_thirtySixAH_293, prime_thirtySixAH_36315365040701025281918957]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtySixAH_42561607827701601630409017605 : Nat.totient 42561607827701601630409017605 = 34048459602464222349720131776 := by
  rw [← show ((([(5, 1), (41189, 1), (206664924264738651729389, 1)] : List FactorBlock).map factorBlockValue).prod) = 42561607827701601630409017605 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtySixAH_5, prime_thirtySixAH_41189, prime_thirtySixAH_206664924264738651729389]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtySixAH_42561607827701601630409017606 : Nat.totient 42561607827701601630409017606 = 14187080202959039276371584960 := by
  rw [← show ((([(2, 1), (3, 1), (115903, 1), (32244294937, 1), (1898100541591, 1)] : List FactorBlock).map factorBlockValue).prod) = 42561607827701601630409017606 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtySixAH_2, prime_thirtySixAH_3, prime_thirtySixAH_115903, prime_thirtySixAH_32244294937, prime_thirtySixAH_1898100541591]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtySixAH_42561607827701601630409017607 : Nat.totient 42561607827701601630409017607 = 35743324968709001021716992000 := by
  rw [← show ((([(7, 1), (73, 1), (151, 1), (1851841, 1), (297862947728773807, 1)] : List FactorBlock).map factorBlockValue).prod) = 42561607827701601630409017607 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtySixAH_7, prime_thirtySixAH_73, prime_thirtySixAH_151, prime_thirtySixAH_1851841, prime_thirtySixAH_297862947728773807]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtySixAH_42561607827701601630409017608 : Nat.totient 42561607827701601630409017608 = 21272809460526560612669875200 := by
  rw [← show ((([(2, 3), (2663, 1), (9063547, 1), (26126021, 1), (8436948721, 1)] : List FactorBlock).map factorBlockValue).prod) = 42561607827701601630409017608 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtySixAH_2, prime_thirtySixAH_2663, prime_thirtySixAH_9063547, prime_thirtySixAH_26126021, prime_thirtySixAH_8436948721]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtySixAH_42561607827701601630409017609 : Nat.totient 42561607827701601630409017609 = 28300557797673049044347904000 := by
  rw [← show ((([(3, 2), (401, 1), (11069, 1), (53269, 1), (20000838920189041, 1)] : List FactorBlock).map factorBlockValue).prod) = 42561607827701601630409017609 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtySixAH_3, prime_thirtySixAH_401, prime_thirtySixAH_11069, prime_thirtySixAH_53269, prime_thirtySixAH_20000838920189041]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtySixAH_42561607827701601630409017610 : Nat.totient 42561607827701601630409017610 = 17024643131080640652163607040 := by
  rw [← show ((([(2, 1), (5, 1), (4256160782770160163040901761, 1)] : List FactorBlock).map factorBlockValue).prod) = 42561607827701601630409017610 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtySixAH_2, prime_thirtySixAH_5, prime_thirtySixAH_4256160782770160163040901761]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtySixAH_42561607827701601630409017611 : Nat.totient 42561607827701601630409017611 = 38692370752456001482190016000 := by
  rw [← show ((([(11, 1), (3869237075245600148219001601, 1)] : List FactorBlock).map factorBlockValue).prod) = 42561607827701601630409017611 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtySixAH_11, prime_thirtySixAH_3869237075245600148219001601]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtySixAH_42561607827701601630409017612 : Nat.totient 42561607827701601630409017612 = 14187202608767627957354904400 := by
  rw [← show ((([(2, 2), (3, 1), (30429025931, 1), (116559782766332771, 1)] : List FactorBlock).map factorBlockValue).prod) = 42561607827701601630409017612 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtySixAH_2, prime_thirtySixAH_3, prime_thirtySixAH_30429025931, prime_thirtySixAH_116559782766332771]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtySixAH_42561607827701601630409017613 : Nat.totient 42561607827701601630409017613 = 38846203180349079436361256960 := by
  rw [← show ((([(13, 1), (89, 1), (57153721, 1), (643635746791607729, 1)] : List FactorBlock).map factorBlockValue).prod) = 42561607827701601630409017613 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtySixAH_13, prime_thirtySixAH_89, prime_thirtySixAH_57153721, prime_thirtySixAH_643635746791607729]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtySixAH_42561607827701601630409017614 : Nat.totient 42561607827701601630409017614 = 18235252366398532689923449728 := by
  rw [← show ((([(2, 1), (7, 1), (4177, 1), (17047, 1), (42695052666442357879, 1)] : List FactorBlock).map factorBlockValue).prod) = 42561607827701601630409017614 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtySixAH_2, prime_thirtySixAH_7, prime_thirtySixAH_4177, prime_thirtySixAH_17047, prime_thirtySixAH_42695052666442357879]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtySixAH_42561607827701601630409017615 : Nat.totient 42561607827701601630409017615 = 22699524174770612339482005536 := by
  rw [← show ((([(3, 1), (5, 1), (6442029294047, 1), (440457562723103, 1)] : List FactorBlock).map factorBlockValue).prod) = 42561607827701601630409017615 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtySixAH_3, prime_thirtySixAH_5, prime_thirtySixAH_6442029294047, prime_thirtySixAH_440457562723103]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtySixAH_42561607827701601630409017616 : Nat.totient 42561607827701601630409017616 = 21272918339361761714570256384 := by
  rw [← show ((([(2, 4), (3137, 1), (19309, 1), (43916097622182558197, 1)] : List FactorBlock).map factorBlockValue).prod) = 42561607827701601630409017616 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtySixAH_2, prime_thirtySixAH_3137, prime_thirtySixAH_19309, prime_thirtySixAH_43916097622182558197]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtySixAH_42561607827701601630409017617 : Nat.totient 42561607827701601630409017617 = 40053755189695997480714371072 := by
  rw [← show ((([(17, 1), (9473, 1), (264290508800253361755137, 1)] : List FactorBlock).map factorBlockValue).prod) = 42561607827701601630409017617 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtySixAH_17, prime_thirtySixAH_9473, prime_thirtySixAH_264290508800253361755137]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtySixAH_42561607827701601630409017618 : Nat.totient 42561607827701601630409017618 = 14187135113158311726045645312 := by
  rw [← show ((([(2, 1), (3, 2), (210193, 1), (11249345925914014905457, 1)] : List FactorBlock).map factorBlockValue).prod) = 42561607827701601630409017618 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtySixAH_2, prime_thirtySixAH_3, prime_thirtySixAH_210193, prime_thirtySixAH_11249345925914014905457]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtySixAH_42561607827701601630409017619 : Nat.totient 42561607827701601630409017619 = 40321316257284231124258435272 := by
  rw [← show ((([(19, 1), (194839, 1), (11497105931105223349159, 1)] : List FactorBlock).map factorBlockValue).prod) = 42561607827701601630409017619 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtySixAH_19, prime_thirtySixAH_194839, prime_thirtySixAH_11497105931105223349159]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtySixAH_42561607827701601630409017620 : Nat.totient 42561607827701601630409017620 = 17019022488969288677097600000 := by
  rw [← show ((([(2, 2), (5, 1), (3181, 1), (73571, 1), (455881, 1), (19946477413151, 1)] : List FactorBlock).map factorBlockValue).prod) = 42561607827701601630409017620 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtySixAH_2, prime_thirtySixAH_5, prime_thirtySixAH_3181, prime_thirtySixAH_73571, prime_thirtySixAH_455881, prime_thirtySixAH_19946477413151]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtySixAH_42561607827701601630409017621 : Nat.totient 42561607827701601630409017621 = 24047478445268565214835731200 := by
  rw [← show ((([(3, 1), (7, 1), (109, 1), (479, 1), (8596663, 1), (20538307, 1), (219857951, 1)] : List FactorBlock).map factorBlockValue).prod) = 42561607827701601630409017621 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtySixAH_3, prime_thirtySixAH_7, prime_thirtySixAH_109, prime_thirtySixAH_479, prime_thirtySixAH_8596663, prime_thirtySixAH_20538307, prime_thirtySixAH_219857951]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtySixAH_42561607827701601630409017622 : Nat.totient 42561607827701601630409017622 = 19346057078217003877880569000 := by
  rw [← show ((([(2, 1), (11, 1), (150791, 1), (12829801099686321293111, 1)] : List FactorBlock).map factorBlockValue).prod) = 42561607827701601630409017622 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtySixAH_2, prime_thirtySixAH_11, prime_thirtySixAH_150791, prime_thirtySixAH_12829801099686321293111]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtySixAH_42561607827701601630409017623 : Nat.totient 42561607827701601630409017623 = 40710889756071026758502945280 := by
  rw [← show ((([(23, 1), (208309, 1), (2639633, 1), (17613571, 1), (191069423, 1)] : List FactorBlock).map factorBlockValue).prod) = 42561607827701601630409017623 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtySixAH_23, prime_thirtySixAH_208309, prime_thirtySixAH_2639633, prime_thirtySixAH_17613571, prime_thirtySixAH_191069423]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtySixAH_42561607827701601630409017624 : Nat.totient 42561607827701601630409017624 = 14185326469577935538308700160 := by
  rw [← show ((([(2, 3), (3, 1), (8233, 1), (93811, 1), (8274073, 1), (277508030299, 1)] : List FactorBlock).map factorBlockValue).prod) = 42561607827701601630409017624 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtySixAH_2, prime_thirtySixAH_3, prime_thirtySixAH_8233, prime_thirtySixAH_93811, prime_thirtySixAH_8274073, prime_thirtySixAH_277508030299]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtySixAH_42561607827701601630409017625 : Nat.totient 42561607827701601630409017625 = 34023033921172722105171859200 := by
  rw [← show ((([(5, 3), (1297, 1), (262523409885591991552253, 1)] : List FactorBlock).map factorBlockValue).prod) = 42561607827701601630409017625 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtySixAH_5, prime_thirtySixAH_1297, prime_thirtySixAH_262523409885591991552253]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtySixAH_42561607827701601630409017626 : Nat.totient 42561607827701601630409017626 = 19643817194719524685178400000 := by
  rw [← show ((([(2, 1), (13, 1), (10897001, 1), (150223434544060480601, 1)] : List FactorBlock).map factorBlockValue).prod) = 42561607827701601630409017626 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtySixAH_2, prime_thirtySixAH_13, prime_thirtySixAH_10897001, prime_thirtySixAH_150223434544060480601]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtySixAH_42561607827701601630409017627 : Nat.totient 42561607827701601630409017627 = 28374405218467734420272678400 := by
  rw [← show ((([(3, 3), (1576355845470429690015148801, 1)] : List FactorBlock).map factorBlockValue).prod) = 42561607827701601630409017627 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtySixAH_3, prime_thirtySixAH_1576355845470429690015148801]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtySixAH_42561607827701601630409017628 : Nat.totient 42561607827701601630409017628 = 17966940458166031206156150528 := by
  rw [← show ((([(2, 2), (7, 1), (67, 1), (12583, 1), (277259, 1), (2674733, 1), (2431279603, 1)] : List FactorBlock).map factorBlockValue).prod) = 42561607827701601630409017628 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtySixAH_2, prime_thirtySixAH_7, prime_thirtySixAH_67, prime_thirtySixAH_12583, prime_thirtySixAH_277259, prime_thirtySixAH_2674733, prime_thirtySixAH_2431279603]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtySixAH_42561607827701601630409017629 : Nat.totient 42561607827701601630409017629 = 41093961704582185629421265200 := by
  rw [← show ((([(29, 1), (9185291, 1), (159781725938904898211, 1)] : List FactorBlock).map factorBlockValue).prod) = 42561607827701601630409017629 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtySixAH_29, prime_thirtySixAH_9185291, prime_thirtySixAH_159781725938904898211]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtySixAH_42561607827701601630409017630 : Nat.totient 42561607827701601630409017630 = 11338861159810098678655401984 := by
  rw [← show ((([(2, 1), (3, 1), (5, 1), (1049, 1), (139537, 1), (175593973, 1), (55197867029, 1)] : List FactorBlock).map factorBlockValue).prod) = 42561607827701601630409017630 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtySixAH_2, prime_thirtySixAH_3, prime_thirtySixAH_5, prime_thirtySixAH_1049, prime_thirtySixAH_139537, prime_thirtySixAH_175593973, prime_thirtySixAH_55197867029]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtySixAH_42561607827701601630409017631 : Nat.totient 42561607827701601630409017631 = 40935961613133615701684642400 := by
  rw [← show ((([(31, 1), (163, 1), (18041531047, 1), (466869322092541, 1)] : List FactorBlock).map factorBlockValue).prod) = 42561607827701601630409017631 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtySixAH_31, prime_thirtySixAH_163, prime_thirtySixAH_18041531047, prime_thirtySixAH_466869322092541]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtySixAH_42561607827701601630409017632 : Nat.totient 42561607827701601630409017632 = 21255709062173240278465873920 := by
  rw [← show ((([(2, 5), (919, 1), (11257, 1), (425291, 1), (302303849620517, 1)] : List FactorBlock).map factorBlockValue).prod) = 42561607827701601630409017632 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtySixAH_2, prime_thirtySixAH_919, prime_thirtySixAH_11257, prime_thirtySixAH_425291, prime_thirtySixAH_302303849620517]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtySixAH_42561607827701601630409017633 : Nat.totient 42561607827701601630409017633 = 25794725895255583825400250000 := by
  rw [← show ((([(3, 1), (11, 1), (137251, 1), (9396985754191469517451, 1)] : List FactorBlock).map factorBlockValue).prod) = 42561607827701601630409017633 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtySixAH_3, prime_thirtySixAH_11, prime_thirtySixAH_137251, prime_thirtySixAH_9396985754191469517451]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtySixAH_42561607827701601630409017634 : Nat.totient 42561607827701601630409017634 = 20028971131152228806081004864 := by
  rw [← show ((([(2, 1), (17, 1), (963499, 1), (1299235385747572180099, 1)] : List FactorBlock).map factorBlockValue).prod) = 42561607827701601630409017634 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtySixAH_2, prime_thirtySixAH_17, prime_thirtySixAH_963499, prime_thirtySixAH_1299235385747572180099]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtySixAH_42561607827701601630409017635 : Nat.totient 42561607827701601630409017635 = 28972062675565031105586236160 := by
  rw [← show ((([(5, 1), (7, 1), (137, 1), (2929571, 1), (3029879706669817843, 1)] : List FactorBlock).map factorBlockValue).prod) = 42561607827701601630409017635 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtySixAH_5, prime_thirtySixAH_7, prime_thirtySixAH_137, prime_thirtySixAH_2929571, prime_thirtySixAH_3029879706669817843]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtySixAH_42561607827701601630409017636 : Nat.totient 42561607827701601630409017636 = 14046657934239547674011714304 := by
  rw [← show ((([(2, 2), (3, 2), (103, 1), (5009, 1), (2291539082278737626663, 1)] : List FactorBlock).map factorBlockValue).prod) = 42561607827701601630409017636 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtySixAH_2, prime_thirtySixAH_3, prime_thirtySixAH_103, prime_thirtySixAH_5009, prime_thirtySixAH_2291539082278737626663]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtySixAH_42561607827701601630409017637 : Nat.totient 42561607827701601630409017637 = 41408686502722872342901497600 := by
  rw [← show ((([(37, 1), (15881, 1), (72433330714250756267321, 1)] : List FactorBlock).map factorBlockValue).prod) = 42561607827701601630409017637 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtySixAH_37, prime_thirtySixAH_15881, prime_thirtySixAH_72433330714250756267321]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtySixAH_42561607827701601630409017638 : Nat.totient 42561607827701601630409017638 = 20158418574190094865696057600 := by
  rw [← show ((([(2, 1), (19, 1), (8713, 1), (712477, 1), (23415331, 1), (7705406671, 1)] : List FactorBlock).map factorBlockValue).prod) = 42561607827701601630409017638 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtySixAH_2, prime_thirtySixAH_19, prime_thirtySixAH_8713, prime_thirtySixAH_712477, prime_thirtySixAH_23415331, prime_thirtySixAH_7705406671]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtySixAH_42561607827701601630409017639 : Nat.totient 42561607827701601630409017639 = 26128733700766601504660981760 := by
  rw [← show ((([(3, 1), (13, 1), (431, 1), (11719, 1), (1228273, 1), (9574219, 1), (18373307, 1)] : List FactorBlock).map factorBlockValue).prod) = 42561607827701601630409017639 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtySixAH_3, prime_thirtySixAH_13, prime_thirtySixAH_431, prime_thirtySixAH_11719, prime_thirtySixAH_1228273, prime_thirtySixAH_9574219, prime_thirtySixAH_18373307]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtySixAH_42561607827701601630409017640 : Nat.totient 42561607827701601630409017640 = 16872863180679073406038671360 := by
  rw [← show ((([(2, 3), (5, 1), (139, 1), (577, 1), (2303321, 1), (5759873610810107, 1)] : List FactorBlock).map factorBlockValue).prod) = 42561607827701601630409017640 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtySixAH_2, prime_thirtySixAH_5, prime_thirtySixAH_139, prime_thirtySixAH_577, prime_thirtySixAH_2303321, prime_thirtySixAH_5759873610810107]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtySixAH_42561607827701601630409017641 : Nat.totient 42561607827701601630409017641 = 40870733722664143814930340480 := by
  rw [← show ((([(41, 1), (83, 1), (269, 1), (46494737125345995421063, 1)] : List FactorBlock).map factorBlockValue).prod) = 42561607827701601630409017641 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtySixAH_41, prime_thirtySixAH_83, prime_thirtySixAH_269, prime_thirtySixAH_46494737125345995421063]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtySixAH_42561607827701601630409017642 : Nat.totient 42561607827701601630409017642 = 12122020211250044472243546240 := by
  rw [← show ((([(2, 1), (3, 1), (7, 1), (331, 1), (7129, 1), (429449525106920937499, 1)] : List FactorBlock).map factorBlockValue).prod) = 42561607827701601630409017642 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtySixAH_2, prime_thirtySixAH_3, prime_thirtySixAH_7, prime_thirtySixAH_331, prime_thirtySixAH_7129, prime_thirtySixAH_429449525106920937499]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtySixAH_42561607827701601630409017643 : Nat.totient 42561607827701601630409017643 = 41254131470537545568497026720 := by
  rw [← show ((([(43, 1), (131, 1), (125197, 1), (60350983534064075543, 1)] : List FactorBlock).map factorBlockValue).prod) = 42561607827701601630409017643 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtySixAH_43, prime_thirtySixAH_131, prime_thirtySixAH_125197, prime_thirtySixAH_60350983534064075543]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtySixAH_42561607827701601630409017644 : Nat.totient 42561607827701601630409017644 = 19216029111215955730747645440 := by
  rw [← show ((([(2, 2), (11, 1), (149, 1), (60793, 1), (106788750604720147493, 1)] : List FactorBlock).map factorBlockValue).prod) = 42561607827701601630409017644 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtySixAH_2, prime_thirtySixAH_11, prime_thirtySixAH_149, prime_thirtySixAH_60793, prime_thirtySixAH_106788750604720147493]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtySixAH_42561607827701601630409017645 : Nat.totient 42561607827701601630409017645 = 22465180138713717417359424000 := by
  rw [← show ((([(3, 2), (5, 1), (107, 1), (1013, 1), (144417341, 1), (60421700572451, 1)] : List FactorBlock).map factorBlockValue).prod) = 42561607827701601630409017645 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtySixAH_3, prime_thirtySixAH_5, prime_thirtySixAH_107, prime_thirtySixAH_1013, prime_thirtySixAH_144417341, prime_thirtySixAH_60421700572451]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtySixAH_42561607827701601630409017646 : Nat.totient 42561607827701601630409017646 = 20355489529643999634723743704 := by
  rw [← show ((([(2, 1), (23, 1), (328103, 1), (2820005742344536930967, 1)] : List FactorBlock).map factorBlockValue).prod) = 42561607827701601630409017646 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtySixAH_2, prime_thirtySixAH_23, prime_thirtySixAH_328103, prime_thirtySixAH_2820005742344536930967]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtySixAH_42561607827701601630409017647 : Nat.totient 42561607827701601630409017647 = 41656041703707950531889676800 := by
  rw [← show ((([(47, 1), (905566123993651098519340801, 1)] : List FactorBlock).map factorBlockValue).prod) = 42561607827701601630409017647 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtySixAH_47, prime_thirtySixAH_905566123993651098519340801]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtySixAH_42561607827701601630409017648 : Nat.totient 42561607827701601630409017648 = 14160493283226141610141286400 := by
  rw [← show ((([(2, 4), (3, 1), (769, 1), (2143, 1), (8597, 1), (9792301, 1), (6391408799, 1)] : List FactorBlock).map factorBlockValue).prod) = 42561607827701601630409017648 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtySixAH_2, prime_thirtySixAH_3, prime_thirtySixAH_769, prime_thirtySixAH_2143, prime_thirtySixAH_8597, prime_thirtySixAH_9792301, prime_thirtySixAH_6391408799]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtySixAH_42561607827701601630409017649 : Nat.totient 42561607827701601630409017649 = 36478781766415536930259970400 := by
  rw [← show ((([(7, 2), (14051, 1), (2141048869, 1), (28872748760879, 1)] : List FactorBlock).map factorBlockValue).prod) = 42561607827701601630409017649 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtySixAH_7, prime_thirtySixAH_14051, prime_thirtySixAH_2141048869, prime_thirtySixAH_28872748760879]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtySixAH_42561607827701601630409017650 : Nat.totient 42561607827701601630409017650 = 17023945999794817768552612800 := by
  rw [← show ((([(2, 1), (5, 2), (24421, 1), (34856564291144180525293, 1)] : List FactorBlock).map factorBlockValue).prod) = 42561607827701601630409017650 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtySixAH_2, prime_thirtySixAH_5, prime_thirtySixAH_24421, prime_thirtySixAH_34856564291144180525293]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtySixAH_42561607827701601630409017651 : Nat.totient 42561607827701601630409017651 = 26661326887217153485174686720 := by
  rw [← show ((([(3, 1), (17, 1), (607, 1), (324023303, 1), (4243096546919081, 1)] : List FactorBlock).map factorBlockValue).prod) = 42561607827701601630409017651 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtySixAH_3, prime_thirtySixAH_17, prime_thirtySixAH_607, prime_thirtySixAH_324023303, prime_thirtySixAH_4243096546919081]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtySixAH_42561607827701601630409017652 : Nat.totient 42561607827701601630409017652 = 19642109203772277142556368896 := by
  rw [← show ((([(2, 2), (13, 1), (11489, 1), (71241401185919644928609, 1)] : List FactorBlock).map factorBlockValue).prod) = 42561607827701601630409017652 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtySixAH_2, prime_thirtySixAH_13, prime_thirtySixAH_11489, prime_thirtySixAH_71241401185919644928609]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtySixAH_42561607827701601630409017653 : Nat.totient 42561607827701601630409017653 = 41758558623405344995872998400 := by
  rw [← show ((([(53, 1), (803049204296256634536019201, 1)] : List FactorBlock).map factorBlockValue).prod) = 42561607827701601630409017653 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtySixAH_53, prime_thirtySixAH_803049204296256634536019201]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtySixAH_42561607827701601630409017654 : Nat.totient 42561607827701601630409017654 = 14143947563348090209298304000 := by
  rw [← show ((([(2, 1), (3, 3), (421, 1), (1483, 1), (2072201, 1), (2567179, 1), (237308333, 1)] : List FactorBlock).map factorBlockValue).prod) = 42561607827701601630409017654 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtySixAH_2, prime_thirtySixAH_3, prime_thirtySixAH_421, prime_thirtySixAH_1483, prime_thirtySixAH_2072201, prime_thirtySixAH_2567179, prime_thirtySixAH_237308333]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtySixAH_42561607827701601630409017655 : Nat.totient 42561607827701601630409017655 = 30953896601964801185752012800 := by
  rw [← show ((([(5, 1), (11, 1), (773847415049120029643800321, 1)] : List FactorBlock).map factorBlockValue).prod) = 42561607827701601630409017655 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtySixAH_5, prime_thirtySixAH_11, prime_thirtySixAH_773847415049120029643800321]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtySixAH_42561607827701601630409017656 : Nat.totient 42561607827701601630409017656 = 18174838203281357432562309120 := by
  rw [← show ((([(2, 3), (7, 1), (277, 1), (6810796141, 1), (402858330250993, 1)] : List FactorBlock).map factorBlockValue).prod) = 42561607827701601630409017656 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtySixAH_2, prime_thirtySixAH_7, prime_thirtySixAH_277, prime_thirtySixAH_6810796141, prime_thirtySixAH_402858330250993]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtySixAH_42561607827701601630409017657 : Nat.totient 42561607827701601630409017657 = 26480901336973829372953497600 := by
  rw [← show ((([(3, 1), (19, 2), (101, 1), (199, 1), (119737, 1), (21706837, 1), (752298509, 1)] : List FactorBlock).map factorBlockValue).prod) = 42561607827701601630409017657 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtySixAH_3, prime_thirtySixAH_19, prime_thirtySixAH_101, prime_thirtySixAH_199, prime_thirtySixAH_119737, prime_thirtySixAH_21706837, prime_thirtySixAH_752298509]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtySixAH_42561607827701601630409017658 : Nat.totient 42561607827701601630409017658 = 20543631600603312415975246080 := by
  rw [← show ((([(2, 1), (29, 1), (6131, 1), (126749873, 1), (944302595030827, 1)] : List FactorBlock).map factorBlockValue).prod) = 42561607827701601630409017658 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtySixAH_2, prime_thirtySixAH_29, prime_thirtySixAH_6131, prime_thirtySixAH_126749873, prime_thirtySixAH_944302595030827]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtySixAH_42561607827701601630409017659 : Nat.totient 42561607827701601630409017659 = 41652600318422575252196271336 := by
  rw [← show ((([(59, 1), (223, 1), (3234902168252762911789087, 1)] : List FactorBlock).map factorBlockValue).prod) = 42561607827701601630409017659 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtySixAH_59, prime_thirtySixAH_223, prime_thirtySixAH_3234902168252762911789087]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtySixAH_42561607827701601630409017660 : Nat.totient 42561607827701601630409017660 = 11294067856788255329410314240 := by
  rw [← show ((([(2, 2), (3, 1), (5, 1), (281, 1), (739, 1), (3540386347, 1), (964862349257, 1)] : List FactorBlock).map factorBlockValue).prod) = 42561607827701601630409017660 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtySixAH_2, prime_thirtySixAH_3, prime_thirtySixAH_5, prime_thirtySixAH_281, prime_thirtySixAH_739, prime_thirtySixAH_3540386347, prime_thirtySixAH_964862349257]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtySixAH_42561607827701601630409017661 : Nat.totient 42561607827701601630409017661 = 41863876551816225732613390320 := by
  rw [← show ((([(61, 1), (1965691801783, 1), (354954563696647, 1)] : List FactorBlock).map factorBlockValue).prod) = 42561607827701601630409017661 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtySixAH_61, prime_thirtySixAH_1965691801783, prime_thirtySixAH_354954563696647]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtySixAH_42561607827701601630409017662 : Nat.totient 42561607827701601630409017662 = 20594326368242710466326944000 := by
  rw [← show ((([(2, 1), (31, 1), (686477545608090348877564801, 1)] : List FactorBlock).map factorBlockValue).prod) = 42561607827701601630409017662 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtySixAH_2, prime_thirtySixAH_31, prime_thirtySixAH_686477545608090348877564801]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtySixAH_42561607827701601630409017663 : Nat.totient 42561607827701601630409017663 = 24298544408402649163161581712 := by
  rw [← show ((([(3, 2), (7, 1), (1087, 1), (621509730110564998034623, 1)] : List FactorBlock).map factorBlockValue).prod) = 42561607827701601630409017663 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtySixAH_3, prime_thirtySixAH_7, prime_thirtySixAH_1087, prime_thirtySixAH_621509730110564998034623]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtySixAH_42561607827701601630409017664 : Nat.totient 42561607827701601630409017664 = 21279982661105504751925601280 := by
  rw [← show ((([(2, 6), (25913, 1), (1731666887, 1), (14820266192971, 1)] : List FactorBlock).map factorBlockValue).prod) = 42561607827701601630409017664 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtySixAH_2, prime_thirtySixAH_25913, prime_thirtySixAH_1731666887, prime_thirtySixAH_14820266192971]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtySixAH_42561607827701601630409017665 : Nat.totient 42561607827701601630409017665 = 30987432592209006828657120000 := by
  rw [← show ((([(5, 1), (13, 1), (71, 1), (161037971, 1), (57268793044601101, 1)] : List FactorBlock).map factorBlockValue).prod) = 42561607827701601630409017665 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtySixAH_5, prime_thirtySixAH_13, prime_thirtySixAH_71, prime_thirtySixAH_161037971, prime_thirtySixAH_57268793044601101]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtySixAH_42561607827701601630409017666 : Nat.totient 42561607827701601630409017666 = 12897259335595233175515382080 := by
  rw [← show ((([(2, 1), (3, 1), (11, 1), (97327, 1), (208223, 1), (4129087, 1), (7706514863, 1)] : List FactorBlock).map factorBlockValue).prod) = 42561607827701601630409017666 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtySixAH_2, prime_thirtySixAH_3, prime_thirtySixAH_11, prime_thirtySixAH_97327, prime_thirtySixAH_208223, prime_thirtySixAH_4129087, prime_thirtySixAH_7706514863]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtySixAH_42561607827701601630409017667 : Nat.totient 42561607827701601630409017667 = 42561508589948508470573727744 := by
  rw [← show ((([(508033, 1), (5191489, 1), (5873239, 1), (2747618869, 1)] : List FactorBlock).map factorBlockValue).prod) = 42561607827701601630409017667 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtySixAH_508033, prime_thirtySixAH_5191489, prime_thirtySixAH_5873239, prime_thirtySixAH_2747618869]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtySixAH_42561607827701601630409017668 : Nat.totient 42561607827701601630409017668 = 20028991918918400767251302400 := by
  rw [← show ((([(2, 2), (17, 1), (625905997466200023976603201, 1)] : List FactorBlock).map factorBlockValue).prod) = 42561607827701601630409017668 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtySixAH_2, prime_thirtySixAH_17, prime_thirtySixAH_625905997466200023976603201]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtySixAH_42561607827701601630409017669 : Nat.totient 42561607827701601630409017669 = 27031458980913175241877946368 := by
  rw [← show ((([(3, 1), (23, 1), (449, 1), (557, 1), (128239, 1), (73816529, 1), (260551547, 1)] : List FactorBlock).map factorBlockValue).prod) = 42561607827701601630409017669 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtySixAH_3, prime_thirtySixAH_23, prime_thirtySixAH_449, prime_thirtySixAH_557, prime_thirtySixAH_128239, prime_thirtySixAH_73816529, prime_thirtySixAH_260551547]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtySixAH_42561607827701601630409017670 : Nat.totient 42561607827701601630409017670 = 14592115565627431319693209728 := by
  rw [← show ((([(2, 1), (5, 1), (7, 1), (33493, 1), (18153732689432590021117, 1)] : List FactorBlock).map factorBlockValue).prod) = 42561607827701601630409017670 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtySixAH_2, prime_thirtySixAH_5, prime_thirtySixAH_7, prime_thirtySixAH_33493, prime_thirtySixAH_18153732689432590021117]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtySixAH_42561607827701601630409017671 : Nat.totient 42561607827701601630409017671 = 41919752831957770957188857856 := by
  rw [← show ((([(79, 1), (433, 1), (7043, 1), (552179, 1), (1997617, 1), (160159697, 1)] : List FactorBlock).map factorBlockValue).prod) = 42561607827701601630409017671 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtySixAH_79, prime_thirtySixAH_433, prime_thirtySixAH_7043, prime_thirtySixAH_552179, prime_thirtySixAH_1997617, prime_thirtySixAH_160159697]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtySixAH_42561607827701601630409017672 : Nat.totient 42561607827701601630409017672 = 14187202597629893889172946400 := by
  rw [← show ((([(2, 3), (3, 2), (1222615931, 1), (483498887150858771, 1)] : List FactorBlock).map factorBlockValue).prod) = 42561607827701601630409017672 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtySixAH_2, prime_thirtySixAH_3, prime_thirtySixAH_1222615931, prime_thirtySixAH_483498887150858771]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtySixAH_42561607827701601630409017673 : Nat.totient 42561607827701601630409017673 = 42143147752670215999953020928 := by
  rw [← show ((([(113, 1), (1009, 1), (373291770768408234126569, 1)] : List FactorBlock).map factorBlockValue).prod) = 42561607827701601630409017673 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtySixAH_113, prime_thirtySixAH_1009, prime_thirtySixAH_373291770768408234126569]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtySixAH_42561607827701601630409017674 : Nat.totient 42561607827701601630409017674 = 20704674860533659389257414656 := by
  rw [← show ((([(2, 1), (37, 1), (28463, 1), (100103, 1), (546353, 1), (369475127753, 1)] : List FactorBlock).map factorBlockValue).prod) = 42561607827701601630409017674 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtySixAH_2, prime_thirtySixAH_37, prime_thirtySixAH_28463, prime_thirtySixAH_100103, prime_thirtySixAH_546353, prime_thirtySixAH_369475127753]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtySixAH_42561607827701601630409017675 : Nat.totient 42561607827701601630409017675 = 22699175643026812723343603200 := by
  rw [← show ((([(3, 1), (5, 2), (65129, 1), (8713293684370321798361, 1)] : List FactorBlock).map factorBlockValue).prod) = 42561607827701601630409017675 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtySixAH_3, prime_thirtySixAH_5, prime_thirtySixAH_65129, prime_thirtySixAH_8713293684370321798361]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtySixAH_42561607827701601630409017676 : Nat.totient 42561607827701601630409017676 = 20155249322637667857567636480 := by
  rw [← show ((([(2, 2), (19, 1), (3691, 1), (401987, 1), (377440396466729153, 1)] : List FactorBlock).map factorBlockValue).prod) = 42561607827701601630409017676 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtySixAH_2, prime_thirtySixAH_19, prime_thirtySixAH_3691, prime_thirtySixAH_401987, prime_thirtySixAH_377440396466729153]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtySixAH_42561607827701601630409017677 : Nat.totient 42561607827701601630409017677 = 33020064339159156117550433280 := by
  rw [← show ((([(7, 1), (11, 1), (229, 1), (985909277, 1), (2448244936903697, 1)] : List FactorBlock).map factorBlockValue).prod) = 42561607827701601630409017677 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtySixAH_7, prime_thirtySixAH_11, prime_thirtySixAH_229, prime_thirtySixAH_985909277, prime_thirtySixAH_2448244936903697]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtySixAH_42561607827701601630409017678 : Nat.totient 42561607827701601630409017678 = 13095879331600492809356620800 := by
  rw [← show ((([(2, 1), (3, 1), (13, 1), (545661638816687200389859201, 1)] : List FactorBlock).map factorBlockValue).prod) = 42561607827701601630409017678 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtySixAH_2, prime_thirtySixAH_3, prime_thirtySixAH_13, prime_thirtySixAH_545661638816687200389859201]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtySixAH_42561607827701601630409017679 : Nat.totient 42561607827701601630409017679 = 42560526728890733426509661400 := by
  rw [← show ((([(62171, 1), (107339, 1), (6377825430320497591, 1)] : List FactorBlock).map factorBlockValue).prod) = 42561607827701601630409017679 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtySixAH_62171, prime_thirtySixAH_107339, prime_thirtySixAH_6377825430320497591]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtySixAH_42561607827701601630409017680 : Nat.totient 42561607827701601630409017680 = 16789974657856405519942729728 := by
  rw [← show ((([(2, 4), (5, 1), (73, 1), (11953, 1), (339907, 1), (1793775758729587, 1)] : List FactorBlock).map factorBlockValue).prod) = 42561607827701601630409017680 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtySixAH_2, prime_thirtySixAH_5, prime_thirtySixAH_73, prime_thirtySixAH_11953, prime_thirtySixAH_339907, prime_thirtySixAH_1793775758729587]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtySixAH_42561607827701601630409017681 : Nat.totient 42561607827701601630409017681 = 28374405218467734420272678400 := by
  rw [← show ((([(3, 4), (525451948490143230005049601, 1)] : List FactorBlock).map factorBlockValue).prod) = 42561607827701601630409017681 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtySixAH_3, prime_thirtySixAH_525451948490143230005049601]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtySixAH_42561607827701601630409017682 : Nat.totient 42561607827701601630409017682 = 20761202148982225333890347680 := by
  rw [← show ((([(2, 1), (41, 1), (37223, 1), (13944174244386535740887, 1)] : List FactorBlock).map factorBlockValue).prod) = 42561607827701601630409017682 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtySixAH_2, prime_thirtySixAH_41, prime_thirtySixAH_37223, prime_thirtySixAH_13944174244386535740887]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtySixAH_42561607827701601630409017683 : Nat.totient 42561607827701601630409017683 = 42290495901360639563350976256 := by
  rw [← show ((([(157, 1), (3496613, 1), (6230057, 1), (12444538203659, 1)] : List FactorBlock).map factorBlockValue).prod) = 42561607827701601630409017683 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtySixAH_157, prime_thirtySixAH_3496613, prime_thirtySixAH_6230057, prime_thirtySixAH_12444538203659]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtySixAH_42561607827701601630409017684 : Nat.totient 42561607827701601630409017684 = 12143732174124047542787144832 := by
  rw [← show ((([(2, 2), (3, 1), (7, 1), (727, 1), (40346827, 1), (17274080639688469, 1)] : List FactorBlock).map factorBlockValue).prod) = 42561607827701601630409017684 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtySixAH_2, prime_thirtySixAH_3, prime_thirtySixAH_7, prime_thirtySixAH_727, prime_thirtySixAH_40346827, prime_thirtySixAH_17274080639688469]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtySixAH_42561607827701601630409017685 : Nat.totient 42561607827701601630409017685 = 32046387070269441227602083840 := by
  rw [← show ((([(5, 1), (17, 1), (500724797972960019181282561, 1)] : List FactorBlock).map factorBlockValue).prod) = 42561607827701601630409017685 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtySixAH_5, prime_thirtySixAH_17, prime_thirtySixAH_500724797972960019181282561]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtySixAH_42561607827701601630409017686 : Nat.totient 42561607827701601630409017686 = 20694986779026058346958028800 := by
  rw [← show ((([(2, 1), (43, 1), (257, 1), (2801, 1), (7829, 1), (87814665071106317, 1)] : List FactorBlock).map factorBlockValue).prod) = 42561607827701601630409017686 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtySixAH_2, prime_thirtySixAH_43, prime_thirtySixAH_257, prime_thirtySixAH_2801, prime_thirtySixAH_7829, prime_thirtySixAH_87814665071106317]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtySixAH_42561607827701601630409017687 : Nat.totient 42561607827701601630409017687 = 27393872713788202793719954560 := by
  rw [← show ((([(3, 1), (29, 1), (16831, 1), (57427, 1), (506142404437043173, 1)] : List FactorBlock).map factorBlockValue).prod) = 42561607827701601630409017687 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtySixAH_3, prime_thirtySixAH_29, prime_thirtySixAH_16831, prime_thirtySixAH_57427, prime_thirtySixAH_506142404437043173]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtySixAH_42561607827701601630409017688 : Nat.totient 42561607827701601630409017688 = 19330214427396915140923144320 := by
  rw [← show ((([(2, 3), (11, 1), (1277, 1), (23539, 1), (16090014941653837367, 1)] : List FactorBlock).map factorBlockValue).prod) = 42561607827701601630409017688 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtySixAH_2, prime_thirtySixAH_11, prime_thirtySixAH_1277, prime_thirtySixAH_23539, prime_thirtySixAH_16090014941653837367]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtySixAH_42561607827701601630409017689 : Nat.totient 42561607827701601630409017689 = 42443051817039480177399521460 := by
  rw [← show ((([(359, 1), (118556010662121453009495871, 1)] : List FactorBlock).map factorBlockValue).prod) = 42561607827701601630409017689 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtySixAH_359, prime_thirtySixAH_118556010662121453009495871]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtySixAH_42561607827701601630409017690 : Nat.totient 42561607827701601630409017690 = 11299652204252097710385228672 := by
  rw [← show ((([(2, 1), (3, 2), (5, 1), (239, 1), (4327, 1), (1214459, 1), (376537177183483, 1)] : List FactorBlock).map factorBlockValue).prod) = 42561607827701601630409017690 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtySixAH_2, prime_thirtySixAH_3, prime_thirtySixAH_5, prime_thirtySixAH_239, prime_thirtySixAH_4327, prime_thirtySixAH_1214459, prime_thirtySixAH_376537177183483]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtySixAH_42561607827701601630409017691 : Nat.totient 42561607827701601630409017691 = 33409924456267755138424316544 := by
  rw [← show ((([(7, 1), (13, 2), (127, 1), (943429, 1), (300275803849406719, 1)] : List FactorBlock).map factorBlockValue).prod) = 42561607827701601630409017691 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtySixAH_7, prime_thirtySixAH_13, prime_thirtySixAH_127, prime_thirtySixAH_943429, prime_thirtySixAH_300275803849406719]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtySixAH_42561607827701601630409017692 : Nat.totient 42561607827701601630409017692 = 20341001497168636910601606576 := by
  rw [← show ((([(2, 2), (23, 1), (1399, 1), (330683468220325089585799, 1)] : List FactorBlock).map factorBlockValue).prod) = 42561607827701601630409017692 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtySixAH_2, prime_thirtySixAH_23, prime_thirtySixAH_1399, prime_thirtySixAH_330683468220325089585799]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtySixAH_42561607827701601630409017693 : Nat.totient 42561607827701601630409017693 = 27175414160613157428773952000 := by
  rw [← show ((([(3, 1), (31, 1), (97, 1), (44983, 1), (104885372978717557351, 1)] : List FactorBlock).map factorBlockValue).prod) = 42561607827701601630409017693 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtySixAH_3, prime_thirtySixAH_31, prime_thirtySixAH_97, prime_thirtySixAH_44983, prime_thirtySixAH_104885372978717557351]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtySixAH_42561607827701601630409017694 : Nat.totient 42561607827701601630409017694 = 20707627667561662586892322560 := by
  rw [← show ((([(2, 1), (47, 1), (173, 1), (117242500777, 1), (22323330836381, 1)] : List FactorBlock).map factorBlockValue).prod) = 42561607827701601630409017694 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtySixAH_2, prime_thirtySixAH_47, prime_thirtySixAH_173, prime_thirtySixAH_117242500777, prime_thirtySixAH_22323330836381]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtySixAH_42561607827701601630409017695 : Nat.totient 42561607827701601630409017695 = 31639390856082734198804225280 := by
  rw [← show ((([(5, 1), (19, 1), (67, 1), (233, 1), (28698797290508111102771, 1)] : List FactorBlock).map factorBlockValue).prod) = 42561607827701601630409017695 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtySixAH_5, prime_thirtySixAH_19, prime_thirtySixAH_67, prime_thirtySixAH_233, prime_thirtySixAH_28698797290508111102771]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtySixAH_42561607827701601630409017696 : Nat.totient 42561607827701601630409017696 = 14148802857292038353182556160 := by
  rw [← show ((([(2, 5), (3, 1), (373, 1), (55249, 1), (157429, 1), (773027, 1), (176780411, 1)] : List FactorBlock).map factorBlockValue).prod) = 42561607827701601630409017696 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtySixAH_2, prime_thirtySixAH_3, prime_thirtySixAH_373, prime_thirtySixAH_55249, prime_thirtySixAH_157429, prime_thirtySixAH_773027, prime_thirtySixAH_176780411]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtySixAH_42561607827701601630409017697 : Nat.totient 42561607827701601630409017697 = 42335401099984048904249001600 := by
  rw [← show ((([(191, 1), (17909, 1), (42043, 1), (295950872210625241, 1)] : List FactorBlock).map factorBlockValue).prod) = 42561607827701601630409017697 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtySixAH_191, prime_thirtySixAH_17909, prime_thirtySixAH_42043, prime_thirtySixAH_295950872210625241]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtySixAH_42561607827701601630409017698 : Nat.totient 42561607827701601630409017698 = 18240689069014972127318150400 := by
  rw [← show ((([(2, 1), (7, 2), (434302120690832669698051201, 1)] : List FactorBlock).map factorBlockValue).prod) = 42561607827701601630409017698 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtySixAH_2, prime_thirtySixAH_7, prime_thirtySixAH_434302120690832669698051201]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtySixAH_42561607827701601630409017699 : Nat.totient 42561607827701601630409017699 = 25790285276054385121047640320 := by
  rw [← show ((([(3, 2), (11, 2), (5573, 1), (3198253273, 1), (2192745608479, 1)] : List FactorBlock).map factorBlockValue).prod) = 42561607827701601630409017699 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtySixAH_3, prime_thirtySixAH_11, prime_thirtySixAH_5573, prime_thirtySixAH_3198253273, prime_thirtySixAH_2192745608479]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

theorem freeKill_64ThirtySixAH : certifiedKill 1 42561607827701601630409017599 99 := by
  norm_num [certifiedKill, windowDiscrepancy, Finset.sum_range_succ,
    phi_thirtySixAH_42561607827701601630409017600, phi_thirtySixAH_42561607827701601630409017601, phi_thirtySixAH_42561607827701601630409017602,
    phi_thirtySixAH_42561607827701601630409017603, phi_thirtySixAH_42561607827701601630409017604, phi_thirtySixAH_42561607827701601630409017605,
    phi_thirtySixAH_42561607827701601630409017606, phi_thirtySixAH_42561607827701601630409017607, phi_thirtySixAH_42561607827701601630409017608,
    phi_thirtySixAH_42561607827701601630409017609, phi_thirtySixAH_42561607827701601630409017610, phi_thirtySixAH_42561607827701601630409017611,
    phi_thirtySixAH_42561607827701601630409017612, phi_thirtySixAH_42561607827701601630409017613, phi_thirtySixAH_42561607827701601630409017614,
    phi_thirtySixAH_42561607827701601630409017615, phi_thirtySixAH_42561607827701601630409017616, phi_thirtySixAH_42561607827701601630409017617,
    phi_thirtySixAH_42561607827701601630409017618, phi_thirtySixAH_42561607827701601630409017619, phi_thirtySixAH_42561607827701601630409017620,
    phi_thirtySixAH_42561607827701601630409017621, phi_thirtySixAH_42561607827701601630409017622, phi_thirtySixAH_42561607827701601630409017623,
    phi_thirtySixAH_42561607827701601630409017624, phi_thirtySixAH_42561607827701601630409017625, phi_thirtySixAH_42561607827701601630409017626,
    phi_thirtySixAH_42561607827701601630409017627, phi_thirtySixAH_42561607827701601630409017628, phi_thirtySixAH_42561607827701601630409017629,
    phi_thirtySixAH_42561607827701601630409017630, phi_thirtySixAH_42561607827701601630409017631, phi_thirtySixAH_42561607827701601630409017632,
    phi_thirtySixAH_42561607827701601630409017633, phi_thirtySixAH_42561607827701601630409017634, phi_thirtySixAH_42561607827701601630409017635,
    phi_thirtySixAH_42561607827701601630409017636, phi_thirtySixAH_42561607827701601630409017637, phi_thirtySixAH_42561607827701601630409017638,
    phi_thirtySixAH_42561607827701601630409017639, phi_thirtySixAH_42561607827701601630409017640, phi_thirtySixAH_42561607827701601630409017641,
    phi_thirtySixAH_42561607827701601630409017642, phi_thirtySixAH_42561607827701601630409017643, phi_thirtySixAH_42561607827701601630409017644,
    phi_thirtySixAH_42561607827701601630409017645, phi_thirtySixAH_42561607827701601630409017646, phi_thirtySixAH_42561607827701601630409017647,
    phi_thirtySixAH_42561607827701601630409017648, phi_thirtySixAH_42561607827701601630409017649, phi_thirtySixAH_42561607827701601630409017650,
    phi_thirtySixAH_42561607827701601630409017651, phi_thirtySixAH_42561607827701601630409017652, phi_thirtySixAH_42561607827701601630409017653,
    phi_thirtySixAH_42561607827701601630409017654, phi_thirtySixAH_42561607827701601630409017655, phi_thirtySixAH_42561607827701601630409017656,
    phi_thirtySixAH_42561607827701601630409017657, phi_thirtySixAH_42561607827701601630409017658, phi_thirtySixAH_42561607827701601630409017659,
    phi_thirtySixAH_42561607827701601630409017660, phi_thirtySixAH_42561607827701601630409017661, phi_thirtySixAH_42561607827701601630409017662,
    phi_thirtySixAH_42561607827701601630409017663, phi_thirtySixAH_42561607827701601630409017664, phi_thirtySixAH_42561607827701601630409017665,
    phi_thirtySixAH_42561607827701601630409017666, phi_thirtySixAH_42561607827701601630409017667, phi_thirtySixAH_42561607827701601630409017668,
    phi_thirtySixAH_42561607827701601630409017669, phi_thirtySixAH_42561607827701601630409017670, phi_thirtySixAH_42561607827701601630409017671,
    phi_thirtySixAH_42561607827701601630409017672, phi_thirtySixAH_42561607827701601630409017673, phi_thirtySixAH_42561607827701601630409017674,
    phi_thirtySixAH_42561607827701601630409017675, phi_thirtySixAH_42561607827701601630409017676, phi_thirtySixAH_42561607827701601630409017677,
    phi_thirtySixAH_42561607827701601630409017678, phi_thirtySixAH_42561607827701601630409017679, phi_thirtySixAH_42561607827701601630409017680,
    phi_thirtySixAH_42561607827701601630409017681, phi_thirtySixAH_42561607827701601630409017682, phi_thirtySixAH_42561607827701601630409017683,
    phi_thirtySixAH_42561607827701601630409017684, phi_thirtySixAH_42561607827701601630409017685, phi_thirtySixAH_42561607827701601630409017686,
    phi_thirtySixAH_42561607827701601630409017687, phi_thirtySixAH_42561607827701601630409017688, phi_thirtySixAH_42561607827701601630409017689,
    phi_thirtySixAH_42561607827701601630409017690, phi_thirtySixAH_42561607827701601630409017691, phi_thirtySixAH_42561607827701601630409017692,
    phi_thirtySixAH_42561607827701601630409017693, phi_thirtySixAH_42561607827701601630409017694, phi_thirtySixAH_42561607827701601630409017695,
    phi_thirtySixAH_42561607827701601630409017696, phi_thirtySixAH_42561607827701601630409017697, phi_thirtySixAH_42561607827701601630409017698,
    phi_thirtySixAH_42561607827701601630409017699]

end TotientTailPeriodKiller
end Erdos249257
