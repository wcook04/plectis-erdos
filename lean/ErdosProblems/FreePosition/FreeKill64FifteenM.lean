import Erdos249257.DiagonalPincerCertificatesT64

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

private def fifteenMFastPow {M : Type*} [Monoid M] (a : M) (n : ℕ) : M :=
  Nat.binaryRec 1 (fun b _ r => if b then r * r * a else r * r) n

private theorem fifteenMFastPow_eq_pow {M : Type*} [Monoid M] (a : M) (n : ℕ) :
    fifteenMFastPow a n = a ^ n := by
  induction n using Nat.binaryRec with
  | zero => simp [fifteenMFastPow, Nat.binaryRec_zero]
  | bit b n ih =>
      rw [fifteenMFastPow, Nat.binaryRec_eq b n (by left; simp)]
      change (if b then fifteenMFastPow a n * fifteenMFastPow a n * a
        else fifteenMFastPow a n * fifteenMFastPow a n) = _
      rw [ih]
      cases b <;> simp [Nat.bit, two_mul, pow_add]

private theorem prime_fifteenM_2 : Nat.Prime 2 := by norm_num
private theorem prime_fifteenM_3 : Nat.Prime 3 := by norm_num
private theorem prime_fifteenM_20117 : Nat.Prime 20117 := by norm_num
private theorem prime_fifteenM_7 : Nat.Prime 7 := by norm_num
private theorem prime_fifteenM_2477 : Nat.Prime 2477 := by norm_num
private theorem prime_fifteenM_633937 : Nat.Prime 633937 := by norm_num
private theorem prime_fifteenM_973727233 : Nat.Prime 973727233 := by
  apply lucas_primality 973727233 (5 : ZMod 973727233)
  · rw [← fifteenMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 9), (3, 1), (633937, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 9), (3, 1), (633937, 1)] : List FactorBlock).map factorBlockValue).prod = 973727233 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fifteenM_2
      · exact prime_fifteenM_3
      · exact prime_fifteenM_633937
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 973727233) ^ 486863616 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (5 : ZMod 973727233) ^ 324575744 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (5 : ZMod 973727233) ^ 1536 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide

private theorem prime_fifteenM_3777013 : Nat.Prime 3777013 := by norm_num
private theorem prime_fifteenM_1450372993 : Nat.Prime 1450372993 := by
  apply lucas_primality 1450372993 (7 : ZMod 1450372993)
  · rw [← fifteenMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 7), (3, 1), (3777013, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 7), (3, 1), (3777013, 1)] : List FactorBlock).map factorBlockValue).prod = 1450372993 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fifteenM_2
      · exact prime_fifteenM_3
      · exact prime_fifteenM_3777013
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 1450372993) ^ 725186496 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (7 : ZMod 1450372993) ^ 483457664 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (7 : ZMod 1450372993) ^ 384 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide

private theorem prime_fifteenM_146923855955513032200547 : Nat.Prime 146923855955513032200547 := by
  apply lucas_primality 146923855955513032200547 (2 : ZMod 146923855955513032200547)
  · rw [← fifteenMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (7, 1), (2477, 1), (973727233, 1), (1450372993, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (7, 1), (2477, 1), (973727233, 1), (1450372993, 1)] : List FactorBlock).map factorBlockValue).prod = 146923855955513032200547 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fifteenM_2
      · exact prime_fifteenM_3
      · exact prime_fifteenM_7
      · exact prime_fifteenM_2477
      · exact prime_fifteenM_973727233
      · exact prime_fifteenM_1450372993
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 146923855955513032200547) ^ 73461927977756516100273 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (2 : ZMod 146923855955513032200547) ^ 48974618651837677400182 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (2 : ZMod 146923855955513032200547) ^ 20989122279359004600078 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (2 : ZMod 146923855955513032200547) ^ 59315242614256371498 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (2 : ZMod 146923855955513032200547) ^ 150888103953762 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (2 : ZMod 146923855955513032200547) ^ 101300738957922 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide

private theorem prime_fifteenM_5 : Nat.Prime 5 := by norm_num
private theorem prime_fifteenM_3923 : Nat.Prime 3923 := by norm_num
private theorem prime_fifteenM_8197093 : Nat.Prime 8197093 := by norm_num
private theorem prime_fifteenM_11 : Nat.Prime 11 := by norm_num
private theorem prime_fifteenM_149 : Nat.Prime 149 := by norm_num
private theorem prime_fifteenM_929 : Nat.Prime 929 := by norm_num
private theorem prime_fifteenM_1796567 : Nat.Prime 1796567 := by norm_num
private theorem prime_fifteenM_110295707065568641 : Nat.Prime 110295707065568641 := by
  apply lucas_primality 110295707065568641 (26 : ZMod 110295707065568641)
  · rw [← fifteenMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 7), (3, 2), (5, 1), (7, 1), (11, 1), (149, 1), (929, 1), (1796567, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 7), (3, 2), (5, 1), (7, 1), (11, 1), (149, 1), (929, 1), (1796567, 1)] : List FactorBlock).map factorBlockValue).prod = 110295707065568641 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fifteenM_2
      · exact prime_fifteenM_3
      · exact prime_fifteenM_5
      · exact prime_fifteenM_7
      · exact prime_fifteenM_11
      · exact prime_fifteenM_149
      · exact prime_fifteenM_929
      · exact prime_fifteenM_1796567
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (26 : ZMod 110295707065568641) ^ 55147853532784320 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (26 : ZMod 110295707065568641) ^ 36765235688522880 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (26 : ZMod 110295707065568641) ^ 22059141413113728 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (26 : ZMod 110295707065568641) ^ 15756529580795520 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (26 : ZMod 110295707065568641) ^ 10026882460506240 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (26 : ZMod 110295707065568641) ^ 740239644735360 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (26 : ZMod 110295707065568641) ^ 118725195980160 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (26 : ZMod 110295707065568641) ^ 61392481920 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide

private theorem prime_fifteenM_1949 : Nat.Prime 1949 := by norm_num
private theorem prime_fifteenM_18481 : Nat.Prime 18481 := by norm_num
private theorem prime_fifteenM_43 : Nat.Prime 43 := by norm_num
private theorem prime_fifteenM_461 : Nat.Prime 461 := by norm_num
private theorem prime_fifteenM_661 : Nat.Prime 661 := by norm_num
private theorem prime_fifteenM_1126858259 : Nat.Prime 1126858259 := by
  apply lucas_primality 1126858259 (2 : ZMod 1126858259)
  · rw [← fifteenMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (43, 2), (461, 1), (661, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (43, 2), (461, 1), (661, 1)] : List FactorBlock).map factorBlockValue).prod = 1126858259 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fifteenM_2
      · exact prime_fifteenM_43
      · exact prime_fifteenM_461
      · exact prime_fifteenM_661
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1126858259) ^ 563429129 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (2 : ZMod 1126858259) ^ 26206006 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (2 : ZMod 1126858259) ^ 2444378 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (2 : ZMod 1126858259) ^ 1704778 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide

private theorem prime_fifteenM_23 : Nat.Prime 23 := by norm_num
private theorem prime_fifteenM_5483 : Nat.Prime 5483 := by norm_num
private theorem prime_fifteenM_15467 : Nat.Prime 15467 := by norm_num
private theorem prime_fifteenM_109229562569 : Nat.Prime 109229562569 := by
  apply lucas_primality 109229562569 (3 : ZMod 109229562569)
  · rw [← fifteenMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (7, 1), (23, 1), (5483, 1), (15467, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (7, 1), (23, 1), (5483, 1), (15467, 1)] : List FactorBlock).map factorBlockValue).prod = 109229562569 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fifteenM_2
      · exact prime_fifteenM_7
      · exact prime_fifteenM_23
      · exact prime_fifteenM_5483
      · exact prime_fifteenM_15467
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 109229562569) ^ 54614781284 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (3 : ZMod 109229562569) ^ 15604223224 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (3 : ZMod 109229562569) ^ 4749111416 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (3 : ZMod 109229562569) ^ 19921496 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (3 : ZMod 109229562569) ^ 7062104 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide

private theorem prime_fifteenM_109 : Nat.Prime 109 := by norm_num
private theorem prime_fifteenM_5013551 : Nat.Prime 5013551 := by norm_num
private theorem prime_fifteenM_393463482481 : Nat.Prime 393463482481 := by
  apply lucas_primality 393463482481 (7 : ZMod 393463482481)
  · rw [← fifteenMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 4), (3, 2), (5, 1), (109, 1), (5013551, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 4), (3, 2), (5, 1), (109, 1), (5013551, 1)] : List FactorBlock).map factorBlockValue).prod = 393463482481 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fifteenM_2
      · exact prime_fifteenM_3
      · exact prime_fifteenM_5
      · exact prime_fifteenM_109
      · exact prime_fifteenM_5013551
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 393463482481) ^ 196731741240 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (7 : ZMod 393463482481) ^ 131154494160 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (7 : ZMod 393463482481) ^ 78692696496 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (7 : ZMod 393463482481) ^ 3609756720 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (7 : ZMod 393463482481) ^ 78480 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide

private theorem prime_fifteenM_31 : Nat.Prime 31 := by norm_num
private theorem prime_fifteenM_17 : Nat.Prime 17 := by norm_num
private theorem prime_fifteenM_19 : Nat.Prime 19 := by norm_num
private theorem prime_fifteenM_9791 : Nat.Prime 9791 := by norm_num
private theorem prime_fifteenM_126499721 : Nat.Prime 126499721 := by
  apply lucas_primality 126499721 (7 : ZMod 126499721)
  · rw [← fifteenMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (5, 1), (17, 1), (19, 1), (9791, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (5, 1), (17, 1), (19, 1), (9791, 1)] : List FactorBlock).map factorBlockValue).prod = 126499721 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fifteenM_2
      · exact prime_fifteenM_5
      · exact prime_fifteenM_17
      · exact prime_fifteenM_19
      · exact prime_fifteenM_9791
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 126499721) ^ 63249860 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (7 : ZMod 126499721) ^ 25299944 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (7 : ZMod 126499721) ^ 7441160 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (7 : ZMod 126499721) ^ 6657880 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (7 : ZMod 126499721) ^ 12920 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide

private theorem prime_fifteenM_46657904094199 : Nat.Prime 46657904094199 := by
  apply lucas_primality 46657904094199 (3 : ZMod 46657904094199)
  · rw [← fifteenMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 2), (31, 1), (661, 1), (126499721, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 2), (31, 1), (661, 1), (126499721, 1)] : List FactorBlock).map factorBlockValue).prod = 46657904094199 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fifteenM_2
      · exact prime_fifteenM_3
      · exact prime_fifteenM_31
      · exact prime_fifteenM_661
      · exact prime_fifteenM_126499721
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 46657904094199) ^ 23328952047099 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (3 : ZMod 46657904094199) ^ 15552634698066 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (3 : ZMod 46657904094199) ^ 1505093680458 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (3 : ZMod 46657904094199) ^ 70586844318 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (3 : ZMod 46657904094199) ^ 368838 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide

private theorem prime_fifteenM_15023845118332079 : Nat.Prime 15023845118332079 := by
  apply lucas_primality 15023845118332079 (7 : ZMod 15023845118332079)
  · rw [← fifteenMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (7, 1), (23, 1), (46657904094199, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (7, 1), (23, 1), (46657904094199, 1)] : List FactorBlock).map factorBlockValue).prod = 15023845118332079 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fifteenM_2
      · exact prime_fifteenM_7
      · exact prime_fifteenM_23
      · exact prime_fifteenM_46657904094199
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 15023845118332079) ^ 7511922559166039 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (7 : ZMod 15023845118332079) ^ 2146263588333154 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (7 : ZMod 15023845118332079) ^ 653210657318786 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (7 : ZMod 15023845118332079) ^ 322 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide

private theorem prime_fifteenM_89 : Nat.Prime 89 := by norm_num
private theorem prime_fifteenM_2503 : Nat.Prime 2503 := by norm_num
private theorem prime_fifteenM_327583 : Nat.Prime 327583 := by norm_num
private theorem prime_fifteenM_137 : Nat.Prime 137 := by norm_num
private theorem prime_fifteenM_283 : Nat.Prime 283 := by norm_num
private theorem prime_fifteenM_13 : Nat.Prime 13 := by norm_num
private theorem prime_fifteenM_1709 : Nat.Prime 1709 := by norm_num
private theorem prime_fifteenM_131702377 : Nat.Prime 131702377 := by
  apply lucas_primality 131702377 (5 : ZMod 131702377)
  · rw [← fifteenMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (3, 1), (13, 2), (19, 1), (1709, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (3, 1), (13, 2), (19, 1), (1709, 1)] : List FactorBlock).map factorBlockValue).prod = 131702377 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fifteenM_2
      · exact prime_fifteenM_3
      · exact prime_fifteenM_13
      · exact prime_fifteenM_19
      · exact prime_fifteenM_1709
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 131702377) ^ 65851188 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (5 : ZMod 131702377) ^ 43900792 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (5 : ZMod 131702377) ^ 10130952 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (5 : ZMod 131702377) ^ 6931704 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (5 : ZMod 131702377) ^ 77064 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide

private theorem prime_fifteenM_30637397152003 : Nat.Prime 30637397152003 := by
  apply lucas_primality 30637397152003 (5 : ZMod 30637397152003)
  · rw [← fifteenMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (137, 1), (283, 1), (131702377, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (137, 1), (283, 1), (131702377, 1)] : List FactorBlock).map factorBlockValue).prod = 30637397152003 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fifteenM_2
      · exact prime_fifteenM_3
      · exact prime_fifteenM_137
      · exact prime_fifteenM_283
      · exact prime_fifteenM_131702377
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 30637397152003) ^ 15318698576001 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (5 : ZMod 30637397152003) ^ 10212465717334 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (5 : ZMod 30637397152003) ^ 223630636146 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (5 : ZMod 30637397152003) ^ 108259353894 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (5 : ZMod 30637397152003) ^ 232626 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide

private theorem prime_fifteenM_183824382912019 : Nat.Prime 183824382912019 := by
  apply lucas_primality 183824382912019 (2 : ZMod 183824382912019)
  · rw [← fifteenMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (30637397152003, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (30637397152003, 1)] : List FactorBlock).map factorBlockValue).prod = 183824382912019 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fifteenM_2
      · exact prime_fifteenM_3
      · exact prime_fifteenM_30637397152003
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 183824382912019) ^ 91912191456009 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (2 : ZMod 183824382912019) ^ 61274794304006 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (2 : ZMod 183824382912019) ^ 6 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide

private theorem prime_fifteenM_2053 : Nat.Prime 2053 := by norm_num
private theorem prime_fifteenM_41 : Nat.Prime 41 := by norm_num
private theorem prime_fifteenM_1427 : Nat.Prime 1427 := by norm_num
private theorem prime_fifteenM_4789 : Nat.Prime 4789 := by norm_num
private theorem prime_fifteenM_1066088869 : Nat.Prime 1066088869 := by
  apply lucas_primality 1066088869 (6 : ZMod 1066088869)
  · rw [← fifteenMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (13, 1), (1427, 1), (4789, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (13, 1), (1427, 1), (4789, 1)] : List FactorBlock).map factorBlockValue).prod = 1066088869 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fifteenM_2
      · exact prime_fifteenM_3
      · exact prime_fifteenM_13
      · exact prime_fifteenM_1427
      · exact prime_fifteenM_4789
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 1066088869) ^ 533044434 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (6 : ZMod 1066088869) ^ 355362956 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (6 : ZMod 1066088869) ^ 82006836 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (6 : ZMod 1066088869) ^ 747084 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (6 : ZMod 1066088869) ^ 222612 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide

private theorem prime_fifteenM_126733 : Nat.Prime 126733 := by norm_num
private theorem prime_fifteenM_57029851 : Nat.Prime 57029851 := by
  apply lucas_primality 57029851 (2 : ZMod 57029851)
  · rw [← fifteenMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 2), (5, 2), (126733, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 2), (5, 2), (126733, 1)] : List FactorBlock).map factorBlockValue).prod = 57029851 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fifteenM_2
      · exact prime_fifteenM_3
      · exact prime_fifteenM_5
      · exact prime_fifteenM_126733
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 57029851) ^ 28514925 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (2 : ZMod 57029851) ^ 19009950 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (2 : ZMod 57029851) ^ 11405970 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (2 : ZMod 57029851) ^ 450 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide

private theorem prime_fifteenM_11177850797 : Nat.Prime 11177850797 := by
  apply lucas_primality 11177850797 (2 : ZMod 11177850797)
  · rw [← fifteenMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (7, 2), (57029851, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (7, 2), (57029851, 1)] : List FactorBlock).map factorBlockValue).prod = 11177850797 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fifteenM_2
      · exact prime_fifteenM_7
      · exact prime_fifteenM_57029851
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 11177850797) ^ 5588925398 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (2 : ZMod 11177850797) ^ 1596835828 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (2 : ZMod 11177850797) ^ 196 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide

private theorem prime_fifteenM_1900234635491 : Nat.Prime 1900234635491 := by
  apply lucas_primality 1900234635491 (2 : ZMod 1900234635491)
  · rw [← fifteenMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 1), (17, 1), (11177850797, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 1), (17, 1), (11177850797, 1)] : List FactorBlock).map factorBlockValue).prod = 1900234635491 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fifteenM_2
      · exact prime_fifteenM_5
      · exact prime_fifteenM_17
      · exact prime_fifteenM_11177850797
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1900234635491) ^ 950117317745 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (2 : ZMod 1900234635491) ^ 380046927098 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (2 : ZMod 1900234635491) ^ 111778507970 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (2 : ZMod 1900234635491) ^ 170 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide

private theorem prime_fifteenM_332234314915177301747357 : Nat.Prime 332234314915177301747357 := by
  apply lucas_primality 332234314915177301747357 (3 : ZMod 332234314915177301747357)
  · rw [← fifteenMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (41, 1), (1066088869, 1), (1900234635491, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (41, 1), (1066088869, 1), (1900234635491, 1)] : List FactorBlock).map factorBlockValue).prod = 332234314915177301747357 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fifteenM_2
      · exact prime_fifteenM_41
      · exact prime_fifteenM_1066088869
      · exact prime_fifteenM_1900234635491
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 332234314915177301747357) ^ 166117157457588650873678 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (3 : ZMod 332234314915177301747357) ^ 8103275973540909798716 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (3 : ZMod 332234314915177301747357) ^ 311638480220524 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (3 : ZMod 332234314915177301747357) ^ 174838574516 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide

private theorem prime_fifteenM_8638092187794609845431283 : Nat.Prime 8638092187794609845431283 := by
  apply lucas_primality 8638092187794609845431283 (2 : ZMod 8638092187794609845431283)
  · rw [← fifteenMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (13, 1), (332234314915177301747357, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (13, 1), (332234314915177301747357, 1)] : List FactorBlock).map factorBlockValue).prod = 8638092187794609845431283 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fifteenM_2
      · exact prime_fifteenM_13
      · exact prime_fifteenM_332234314915177301747357
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 8638092187794609845431283) ^ 4319046093897304922715641 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (2 : ZMod 8638092187794609845431283) ^ 664468629830354603494714 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (2 : ZMod 8638092187794609845431283) ^ 26 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide

private theorem prime_fifteenM_29 : Nat.Prime 29 := by norm_num
private theorem prime_fifteenM_37 : Nat.Prime 37 := by norm_num
private theorem prime_fifteenM_47 : Nat.Prime 47 := by norm_num
private theorem prime_fifteenM_53 : Nat.Prime 53 := by norm_num
private theorem prime_fifteenM_59 : Nat.Prime 59 := by norm_num
private theorem prime_fifteenM_61 : Nat.Prime 61 := by norm_num
private theorem prime_fifteenM_883 : Nat.Prime 883 := by norm_num
private theorem prime_fifteenM_1535377 : Nat.Prime 1535377 := by norm_num
private theorem prime_fifteenM_2497849 : Nat.Prime 2497849 := by norm_num
private theorem prime_fifteenM_571 : Nat.Prime 571 := by norm_num
private theorem prime_fifteenM_129209 : Nat.Prime 129209 := by norm_num
private theorem prime_fifteenM_1032896747 : Nat.Prime 1032896747 := by
  apply lucas_primality 1032896747 (2 : ZMod 1032896747)
  · rw [← fifteenMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (7, 1), (571, 1), (129209, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (7, 1), (571, 1), (129209, 1)] : List FactorBlock).map factorBlockValue).prod = 1032896747 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fifteenM_2
      · exact prime_fifteenM_7
      · exact prime_fifteenM_571
      · exact prime_fifteenM_129209
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1032896747) ^ 516448373 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (2 : ZMod 1032896747) ^ 147556678 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (2 : ZMod 1032896747) ^ 1808926 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (2 : ZMod 1032896747) ^ 7994 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide

private theorem prime_fifteenM_13080701940447819211 : Nat.Prime 13080701940447819211 := by
  apply lucas_primality 13080701940447819211 (10 : ZMod 13080701940447819211)
  · rw [← fifteenMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (5, 1), (13, 2), (2497849, 1), (1032896747, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (5, 1), (13, 2), (2497849, 1), (1032896747, 1)] : List FactorBlock).map factorBlockValue).prod = 13080701940447819211 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fifteenM_2
      · exact prime_fifteenM_3
      · exact prime_fifteenM_5
      · exact prime_fifteenM_13
      · exact prime_fifteenM_2497849
      · exact prime_fifteenM_1032896747
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 13080701940447819211) ^ 6540350970223909605 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (10 : ZMod 13080701940447819211) ^ 4360233980149273070 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (10 : ZMod 13080701940447819211) ^ 2616140388089563842 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (10 : ZMod 13080701940447819211) ^ 1006207841572909170 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (10 : ZMod 13080701940447819211) ^ 5236786507290 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (10 : ZMod 13080701940447819211) ^ 12664094430 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide

private theorem prime_fifteenM_2293 : Nat.Prime 2293 := by norm_num
private theorem prime_fifteenM_8810759 : Nat.Prime 8810759 := by norm_num
private theorem prime_fifteenM_173 : Nat.Prime 173 := by norm_num
private theorem prime_fifteenM_127 : Nat.Prime 127 := by norm_num
private theorem prime_fifteenM_383 : Nat.Prime 383 := by norm_num
private theorem prime_fifteenM_132383 : Nat.Prime 132383 := by norm_num
private theorem prime_fifteenM_45274987 : Nat.Prime 45274987 := by
  apply lucas_primality 45274987 (2 : ZMod 45274987)
  · rw [← fifteenMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 2), (19, 1), (132383, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 2), (19, 1), (132383, 1)] : List FactorBlock).map factorBlockValue).prod = 45274987 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fifteenM_2
      · exact prime_fifteenM_3
      · exact prime_fifteenM_19
      · exact prime_fifteenM_132383
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 45274987) ^ 22637493 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (2 : ZMod 45274987) ^ 15091662 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (2 : ZMod 45274987) ^ 2382894 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (2 : ZMod 45274987) ^ 342 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide

private theorem prime_fifteenM_13213323856003 : Nat.Prime 13213323856003 := by
  apply lucas_primality 13213323856003 (2 : ZMod 13213323856003)
  · rw [← fifteenMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (127, 1), (383, 1), (45274987, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (127, 1), (383, 1), (45274987, 1)] : List FactorBlock).map factorBlockValue).prod = 13213323856003 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fifteenM_2
      · exact prime_fifteenM_3
      · exact prime_fifteenM_127
      · exact prime_fifteenM_383
      · exact prime_fifteenM_45274987
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 13213323856003) ^ 6606661928001 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (2 : ZMod 13213323856003) ^ 4404441285334 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (2 : ZMod 13213323856003) ^ 104041920126 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (2 : ZMod 13213323856003) ^ 34499540094 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (2 : ZMod 13213323856003) ^ 291846 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide

private theorem prime_fifteenM_18287240216708153 : Nat.Prime 18287240216708153 := by
  apply lucas_primality 18287240216708153 (3 : ZMod 18287240216708153)
  · rw [← fifteenMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (173, 1), (13213323856003, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (173, 1), (13213323856003, 1)] : List FactorBlock).map factorBlockValue).prod = 18287240216708153 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fifteenM_2
      · exact prime_fifteenM_173
      · exact prime_fifteenM_13213323856003
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 18287240216708153) ^ 9143620108354076 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (3 : ZMod 18287240216708153) ^ 105706590848024 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (3 : ZMod 18287240216708153) ^ 1384 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide

private theorem prime_fifteenM_36574480433416307 : Nat.Prime 36574480433416307 := by
  apply lucas_primality 36574480433416307 (2 : ZMod 36574480433416307)
  · rw [← fifteenMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (18287240216708153, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (18287240216708153, 1)] : List FactorBlock).map factorBlockValue).prod = 36574480433416307 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_fifteenM_2
      · exact prime_fifteenM_18287240216708153
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 36574480433416307) ^ 18287240216708153 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (2 : ZMod 36574480433416307) ^ 2 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide

private theorem prime_fifteenM_3866987191788559531764157 : Nat.Prime 3866987191788559531764157 := by
  apply lucas_primality 3866987191788559531764157 (5 : ZMod 3866987191788559531764157)
  · rw [← fifteenMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (8810759, 1), (36574480433416307, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (8810759, 1), (36574480433416307, 1)] : List FactorBlock).map factorBlockValue).prod = 3866987191788559531764157 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fifteenM_2
      · exact prime_fifteenM_3
      · exact prime_fifteenM_8810759
      · exact prime_fifteenM_36574480433416307
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 3866987191788559531764157) ^ 1933493595894279765882078 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (5 : ZMod 3866987191788559531764157) ^ 1288995730596186510588052 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (5 : ZMod 3866987191788559531764157) ^ 438893765200995684 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (5 : ZMod 3866987191788559531764157) ^ 105729108 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide

private theorem prime_fifteenM_143669 : Nat.Prime 143669 := by norm_num
private theorem prime_fifteenM_349 : Nat.Prime 349 := by norm_num
private theorem prime_fifteenM_619 : Nat.Prime 619 := by norm_num
private theorem prime_fifteenM_10687 : Nat.Prime 10687 := by norm_num
private theorem prime_fifteenM_13852339783 : Nat.Prime 13852339783 := by
  apply lucas_primality 13852339783 (3 : ZMod 13852339783)
  · rw [← fifteenMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (349, 1), (619, 1), (10687, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (349, 1), (619, 1), (10687, 1)] : List FactorBlock).map factorBlockValue).prod = 13852339783 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fifteenM_2
      · exact prime_fifteenM_3
      · exact prime_fifteenM_349
      · exact prime_fifteenM_619
      · exact prime_fifteenM_10687
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 13852339783) ^ 6926169891 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (3 : ZMod 13852339783) ^ 4617446594 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (3 : ZMod 13852339783) ^ 39691518 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (3 : ZMod 13852339783) ^ 22378578 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (3 : ZMod 13852339783) ^ 1296186 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide

private theorem prime_fifteenM_761 : Nat.Prime 761 := by norm_num
private theorem prime_fifteenM_5801 : Nat.Prime 5801 := by norm_num
private theorem prime_fifteenM_1951572421 : Nat.Prime 1951572421 := by
  apply lucas_primality 1951572421 (10 : ZMod 1951572421)
  · rw [← fifteenMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 3), (5, 1), (7, 1), (89, 1), (5801, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 3), (5, 1), (7, 1), (89, 1), (5801, 1)] : List FactorBlock).map factorBlockValue).prod = 1951572421 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fifteenM_2
      · exact prime_fifteenM_3
      · exact prime_fifteenM_5
      · exact prime_fifteenM_7
      · exact prime_fifteenM_89
      · exact prime_fifteenM_5801
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 1951572421) ^ 975786210 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (10 : ZMod 1951572421) ^ 650524140 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (10 : ZMod 1951572421) ^ 390314484 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (10 : ZMod 1951572421) ^ 278796060 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (10 : ZMod 1951572421) ^ 21927780 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (10 : ZMod 1951572421) ^ 336420 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide

private theorem prime_fifteenM_2970293224763 : Nat.Prime 2970293224763 := by
  apply lucas_primality 2970293224763 (2 : ZMod 2970293224763)
  · rw [← fifteenMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (761, 1), (1951572421, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (761, 1), (1951572421, 1)] : List FactorBlock).map factorBlockValue).prod = 2970293224763 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fifteenM_2
      · exact prime_fifteenM_761
      · exact prime_fifteenM_1951572421
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 2970293224763) ^ 1485146612381 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (2 : ZMod 2970293224763) ^ 3903144842 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (2 : ZMod 2970293224763) ^ 1522 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide

private theorem prime_fifteenM_241 : Nat.Prime 241 := by norm_num
private theorem prime_fifteenM_1701391 : Nat.Prime 1701391 := by norm_num
private theorem prime_fifteenM_11484449 : Nat.Prime 11484449 := by norm_num
private theorem prime_fifteenM_257 : Nat.Prime 257 := by norm_num
private theorem prime_fifteenM_1896161 : Nat.Prime 1896161 := by norm_num
private theorem prime_fifteenM_1831691527 : Nat.Prime 1831691527 := by
  apply lucas_primality 1831691527 (5 : ZMod 1831691527)
  · rw [← fifteenMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (7, 1), (23, 1), (1896161, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (7, 1), (23, 1), (1896161, 1)] : List FactorBlock).map factorBlockValue).prod = 1831691527 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fifteenM_2
      · exact prime_fifteenM_3
      · exact prime_fifteenM_7
      · exact prime_fifteenM_23
      · exact prime_fifteenM_1896161
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 1831691527) ^ 915845763 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (5 : ZMod 1831691527) ^ 610563842 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (5 : ZMod 1831691527) ^ 261670218 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (5 : ZMod 1831691527) ^ 79638762 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (5 : ZMod 1831691527) ^ 966 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide

private theorem prime_fifteenM_941489444879 : Nat.Prime 941489444879 := by
  apply lucas_primality 941489444879 (7 : ZMod 941489444879)
  · rw [← fifteenMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (257, 1), (1831691527, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (257, 1), (1831691527, 1)] : List FactorBlock).map factorBlockValue).prod = 941489444879 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fifteenM_2
      · exact prime_fifteenM_257
      · exact prime_fifteenM_1831691527
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 941489444879) ^ 470744722439 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (7 : ZMod 941489444879) ^ 3663383054 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (7 : ZMod 941489444879) ^ 514 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide

private theorem prime_fifteenM_71 : Nat.Prime 71 := by norm_num
private theorem prime_fifteenM_114593 : Nat.Prime 114593 := by norm_num
private theorem prime_fifteenM_42857783 : Nat.Prime 42857783 := by
  apply lucas_primality 42857783 (5 : ZMod 42857783)
  · rw [← fifteenMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (11, 1), (17, 1), (114593, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (11, 1), (17, 1), (114593, 1)] : List FactorBlock).map factorBlockValue).prod = 42857783 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fifteenM_2
      · exact prime_fifteenM_11
      · exact prime_fifteenM_17
      · exact prime_fifteenM_114593
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 42857783) ^ 21428891 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (5 : ZMod 42857783) ^ 3896162 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (5 : ZMod 42857783) ^ 2521046 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (5 : ZMod 42857783) ^ 374 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide

private theorem prime_fifteenM_30429025931 : Nat.Prime 30429025931 := by
  apply lucas_primality 30429025931 (2 : ZMod 30429025931)
  · rw [← fifteenMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 1), (71, 1), (42857783, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 1), (71, 1), (42857783, 1)] : List FactorBlock).map factorBlockValue).prod = 30429025931 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fifteenM_2
      · exact prime_fifteenM_5
      · exact prime_fifteenM_71
      · exact prime_fifteenM_42857783
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 30429025931) ^ 15214512965 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (2 : ZMod 30429025931) ^ 6085805186 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (2 : ZMod 30429025931) ^ 428577830 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (2 : ZMod 30429025931) ^ 710 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide

private theorem prime_fifteenM_81047 : Nat.Prime 81047 := by norm_num
private theorem prime_fifteenM_14999741 : Nat.Prime 14999741 := by norm_num
private theorem prime_fifteenM_11655978276633277 : Nat.Prime 11655978276633277 := by
  apply lucas_primality 11655978276633277 (2 : ZMod 11655978276633277)
  · rw [← fifteenMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (17, 1), (47, 1), (81047, 1), (14999741, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (17, 1), (47, 1), (81047, 1), (14999741, 1)] : List FactorBlock).map factorBlockValue).prod = 11655978276633277 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fifteenM_2
      · exact prime_fifteenM_3
      · exact prime_fifteenM_17
      · exact prime_fifteenM_47
      · exact prime_fifteenM_81047
      · exact prime_fifteenM_14999741
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 11655978276633277) ^ 5827989138316638 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (2 : ZMod 11655978276633277) ^ 3885326092211092 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (2 : ZMod 11655978276633277) ^ 685645780978428 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (2 : ZMod 11655978276633277) ^ 247999537800708 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (2 : ZMod 11655978276633277) ^ 143817516708 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (2 : ZMod 11655978276633277) ^ 777078636 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide

private theorem prime_fifteenM_116559782766332771 : Nat.Prime 116559782766332771 := by
  apply lucas_primality 116559782766332771 (2 : ZMod 116559782766332771)
  · rw [← fifteenMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 1), (11655978276633277, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 1), (11655978276633277, 1)] : List FactorBlock).map factorBlockValue).prod = 116559782766332771 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fifteenM_2
      · exact prime_fifteenM_5
      · exact prime_fifteenM_11655978276633277
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 116559782766332771) ^ 58279891383166385 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (2 : ZMod 116559782766332771) ^ 23311956553266554 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (2 : ZMod 116559782766332771) ^ 10 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide

private theorem prime_fifteenM_223 : Nat.Prime 223 := by norm_num
private theorem prime_fifteenM_5113 : Nat.Prime 5113 := by norm_num
private theorem prime_fifteenM_101287 : Nat.Prime 101287 := by norm_num
private theorem prime_fifteenM_656951 : Nat.Prime 656951 := by norm_num
private theorem prime_fifteenM_2669767 : Nat.Prime 2669767 := by norm_num
private theorem prime_fifteenM_42716273 : Nat.Prime 42716273 := by
  apply lucas_primality 42716273 (3 : ZMod 42716273)
  · rw [← fifteenMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 4), (2669767, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 4), (2669767, 1)] : List FactorBlock).map factorBlockValue).prod = 42716273 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_fifteenM_2
      · exact prime_fifteenM_2669767
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 42716273) ^ 21358136 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (3 : ZMod 42716273) ^ 16 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide

private theorem prime_fifteenM_25592998416424177 : Nat.Prime 25592998416424177 := by
  apply lucas_primality 25592998416424177 (5 : ZMod 25592998416424177)
  · rw [← fifteenMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 4), (3, 1), (19, 1), (656951, 1), (42716273, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 4), (3, 1), (19, 1), (656951, 1), (42716273, 1)] : List FactorBlock).map factorBlockValue).prod = 25592998416424177 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fifteenM_2
      · exact prime_fifteenM_3
      · exact prime_fifteenM_19
      · exact prime_fifteenM_656951
      · exact prime_fifteenM_42716273
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 25592998416424177) ^ 12796499208212088 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (5 : ZMod 25592998416424177) ^ 8530999472141392 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (5 : ZMod 25592998416424177) ^ 1346999916653904 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (5 : ZMod 25592998416424177) ^ 38957240976 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (5 : ZMod 25592998416424177) ^ 599139312 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide

private theorem prime_fifteenM_131 : Nat.Prime 131 := by norm_num
private theorem prime_fifteenM_60607 : Nat.Prime 60607 := by norm_num
private theorem prime_fifteenM_5301391 : Nat.Prime 5301391 := by norm_num
private theorem prime_fifteenM_275672333 : Nat.Prime 275672333 := by
  apply lucas_primality 275672333 (3 : ZMod 275672333)
  · rw [← fifteenMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (13, 1), (5301391, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (13, 1), (5301391, 1)] : List FactorBlock).map factorBlockValue).prod = 275672333 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fifteenM_2
      · exact prime_fifteenM_13
      · exact prime_fifteenM_5301391
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 275672333) ^ 137836166 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (3 : ZMod 275672333) ^ 21205564 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (3 : ZMod 275672333) ^ 52 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide

private theorem prime_fifteenM_56779 : Nat.Prime 56779 := by norm_num
private theorem prime_fifteenM_27481037 : Nat.Prime 27481037 := by
  apply lucas_primality 27481037 (2 : ZMod 27481037)
  · rw [← fifteenMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (11, 2), (56779, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (11, 2), (56779, 1)] : List FactorBlock).map factorBlockValue).prod = 27481037 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fifteenM_2
      · exact prime_fifteenM_11
      · exact prime_fifteenM_56779
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 27481037) ^ 13740518 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (2 : ZMod 27481037) ^ 2498276 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (2 : ZMod 27481037) ^ 484 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide

private theorem prime_fifteenM_1157501278441 : Nat.Prime 1157501278441 := by
  apply lucas_primality 1157501278441 (11 : ZMod 1157501278441)
  · rw [← fifteenMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (3, 4), (5, 1), (13, 1), (27481037, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (3, 4), (5, 1), (13, 1), (27481037, 1)] : List FactorBlock).map factorBlockValue).prod = 1157501278441 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fifteenM_2
      · exact prime_fifteenM_3
      · exact prime_fifteenM_5
      · exact prime_fifteenM_13
      · exact prime_fifteenM_27481037
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 1157501278441) ^ 578750639220 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (11 : ZMod 1157501278441) ^ 385833759480 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (11 : ZMod 1157501278441) ^ 231500255688 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (11 : ZMod 1157501278441) ^ 89038559880 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (11 : ZMod 1157501278441) ^ 42120 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide

private theorem prime_fifteenM_211 : Nat.Prime 211 := by norm_num
private theorem prime_fifteenM_28751 : Nat.Prime 28751 := by norm_num
private theorem prime_fifteenM_75389 : Nat.Prime 75389 := by norm_num
private theorem prime_fifteenM_503 : Nat.Prime 503 := by norm_num
private theorem prime_fifteenM_13901 : Nat.Prime 13901 := by norm_num
private theorem prime_fifteenM_13913 : Nat.Prime 13913 := by norm_num
private theorem prime_fifteenM_66917996099 : Nat.Prime 66917996099 := by
  apply lucas_primality 66917996099 (2 : ZMod 66917996099)
  · rw [← fifteenMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (173, 1), (13901, 1), (13913, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (173, 1), (13901, 1), (13913, 1)] : List FactorBlock).map factorBlockValue).prod = 66917996099 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fifteenM_2
      · exact prime_fifteenM_173
      · exact prime_fifteenM_13901
      · exact prime_fifteenM_13913
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 66917996099) ^ 33458998049 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (2 : ZMod 66917996099) ^ 386809226 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (2 : ZMod 66917996099) ^ 4813898 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (2 : ZMod 66917996099) ^ 4809746 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide

private theorem prime_fifteenM_4847004293442769 : Nat.Prime 4847004293442769 := by
  apply lucas_primality 4847004293442769 (7 : ZMod 4847004293442769)
  · rw [← fifteenMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 4), (3, 2), (503, 1), (66917996099, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 4), (3, 2), (503, 1), (66917996099, 1)] : List FactorBlock).map factorBlockValue).prod = 4847004293442769 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fifteenM_2
      · exact prime_fifteenM_3
      · exact prime_fifteenM_503
      · exact prime_fifteenM_66917996099
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 4847004293442769) ^ 2423502146721384 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (7 : ZMod 4847004293442769) ^ 1615668097814256 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (7 : ZMod 4847004293442769) ^ 9636191438256 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (7 : ZMod 4847004293442769) ^ 72432 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide

private theorem prime_fifteenM_73 : Nat.Prime 73 := by norm_num
private theorem prime_fifteenM_13737811 : Nat.Prime 13737811 := by norm_num
private theorem prime_fifteenM_3439229 : Nat.Prime 3439229 := by norm_num
private theorem prime_fifteenM_68784581 : Nat.Prime 68784581 := by
  apply lucas_primality 68784581 (3 : ZMod 68784581)
  · rw [← fifteenMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (5, 1), (3439229, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (5, 1), (3439229, 1)] : List FactorBlock).map factorBlockValue).prod = 68784581 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fifteenM_2
      · exact prime_fifteenM_5
      · exact prime_fifteenM_3439229
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 68784581) ^ 34392290 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (3 : ZMod 68784581) ^ 13756916 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (3 : ZMod 68784581) ^ 20 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide

private theorem prime_fifteenM_15558227 : Nat.Prime 15558227 := by norm_num
private theorem prime_fifteenM_840144259 : Nat.Prime 840144259 := by
  apply lucas_primality 840144259 (2 : ZMod 840144259)
  · rw [← fifteenMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 3), (15558227, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 3), (15558227, 1)] : List FactorBlock).map factorBlockValue).prod = 840144259 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fifteenM_2
      · exact prime_fifteenM_3
      · exact prime_fifteenM_15558227
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 840144259) ^ 420072129 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (2 : ZMod 840144259) ^ 280048086 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (2 : ZMod 840144259) ^ 54 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide

private theorem prime_fifteenM_28564904807 : Nat.Prime 28564904807 := by
  apply lucas_primality 28564904807 (5 : ZMod 28564904807)
  · rw [← fifteenMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (17, 1), (840144259, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (17, 1), (840144259, 1)] : List FactorBlock).map factorBlockValue).prod = 28564904807 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fifteenM_2
      · exact prime_fifteenM_17
      · exact prime_fifteenM_840144259
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 28564904807) ^ 14282452403 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (5 : ZMod 28564904807) ^ 1680288518 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (5 : ZMod 28564904807) ^ 34 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide

private theorem prime_fifteenM_8233 : Nat.Prime 8233 := by norm_num
private theorem prime_fifteenM_93811 : Nat.Prime 93811 := by norm_num
private theorem prime_fifteenM_8274073 : Nat.Prime 8274073 := by norm_num
private theorem prime_fifteenM_1429 : Nat.Prime 1429 := by norm_num
private theorem prime_fifteenM_217223 : Nat.Prime 217223 := by norm_num
private theorem prime_fifteenM_277508030299 : Nat.Prime 277508030299 := by
  apply lucas_primality 277508030299 (3 : ZMod 277508030299)
  · rw [← fifteenMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (149, 1), (1429, 1), (217223, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (149, 1), (1429, 1), (217223, 1)] : List FactorBlock).map factorBlockValue).prod = 277508030299 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fifteenM_2
      · exact prime_fifteenM_3
      · exact prime_fifteenM_149
      · exact prime_fifteenM_1429
      · exact prime_fifteenM_217223
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 277508030299) ^ 138754015149 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (3 : ZMod 277508030299) ^ 92502676766 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (3 : ZMod 277508030299) ^ 1862470002 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (3 : ZMod 277508030299) ^ 194197362 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (3 : ZMod 277508030299) ^ 1277526 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide

private theorem prime_fifteenM_499 : Nat.Prime 499 := by norm_num
private theorem prime_fifteenM_375101 : Nat.Prime 375101 := by norm_num
private theorem prime_fifteenM_433 : Nat.Prime 433 := by norm_num
private theorem prime_fifteenM_7910317 : Nat.Prime 7910317 := by norm_num
private theorem prime_fifteenM_16744068585947 : Nat.Prime 16744068585947 := by
  apply lucas_primality 16744068585947 (2 : ZMod 16744068585947)
  · rw [← fifteenMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (13, 1), (17, 1), (4789, 1), (7910317, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (13, 1), (17, 1), (4789, 1), (7910317, 1)] : List FactorBlock).map factorBlockValue).prod = 16744068585947 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fifteenM_2
      · exact prime_fifteenM_13
      · exact prime_fifteenM_17
      · exact prime_fifteenM_4789
      · exact prime_fifteenM_7910317
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 16744068585947) ^ 8372034292973 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (2 : ZMod 16744068585947) ^ 1288005275842 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (2 : ZMod 16744068585947) ^ 984945210938 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (2 : ZMod 16744068585947) ^ 3496360114 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (2 : ZMod 16744068585947) ^ 2116738 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide

private theorem prime_fifteenM_783019623353225509 : Nat.Prime 783019623353225509 := by
  apply lucas_primality 783019623353225509 (2 : ZMod 783019623353225509)
  · rw [← fifteenMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 3), (433, 1), (16744068585947, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 3), (433, 1), (16744068585947, 1)] : List FactorBlock).map factorBlockValue).prod = 783019623353225509 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fifteenM_2
      · exact prime_fifteenM_3
      · exact prime_fifteenM_433
      · exact prime_fifteenM_16744068585947
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 783019623353225509) ^ 391509811676612754 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (2 : ZMod 783019623353225509) ^ 261006541117741836 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (2 : ZMod 783019623353225509) ^ 1808359407282276 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (2 : ZMod 783019623353225509) ^ 46764 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide

private theorem prime_fifteenM_1477833605128527834389202001 : Nat.Prime 1477833605128527834389202001 := by
  apply lucas_primality 1477833605128527834389202001 (107 : ZMod 1477833605128527834389202001)
  · rw [← fifteenMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 4), (3, 3), (5, 3), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 4), (3, 3), (5, 3), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod = 1477833605128527834389202001 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fifteenM_2
      · exact prime_fifteenM_3
      · exact prime_fifteenM_5
      · exact prime_fifteenM_7
      · exact prime_fifteenM_11
      · exact prime_fifteenM_13
      · exact prime_fifteenM_17
      · exact prime_fifteenM_19
      · exact prime_fifteenM_23
      · exact prime_fifteenM_29
      · exact prime_fifteenM_31
      · exact prime_fifteenM_37
      · exact prime_fifteenM_41
      · exact prime_fifteenM_43
      · exact prime_fifteenM_47
      · exact prime_fifteenM_53
      · exact prime_fifteenM_59
      · exact prime_fifteenM_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (107 : ZMod 1477833605128527834389202001) ^ 738916802564263917194601000 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (107 : ZMod 1477833605128527834389202001) ^ 492611201709509278129734000 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (107 : ZMod 1477833605128527834389202001) ^ 295566721025705566877840400 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (107 : ZMod 1477833605128527834389202001) ^ 211119086446932547769886000 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (107 : ZMod 1477833605128527834389202001) ^ 134348509557138894035382000 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (107 : ZMod 1477833605128527834389202001) ^ 113679508086809833414554000 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (107 : ZMod 1477833605128527834389202001) ^ 86931388536972225552306000 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (107 : ZMod 1477833605128527834389202001) ^ 77780716059396201809958000 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (107 : ZMod 1477833605128527834389202001) ^ 64253635005588166712574000 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (107 : ZMod 1477833605128527834389202001) ^ 50959779487190614978938000 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (107 : ZMod 1477833605128527834389202001) ^ 47672051778339607560942000 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (107 : ZMod 1477833605128527834389202001) ^ 39941448787257509037546000 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (107 : ZMod 1477833605128527834389202001) ^ 36044722076305556936322000 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (107 : ZMod 1477833605128527834389202001) ^ 34368223375082042660214000 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (107 : ZMod 1477833605128527834389202001) ^ 31443268194223996476366000 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (107 : ZMod 1477833605128527834389202001) ^ 27883652926953355365834000 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (107 : ZMod 1477833605128527834389202001) ^ 25048027205568268379478000 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (107 : ZMod 1477833605128527834389202001) ^ 24226780411943079252282000 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide

private theorem prime_fifteenM_229 : Nat.Prime 229 := by norm_num
private theorem prime_fifteenM_887599 : Nat.Prime 887599 := by norm_num
private theorem prime_fifteenM_3448607 : Nat.Prime 3448607 := by norm_num
private theorem prime_fifteenM_1779481213 : Nat.Prime 1779481213 := by
  apply lucas_primality 1779481213 (2 : ZMod 1779481213)
  · rw [← fifteenMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (43, 1), (3448607, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (43, 1), (3448607, 1)] : List FactorBlock).map factorBlockValue).prod = 1779481213 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fifteenM_2
      · exact prime_fifteenM_3
      · exact prime_fifteenM_43
      · exact prime_fifteenM_3448607
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1779481213) ^ 889740606 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (2 : ZMod 1779481213) ^ 593160404 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (2 : ZMod 1779481213) ^ 41383284 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (2 : ZMod 1779481213) ^ 516 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide

private theorem prime_fifteenM_6759017 : Nat.Prime 6759017 := by norm_num
private theorem prime_fifteenM_3771531487 : Nat.Prime 3771531487 := by
  apply lucas_primality 3771531487 (3 : ZMod 3771531487)
  · rw [← fifteenMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 2), (31, 1), (6759017, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 2), (31, 1), (6759017, 1)] : List FactorBlock).map factorBlockValue).prod = 3771531487 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fifteenM_2
      · exact prime_fifteenM_3
      · exact prime_fifteenM_31
      · exact prime_fifteenM_6759017
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 3771531487) ^ 1885765743 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (3 : ZMod 3771531487) ^ 1257177162 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (3 : ZMod 3771531487) ^ 121662306 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (3 : ZMod 3771531487) ^ 558 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide

private theorem prime_fifteenM_36587 : Nat.Prime 36587 := by norm_num
private theorem prime_fifteenM_347 : Nat.Prime 347 := by norm_num
private theorem prime_fifteenM_787 : Nat.Prime 787 := by norm_num
private theorem prime_fifteenM_1361 : Nat.Prime 1361 := by norm_num
private theorem prime_fifteenM_38559853 : Nat.Prime 38559853 := by
  apply lucas_primality 38559853 (5 : ZMod 38559853)
  · rw [← fifteenMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 2), (787, 1), (1361, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 2), (787, 1), (1361, 1)] : List FactorBlock).map factorBlockValue).prod = 38559853 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fifteenM_2
      · exact prime_fifteenM_3
      · exact prime_fifteenM_787
      · exact prime_fifteenM_1361
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 38559853) ^ 19279926 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (5 : ZMod 38559853) ^ 12853284 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (5 : ZMod 38559853) ^ 48996 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (5 : ZMod 38559853) ^ 28332 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide

private theorem prime_fifteenM_107042151929 : Nat.Prime 107042151929 := by
  apply lucas_primality 107042151929 (3 : ZMod 107042151929)
  · rw [← fifteenMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (347, 1), (38559853, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (347, 1), (38559853, 1)] : List FactorBlock).map factorBlockValue).prod = 107042151929 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fifteenM_2
      · exact prime_fifteenM_347
      · exact prime_fifteenM_38559853
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 107042151929) ^ 53521075964 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (3 : ZMod 107042151929) ^ 308478824 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (3 : ZMod 107042151929) ^ 2776 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide

private theorem prime_fifteenM_3719 : Nat.Prime 3719 := by norm_num
private theorem prime_fifteenM_1610561 : Nat.Prime 1610561 := by norm_num
private theorem prime_fifteenM_323442523387 : Nat.Prime 323442523387 := by
  apply lucas_primality 323442523387 (2 : ZMod 323442523387)
  · rw [← fifteenMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 3), (3719, 1), (1610561, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 3), (3719, 1), (1610561, 1)] : List FactorBlock).map factorBlockValue).prod = 323442523387 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fifteenM_2
      · exact prime_fifteenM_3
      · exact prime_fifteenM_3719
      · exact prime_fifteenM_1610561
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 323442523387) ^ 161721261693 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (2 : ZMod 323442523387) ^ 107814174462 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (2 : ZMod 323442523387) ^ 86970294 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (2 : ZMod 323442523387) ^ 200826 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide

private theorem prime_fifteenM_103 : Nat.Prime 103 := by norm_num
private theorem prime_fifteenM_5009 : Nat.Prime 5009 := by norm_num
private theorem prime_fifteenM_107 : Nat.Prime 107 := by norm_num
private theorem prime_fifteenM_61717 : Nat.Prime 61717 := by norm_num
private theorem prime_fifteenM_35279 : Nat.Prime 35279 := by norm_num
private theorem prime_fifteenM_7190123 : Nat.Prime 7190123 := by norm_num
private theorem prime_fifteenM_1521962095903 : Nat.Prime 1521962095903 := by
  apply lucas_primality 1521962095903 (3 : ZMod 1521962095903)
  · rw [← fifteenMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (35279, 1), (7190123, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (35279, 1), (7190123, 1)] : List FactorBlock).map factorBlockValue).prod = 1521962095903 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fifteenM_2
      · exact prime_fifteenM_3
      · exact prime_fifteenM_35279
      · exact prime_fifteenM_7190123
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1521962095903) ^ 760981047951 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (3 : ZMod 1521962095903) ^ 507320698634 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (3 : ZMod 1521962095903) ^ 43140738 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (3 : ZMod 1521962095903) ^ 211674 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide

private theorem prime_fifteenM_563585608037072707 : Nat.Prime 563585608037072707 := by
  apply lucas_primality 563585608037072707 (3 : ZMod 563585608037072707)
  · rw [← fifteenMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (61717, 1), (1521962095903, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (61717, 1), (1521962095903, 1)] : List FactorBlock).map factorBlockValue).prod = 563585608037072707 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fifteenM_2
      · exact prime_fifteenM_3
      · exact prime_fifteenM_61717
      · exact prime_fifteenM_1521962095903
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 563585608037072707) ^ 281792804018536353 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (3 : ZMod 563585608037072707) ^ 187861869345690902 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (3 : ZMod 563585608037072707) ^ 9131772575418 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (3 : ZMod 563585608037072707) ^ 370302 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide

private theorem prime_fifteenM_2291539082278737626663 : Nat.Prime 2291539082278737626663 := by
  apply lucas_primality 2291539082278737626663 (10 : ZMod 2291539082278737626663)
  · rw [← fifteenMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (19, 1), (107, 1), (563585608037072707, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (19, 1), (107, 1), (563585608037072707, 1)] : List FactorBlock).map factorBlockValue).prod = 2291539082278737626663 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fifteenM_2
      · exact prime_fifteenM_19
      · exact prime_fifteenM_107
      · exact prime_fifteenM_563585608037072707
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (10 : ZMod 2291539082278737626663) ^ 1145769541139368813331 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (10 : ZMod 2291539082278737626663) ^ 120607320119933559298 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (10 : ZMod 2291539082278737626663) ^ 21416253105408762866 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (10 : ZMod 2291539082278737626663) ^ 4066 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide

private theorem prime_fifteenM_406247 : Nat.Prime 406247 := by norm_num
private theorem prime_fifteenM_11909399 : Nat.Prime 11909399 := by norm_num
private theorem prime_fifteenM_20101 : Nat.Prime 20101 := by norm_num
private theorem prime_fifteenM_775937 : Nat.Prime 775937 := by norm_num
private theorem prime_fifteenM_93582657823 : Nat.Prime 93582657823 := by
  apply lucas_primality 93582657823 (3 : ZMod 93582657823)
  · rw [← fifteenMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (20101, 1), (775937, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (20101, 1), (775937, 1)] : List FactorBlock).map factorBlockValue).prod = 93582657823 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fifteenM_2
      · exact prime_fifteenM_3
      · exact prime_fifteenM_20101
      · exact prime_fifteenM_775937
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 93582657823) ^ 46791328911 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (3 : ZMod 93582657823) ^ 31194219274 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (3 : ZMod 93582657823) ^ 4655622 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (3 : ZMod 93582657823) ^ 120606 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide

private theorem prime_fifteenM_19090862195893 : Nat.Prime 19090862195893 := by
  apply lucas_primality 19090862195893 (2 : ZMod 19090862195893)
  · rw [← fifteenMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (17, 1), (93582657823, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (17, 1), (93582657823, 1)] : List FactorBlock).map factorBlockValue).prod = 19090862195893 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fifteenM_2
      · exact prime_fifteenM_3
      · exact prime_fifteenM_17
      · exact prime_fifteenM_93582657823
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 19090862195893) ^ 9545431097946 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (2 : ZMod 19090862195893) ^ 6363620731964 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (2 : ZMod 19090862195893) ^ 1122991893876 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (2 : ZMod 19090862195893) ^ 204 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide

private theorem prime_fifteenM_229090346350717 : Nat.Prime 229090346350717 := by
  apply lucas_primality 229090346350717 (2 : ZMod 229090346350717)
  · rw [← fifteenMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (19090862195893, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (19090862195893, 1)] : List FactorBlock).map factorBlockValue).prod = 229090346350717 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fifteenM_2
      · exact prime_fifteenM_3
      · exact prime_fifteenM_19090862195893
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 229090346350717) ^ 114545173175358 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (2 : ZMod 229090346350717) ^ 76363448783572 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (2 : ZMod 229090346350717) ^ 12 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide

private theorem prime_fifteenM_42466681 : Nat.Prime 42466681 := by
  apply lucas_primality 42466681 (7 : ZMod 42466681)
  · rw [← fifteenMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (3, 5), (5, 1), (17, 1), (257, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (3, 5), (5, 1), (17, 1), (257, 1)] : List FactorBlock).map factorBlockValue).prod = 42466681 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fifteenM_2
      · exact prime_fifteenM_3
      · exact prime_fifteenM_5
      · exact prime_fifteenM_17
      · exact prime_fifteenM_257
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 42466681) ^ 21233340 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (7 : ZMod 42466681) ^ 14155560 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (7 : ZMod 42466681) ^ 8493336 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (7 : ZMod 42466681) ^ 2498040 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (7 : ZMod 42466681) ^ 165240 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide

private theorem prime_fifteenM_29811610063 : Nat.Prime 29811610063 := by
  apply lucas_primality 29811610063 (3 : ZMod 29811610063)
  · rw [← fifteenMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 3), (13, 1), (42466681, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 3), (13, 1), (42466681, 1)] : List FactorBlock).map factorBlockValue).prod = 29811610063 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fifteenM_2
      · exact prime_fifteenM_3
      · exact prime_fifteenM_13
      · exact prime_fifteenM_42466681
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 29811610063) ^ 14905805031 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (3 : ZMod 29811610063) ^ 9937203354 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (3 : ZMod 29811610063) ^ 2293200774 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (3 : ZMod 29811610063) ^ 702 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide

private theorem prime_fifteenM_79 : Nat.Prime 79 := by norm_num
private theorem prime_fifteenM_5283683 : Nat.Prime 5283683 := by norm_num
private theorem prime_fifteenM_285318883 : Nat.Prime 285318883 := by
  apply lucas_primality 285318883 (2 : ZMod 285318883)
  · rw [← fifteenMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 3), (5283683, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 3), (5283683, 1)] : List FactorBlock).map factorBlockValue).prod = 285318883 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fifteenM_2
      · exact prime_fifteenM_3
      · exact prime_fifteenM_5283683
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 285318883) ^ 142659441 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (2 : ZMod 285318883) ^ 95106294 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (2 : ZMod 285318883) ^ 54 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide

private theorem prime_fifteenM_90160767029 : Nat.Prime 90160767029 := by
  apply lucas_primality 90160767029 (2 : ZMod 90160767029)
  · rw [← fifteenMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (79, 1), (285318883, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (79, 1), (285318883, 1)] : List FactorBlock).map factorBlockValue).prod = 90160767029 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fifteenM_2
      · exact prime_fifteenM_79
      · exact prime_fifteenM_285318883
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 90160767029) ^ 45080383514 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (2 : ZMod 90160767029) ^ 1141275532 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (2 : ZMod 90160767029) ^ 316 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide

private theorem prime_fifteenM_2704823010871 : Nat.Prime 2704823010871 := by
  apply lucas_primality 2704823010871 (13 : ZMod 2704823010871)
  · rw [← fifteenMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (5, 1), (90160767029, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (5, 1), (90160767029, 1)] : List FactorBlock).map factorBlockValue).prod = 2704823010871 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fifteenM_2
      · exact prime_fifteenM_3
      · exact prime_fifteenM_5
      · exact prime_fifteenM_90160767029
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (13 : ZMod 2704823010871) ^ 1352411505435 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (13 : ZMod 2704823010871) ^ 901607670290 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (13 : ZMod 2704823010871) ^ 540964602174 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (13 : ZMod 2704823010871) ^ 30 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide

private theorem prime_fifteenM_613 : Nat.Prime 613 := by norm_num
private theorem prime_fifteenM_85303 : Nat.Prime 85303 := by norm_num
private theorem prime_fifteenM_381559 : Nat.Prime 381559 := by norm_num
private theorem prime_fifteenM_2227409 : Nat.Prime 2227409 := by norm_num
private theorem prime_fifteenM_5099327703787 : Nat.Prime 5099327703787 := by
  apply lucas_primality 5099327703787 (3 : ZMod 5099327703787)
  · rw [← fifteenMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (381559, 1), (2227409, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (381559, 1), (2227409, 1)] : List FactorBlock).map factorBlockValue).prod = 5099327703787 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fifteenM_2
      · exact prime_fifteenM_3
      · exact prime_fifteenM_381559
      · exact prime_fifteenM_2227409
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 5099327703787) ^ 2549663851893 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (3 : ZMod 5099327703787) ^ 1699775901262 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (3 : ZMod 5099327703787) ^ 13364454 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (3 : ZMod 5099327703787) ^ 2289354 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide

private theorem prime_fifteenM_66576822500643073 : Nat.Prime 66576822500643073 := by
  apply lucas_primality 66576822500643073 (5 : ZMod 66576822500643073)
  · rw [← fifteenMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 8), (3, 1), (17, 1), (5099327703787, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 8), (3, 1), (17, 1), (5099327703787, 1)] : List FactorBlock).map factorBlockValue).prod = 66576822500643073 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fifteenM_2
      · exact prime_fifteenM_3
      · exact prime_fifteenM_17
      · exact prime_fifteenM_5099327703787
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 66576822500643073) ^ 33288411250321536 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (5 : ZMod 66576822500643073) ^ 22192274166881024 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (5 : ZMod 66576822500643073) ^ 3916283676508416 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (5 : ZMod 66576822500643073) ^ 13056 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide

private theorem prime_fifteenM_2113 : Nat.Prime 2113 := by norm_num
private theorem prime_fifteenM_4871 : Nat.Prime 4871 := by norm_num
private theorem prime_fifteenM_11119 : Nat.Prime 11119 := by norm_num
private theorem prime_fifteenM_48179 : Nat.Prime 48179 := by norm_num
private theorem prime_fifteenM_230969 : Nat.Prime 230969 := by norm_num
private theorem prime_fifteenM_732923 : Nat.Prime 732923 := by norm_num
private theorem prime_fifteenM_769 : Nat.Prime 769 := by norm_num
private theorem prime_fifteenM_2143 : Nat.Prime 2143 := by norm_num
private theorem prime_fifteenM_8597 : Nat.Prime 8597 := by norm_num
private theorem prime_fifteenM_9792301 : Nat.Prime 9792301 := by norm_num
private theorem prime_fifteenM_161017 : Nat.Prime 161017 := by norm_num
private theorem prime_fifteenM_6391408799 : Nat.Prime 6391408799 := by
  apply lucas_primality 6391408799 (23 : ZMod 6391408799)
  · rw [← fifteenMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (89, 1), (223, 1), (161017, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (89, 1), (223, 1), (161017, 1)] : List FactorBlock).map factorBlockValue).prod = 6391408799 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fifteenM_2
      · exact prime_fifteenM_89
      · exact prime_fifteenM_223
      · exact prime_fifteenM_161017
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (23 : ZMod 6391408799) ^ 3195704399 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (23 : ZMod 6391408799) ^ 71813582 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (23 : ZMod 6391408799) ^ 28661026 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (23 : ZMod 6391408799) ^ 39694 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide

private theorem prime_fifteenM_113 : Nat.Prime 113 := by norm_num
private theorem prime_fifteenM_54421 : Nat.Prime 54421 := by norm_num
private theorem prime_fifteenM_5897 : Nat.Prime 5897 := by norm_num
private theorem prime_fifteenM_97654321 : Nat.Prime 97654321 := by
  apply lucas_primality 97654321 (17 : ZMod 97654321)
  · rw [← fifteenMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 4), (3, 2), (5, 1), (23, 1), (5897, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 4), (3, 2), (5, 1), (23, 1), (5897, 1)] : List FactorBlock).map factorBlockValue).prod = 97654321 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fifteenM_2
      · exact prime_fifteenM_3
      · exact prime_fifteenM_5
      · exact prime_fifteenM_23
      · exact prime_fifteenM_5897
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (17 : ZMod 97654321) ^ 48827160 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (17 : ZMod 97654321) ^ 32551440 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (17 : ZMod 97654321) ^ 19530864 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (17 : ZMod 97654321) ^ 4245840 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (17 : ZMod 97654321) ^ 16560 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide

private theorem prime_fifteenM_397 : Nat.Prime 397 := by norm_num
private theorem prime_fifteenM_977 : Nat.Prime 977 := by norm_num
private theorem prime_fifteenM_906371 : Nat.Prime 906371 := by norm_num
private theorem prime_fifteenM_1406212853597 : Nat.Prime 1406212853597 := by
  apply lucas_primality 1406212853597 (2 : ZMod 1406212853597)
  · rw [← fifteenMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (397, 1), (977, 1), (906371, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (397, 1), (977, 1), (906371, 1)] : List FactorBlock).map factorBlockValue).prod = 1406212853597 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fifteenM_2
      · exact prime_fifteenM_397
      · exact prime_fifteenM_977
      · exact prime_fifteenM_906371
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1406212853597) ^ 703106426798 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (2 : ZMod 1406212853597) ^ 3542097868 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (2 : ZMod 1406212853597) ^ 1439317148 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (2 : ZMod 1406212853597) ^ 1551476 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide

private theorem prime_fifteenM_367 : Nat.Prime 367 := by norm_num
private theorem prime_fifteenM_33641 : Nat.Prime 33641 := by norm_num
private theorem prime_fifteenM_67 : Nat.Prime 67 := by norm_num
private theorem prime_fifteenM_1877 : Nat.Prime 1877 := by norm_num
private theorem prime_fifteenM_1589747 : Nat.Prime 1589747 := by norm_num
private theorem prime_fifteenM_97368824257 : Nat.Prime 97368824257 := by
  apply lucas_primality 97368824257 (5 : ZMod 97368824257)
  · rw [← fifteenMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 6), (3, 1), (11, 1), (29, 1), (1589747, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 6), (3, 1), (11, 1), (29, 1), (1589747, 1)] : List FactorBlock).map factorBlockValue).prod = 97368824257 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fifteenM_2
      · exact prime_fifteenM_3
      · exact prime_fifteenM_11
      · exact prime_fifteenM_29
      · exact prime_fifteenM_1589747
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 97368824257) ^ 48684412128 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (5 : ZMod 97368824257) ^ 32456274752 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (5 : ZMod 97368824257) ^ 8851711296 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (5 : ZMod 97368824257) ^ 3357545664 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (5 : ZMod 97368824257) ^ 61248 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide

private theorem prime_fifteenM_24490011939472127 : Nat.Prime 24490011939472127 := by
  apply lucas_primality 24490011939472127 (5 : ZMod 24490011939472127)
  · rw [← fifteenMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (67, 1), (1877, 1), (97368824257, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (67, 1), (1877, 1), (97368824257, 1)] : List FactorBlock).map factorBlockValue).prod = 24490011939472127 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fifteenM_2
      · exact prime_fifteenM_67
      · exact prime_fifteenM_1877
      · exact prime_fifteenM_97368824257
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 24490011939472127) ^ 12245005969736063 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (5 : ZMod 24490011939472127) ^ 365522566260778 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (5 : ZMod 24490011939472127) ^ 13047422450438 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (5 : ZMod 24490011939472127) ^ 251518 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide

private theorem prime_fifteenM_65290371830632690583 : Nat.Prime 65290371830632690583 := by
  apply lucas_primality 65290371830632690583 (5 : ZMod 65290371830632690583)
  · rw [← fifteenMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (31, 1), (43, 1), (24490011939472127, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (31, 1), (43, 1), (24490011939472127, 1)] : List FactorBlock).map factorBlockValue).prod = 65290371830632690583 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fifteenM_2
      · exact prime_fifteenM_31
      · exact prime_fifteenM_43
      · exact prime_fifteenM_24490011939472127
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 65290371830632690583) ^ 32645185915316345291 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (5 : ZMod 65290371830632690583) ^ 2106141026794602922 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (5 : ZMod 65290371830632690583) ^ 1518380740247271874 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (5 : ZMod 65290371830632690583) ^ 2666 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide

private theorem prime_fifteenM_269 : Nat.Prime 269 := by norm_num
private theorem prime_fifteenM_607 : Nat.Prime 607 := by norm_num
private theorem prime_fifteenM_82621199 : Nat.Prime 82621199 := by
  apply lucas_primality 82621199 (11 : ZMod 82621199)
  · rw [← fifteenMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (11, 1), (23, 1), (269, 1), (607, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (11, 1), (23, 1), (269, 1), (607, 1)] : List FactorBlock).map factorBlockValue).prod = 82621199 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fifteenM_2
      · exact prime_fifteenM_11
      · exact prime_fifteenM_23
      · exact prime_fifteenM_269
      · exact prime_fifteenM_607
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 82621199) ^ 41310599 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (11 : ZMod 82621199) ^ 7511018 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (11 : ZMod 82621199) ^ 3592226 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (11 : ZMod 82621199) ^ 307142 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (11 : ZMod 82621199) ^ 136114 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide

private theorem prime_fifteenM_325800521 : Nat.Prime 325800521 := by
  apply lucas_primality 325800521 (3 : ZMod 325800521)
  · rw [← fifteenMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (5, 1), (23, 2), (89, 1), (173, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (5, 1), (23, 2), (89, 1), (173, 1)] : List FactorBlock).map factorBlockValue).prod = 325800521 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fifteenM_2
      · exact prime_fifteenM_5
      · exact prime_fifteenM_23
      · exact prime_fifteenM_89
      · exact prime_fifteenM_173
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 325800521) ^ 162900260 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (3 : ZMod 325800521) ^ 65160104 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (3 : ZMod 325800521) ^ 14165240 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (3 : ZMod 325800521) ^ 3660680 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (3 : ZMod 325800521) ^ 1883240 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide

private theorem prime_fifteenM_131371 : Nat.Prime 131371 := by norm_num
private theorem prime_fifteenM_362583961 : Nat.Prime 362583961 := by
  apply lucas_primality 362583961 (14 : ZMod 362583961)
  · rw [← fifteenMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (3, 1), (5, 1), (23, 1), (131371, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (3, 1), (5, 1), (23, 1), (131371, 1)] : List FactorBlock).map factorBlockValue).prod = 362583961 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fifteenM_2
      · exact prime_fifteenM_3
      · exact prime_fifteenM_5
      · exact prime_fifteenM_23
      · exact prime_fifteenM_131371
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (14 : ZMod 362583961) ^ 181291980 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (14 : ZMod 362583961) ^ 120861320 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (14 : ZMod 362583961) ^ 72516792 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (14 : ZMod 362583961) ^ 15764520 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (14 : ZMod 362583961) ^ 2760 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide

private theorem prime_fifteenM_83 : Nat.Prime 83 := by norm_num
private theorem prime_fifteenM_1433741 : Nat.Prime 1433741 := by norm_num
private theorem prime_fifteenM_558757 : Nat.Prime 558757 := by norm_num
private theorem prime_fifteenM_106163831 : Nat.Prime 106163831 := by
  apply lucas_primality 106163831 (11 : ZMod 106163831)
  · rw [← fifteenMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 1), (19, 1), (558757, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 1), (19, 1), (558757, 1)] : List FactorBlock).map factorBlockValue).prod = 106163831 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fifteenM_2
      · exact prime_fifteenM_5
      · exact prime_fifteenM_19
      · exact prime_fifteenM_558757
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 106163831) ^ 53081915 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (11 : ZMod 106163831) ^ 21232766 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (11 : ZMod 106163831) ^ 5587570 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (11 : ZMod 106163831) ^ 190 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide

private theorem prime_fifteenM_2409709 : Nat.Prime 2409709 := by norm_num
private theorem prime_fifteenM_7311057107 : Nat.Prime 7311057107 := by
  apply lucas_primality 7311057107 (2 : ZMod 7311057107)
  · rw [← fifteenMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (37, 1), (41, 1), (2409709, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (37, 1), (41, 1), (2409709, 1)] : List FactorBlock).map factorBlockValue).prod = 7311057107 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fifteenM_2
      · exact prime_fifteenM_37
      · exact prime_fifteenM_41
      · exact prime_fifteenM_2409709
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 7311057107) ^ 3655528553 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (2 : ZMod 7311057107) ^ 197596138 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (2 : ZMod 7311057107) ^ 178318466 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (2 : ZMod 7311057107) ^ 3034 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide

private theorem prime_fifteenM_58488456857 : Nat.Prime 58488456857 := by
  apply lucas_primality 58488456857 (3 : ZMod 58488456857)
  · rw [← fifteenMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (7311057107, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (7311057107, 1)] : List FactorBlock).map factorBlockValue).prod = 58488456857 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_fifteenM_2
      · exact prime_fifteenM_7311057107
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 58488456857) ^ 29244228428 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (3 : ZMod 58488456857) ^ 8 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide

private theorem prime_fifteenM_281 : Nat.Prime 281 := by norm_num
private theorem prime_fifteenM_739 : Nat.Prime 739 := by norm_num
private theorem prime_fifteenM_8443 : Nat.Prime 8443 := by norm_num
private theorem prime_fifteenM_84294913 : Nat.Prime 84294913 := by
  apply lucas_primality 84294913 (14 : ZMod 84294913)
  · rw [← fifteenMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 8), (3, 1), (13, 1), (8443, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 8), (3, 1), (13, 1), (8443, 1)] : List FactorBlock).map factorBlockValue).prod = 84294913 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fifteenM_2
      · exact prime_fifteenM_3
      · exact prime_fifteenM_13
      · exact prime_fifteenM_8443
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (14 : ZMod 84294913) ^ 42147456 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (14 : ZMod 84294913) ^ 28098304 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (14 : ZMod 84294913) ^ 6484224 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (14 : ZMod 84294913) ^ 9984 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide

private theorem prime_fifteenM_3540386347 : Nat.Prime 3540386347 := by
  apply lucas_primality 3540386347 (11 : ZMod 3540386347)
  · rw [← fifteenMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (7, 1), (84294913, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (7, 1), (84294913, 1)] : List FactorBlock).map factorBlockValue).prod = 3540386347 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fifteenM_2
      · exact prime_fifteenM_3
      · exact prime_fifteenM_7
      · exact prime_fifteenM_84294913
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 3540386347) ^ 1770193173 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (11 : ZMod 3540386347) ^ 1180128782 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (11 : ZMod 3540386347) ^ 505769478 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (11 : ZMod 3540386347) ^ 42 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide

private theorem prime_fifteenM_1509031 : Nat.Prime 1509031 := by norm_num
private theorem prime_fifteenM_9277522589 : Nat.Prime 9277522589 := by
  apply lucas_primality 9277522589 (2 : ZMod 9277522589)
  · rw [← fifteenMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (29, 1), (53, 1), (1509031, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (29, 1), (53, 1), (1509031, 1)] : List FactorBlock).map factorBlockValue).prod = 9277522589 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fifteenM_2
      · exact prime_fifteenM_29
      · exact prime_fifteenM_53
      · exact prime_fifteenM_1509031
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 9277522589) ^ 4638761294 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (2 : ZMod 9277522589) ^ 319914572 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (2 : ZMod 9277522589) ^ 175047596 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (2 : ZMod 9277522589) ^ 6148 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide

private theorem prime_fifteenM_964862349257 : Nat.Prime 964862349257 := by
  apply lucas_primality 964862349257 (5 : ZMod 964862349257)
  · rw [← fifteenMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (13, 1), (9277522589, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (13, 1), (9277522589, 1)] : List FactorBlock).map factorBlockValue).prod = 964862349257 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fifteenM_2
      · exact prime_fifteenM_13
      · exact prime_fifteenM_9277522589
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 964862349257) ^ 482431174628 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (5 : ZMod 964862349257) ^ 74220180712 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (5 : ZMod 964862349257) ^ 104 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide

private theorem prime_fifteenM_31063 : Nat.Prime 31063 := by norm_num
private theorem prime_fifteenM_2137 : Nat.Prime 2137 := by norm_num
private theorem prime_fifteenM_912772537 : Nat.Prime 912772537 := by
  apply lucas_primality 912772537 (7 : ZMod 912772537)
  · rw [← fifteenMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (3, 1), (13, 1), (37, 2), (2137, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (3, 1), (13, 1), (37, 2), (2137, 1)] : List FactorBlock).map factorBlockValue).prod = 912772537 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fifteenM_2
      · exact prime_fifteenM_3
      · exact prime_fifteenM_13
      · exact prime_fifteenM_37
      · exact prime_fifteenM_2137
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 912772537) ^ 456386268 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (7 : ZMod 912772537) ^ 304257512 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (7 : ZMod 912772537) ^ 70213272 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (7 : ZMod 912772537) ^ 24669528 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (7 : ZMod 912772537) ^ 427128 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide

private theorem prime_fifteenM_4567973 : Nat.Prime 4567973 := by norm_num
private theorem prime_fifteenM_2832143261 : Nat.Prime 2832143261 := by
  apply lucas_primality 2832143261 (2 : ZMod 2832143261)
  · rw [← fifteenMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (5, 1), (31, 1), (4567973, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (5, 1), (31, 1), (4567973, 1)] : List FactorBlock).map factorBlockValue).prod = 2832143261 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fifteenM_2
      · exact prime_fifteenM_5
      · exact prime_fifteenM_31
      · exact prime_fifteenM_4567973
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 2832143261) ^ 1416071630 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (2 : ZMod 2832143261) ^ 566428652 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (2 : ZMod 2832143261) ^ 91359460 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (2 : ZMod 2832143261) ^ 620 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide

private theorem prime_fifteenM_175592882183 : Nat.Prime 175592882183 := by
  apply lucas_primality 175592882183 (10 : ZMod 175592882183)
  · rw [← fifteenMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (31, 1), (2832143261, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (31, 1), (2832143261, 1)] : List FactorBlock).map factorBlockValue).prod = 175592882183 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fifteenM_2
      · exact prime_fifteenM_31
      · exact prime_fifteenM_2832143261
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (10 : ZMod 175592882183) ^ 87796441091 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (10 : ZMod 175592882183) ^ 5664286522 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (10 : ZMod 175592882183) ^ 62 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide

private theorem prime_fifteenM_569 : Nat.Prime 569 := by norm_num
private theorem prime_fifteenM_37039 : Nat.Prime 37039 := by norm_num
private theorem prime_fifteenM_1544987 : Nat.Prime 1544987 := by norm_num
private theorem prime_fifteenM_9813829 : Nat.Prime 9813829 := by norm_num
private theorem prime_fifteenM_2394574277 : Nat.Prime 2394574277 := by
  apply lucas_primality 2394574277 (2 : ZMod 2394574277)
  · rw [← fifteenMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (61, 1), (9813829, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (61, 1), (9813829, 1)] : List FactorBlock).map factorBlockValue).prod = 2394574277 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fifteenM_2
      · exact prime_fifteenM_61
      · exact prime_fifteenM_9813829
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 2394574277) ^ 1197287138 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (2 : ZMod 2394574277) ^ 39255316 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (2 : ZMod 2394574277) ^ 244 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide

private theorem prime_fifteenM_14367445663 : Nat.Prime 14367445663 := by
  apply lucas_primality 14367445663 (23 : ZMod 14367445663)
  · rw [← fifteenMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (2394574277, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (2394574277, 1)] : List FactorBlock).map factorBlockValue).prod = 14367445663 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fifteenM_2
      · exact prime_fifteenM_3
      · exact prime_fifteenM_2394574277
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (23 : ZMod 14367445663) ^ 7183722831 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (23 : ZMod 14367445663) ^ 4789148554 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (23 : ZMod 14367445663) ^ 6 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide

private theorem prime_fifteenM_20171893710853 : Nat.Prime 20171893710853 := by
  apply lucas_primality 20171893710853 (5 : ZMod 20171893710853)
  · rw [← fifteenMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 3), (13, 1), (14367445663, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 3), (13, 1), (14367445663, 1)] : List FactorBlock).map factorBlockValue).prod = 20171893710853 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fifteenM_2
      · exact prime_fifteenM_3
      · exact prime_fifteenM_13
      · exact prime_fifteenM_14367445663
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 20171893710853) ^ 10085946855426 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (5 : ZMod 20171893710853) ^ 6723964570284 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (5 : ZMod 20171893710853) ^ 1551684131604 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (5 : ZMod 20171893710853) ^ 1404 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide

private theorem prime_fifteenM_633357259340797643309658001 : Nat.Prime 633357259340797643309658001 := by
  apply lucas_primality 633357259340797643309658001 (101 : ZMod 633357259340797643309658001)
  · rw [← fifteenMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 4), (3, 4), (5, 3), (7, 1), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 4), (3, 4), (5, 3), (7, 1), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod = 633357259340797643309658001 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fifteenM_2
      · exact prime_fifteenM_3
      · exact prime_fifteenM_5
      · exact prime_fifteenM_7
      · exact prime_fifteenM_11
      · exact prime_fifteenM_13
      · exact prime_fifteenM_17
      · exact prime_fifteenM_19
      · exact prime_fifteenM_23
      · exact prime_fifteenM_29
      · exact prime_fifteenM_31
      · exact prime_fifteenM_37
      · exact prime_fifteenM_41
      · exact prime_fifteenM_43
      · exact prime_fifteenM_47
      · exact prime_fifteenM_53
      · exact prime_fifteenM_59
      · exact prime_fifteenM_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (101 : ZMod 633357259340797643309658001) ^ 316678629670398821654829000 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (101 : ZMod 633357259340797643309658001) ^ 211119086446932547769886000 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (101 : ZMod 633357259340797643309658001) ^ 126671451868159528661931600 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (101 : ZMod 633357259340797643309658001) ^ 90479608477256806187094000 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (101 : ZMod 633357259340797643309658001) ^ 57577932667345240300878000 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (101 : ZMod 633357259340797643309658001) ^ 48719789180061357177666000 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (101 : ZMod 633357259340797643309658001) ^ 37256309372988096665274000 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (101 : ZMod 633357259340797643309658001) ^ 33334592596884086489982000 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (101 : ZMod 633357259340797643309658001) ^ 27537272145252071448246000 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (101 : ZMod 633357259340797643309658001) ^ 21839905494510263562402000 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (101 : ZMod 633357259340797643309658001) ^ 20430879333574117526118000 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (101 : ZMod 633357259340797643309658001) ^ 17117763765967503873234000 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (101 : ZMod 633357259340797643309658001) ^ 15447738032702381544138000 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (101 : ZMod 633357259340797643309658001) ^ 14729238589320875425806000 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (101 : ZMod 633357259340797643309658001) ^ 13475686368953141347014000 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (101 : ZMod 633357259340797643309658001) ^ 11950136968694295156786000 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (101 : ZMod 633357259340797643309658001) ^ 10734868802386400734062000 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (101 : ZMod 633357259340797643309658001) ^ 10382905890832748250978000 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide

private theorem prime_fifteenM_1056241 : Nat.Prime 1056241 := by norm_num
private theorem prime_fifteenM_811 : Nat.Prime 811 := by norm_num
private theorem prime_fifteenM_3413 : Nat.Prime 3413 := by norm_num
private theorem prime_fifteenM_3583 : Nat.Prime 3583 := by norm_num
private theorem prime_fifteenM_3617 : Nat.Prime 3617 := by norm_num
private theorem prime_fifteenM_21673431885071 : Nat.Prime 21673431885071 := by
  apply lucas_primality 21673431885071 (13 : ZMod 21673431885071)
  · rw [← fifteenMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 1), (7, 2), (3413, 1), (3583, 1), (3617, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 1), (7, 2), (3413, 1), (3583, 1), (3617, 1)] : List FactorBlock).map factorBlockValue).prod = 21673431885071 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fifteenM_2
      · exact prime_fifteenM_5
      · exact prime_fifteenM_7
      · exact prime_fifteenM_3413
      · exact prime_fifteenM_3583
      · exact prime_fifteenM_3617
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 21673431885071) ^ 10836715942535 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (13 : ZMod 21673431885071) ^ 4334686377014 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (13 : ZMod 21673431885071) ^ 3096204555010 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (13 : ZMod 21673431885071) ^ 6350258390 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (13 : ZMod 21673431885071) ^ 6048962290 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (13 : ZMod 21673431885071) ^ 5992101710 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide

private theorem prime_fifteenM_1511635180256161967 : Nat.Prime 1511635180256161967 := by
  apply lucas_primality 1511635180256161967 (5 : ZMod 1511635180256161967)
  · rw [← fifteenMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (43, 1), (811, 1), (21673431885071, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (43, 1), (811, 1), (21673431885071, 1)] : List FactorBlock).map factorBlockValue).prod = 1511635180256161967 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fifteenM_2
      · exact prime_fifteenM_43
      · exact prime_fifteenM_811
      · exact prime_fifteenM_21673431885071
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 1511635180256161967) ^ 755817590128080983 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (5 : ZMod 1511635180256161967) ^ 35154306517585162 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (5 : ZMod 1511635180256161967) ^ 1863915142116106 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (5 : ZMod 1511635180256161967) ^ 69746 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide

private theorem prime_fifteenM_37309 : Nat.Prime 37309 := by norm_num
private theorem prime_fifteenM_1222615931 : Nat.Prime 1222615931 := by
  apply lucas_primality 1222615931 (2 : ZMod 1222615931)
  · rw [← fifteenMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 1), (29, 1), (113, 1), (37309, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 1), (29, 1), (113, 1), (37309, 1)] : List FactorBlock).map factorBlockValue).prod = 1222615931 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fifteenM_2
      · exact prime_fifteenM_5
      · exact prime_fifteenM_29
      · exact prime_fifteenM_113
      · exact prime_fifteenM_37309
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1222615931) ^ 611307965 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (2 : ZMod 1222615931) ^ 244523186 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (2 : ZMod 1222615931) ^ 42159170 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (2 : ZMod 1222615931) ^ 10819610 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (2 : ZMod 1222615931) ^ 32770 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide

private theorem prime_fifteenM_2531 : Nat.Prime 2531 := by norm_num
private theorem prime_fifteenM_6763 : Nat.Prime 6763 := by norm_num
private theorem prime_fifteenM_462094662389 : Nat.Prime 462094662389 := by
  apply lucas_primality 462094662389 (2 : ZMod 462094662389)
  · rw [← fifteenMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (17, 1), (397, 1), (2531, 1), (6763, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (17, 1), (397, 1), (2531, 1), (6763, 1)] : List FactorBlock).map factorBlockValue).prod = 462094662389 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fifteenM_2
      · exact prime_fifteenM_17
      · exact prime_fifteenM_397
      · exact prime_fifteenM_2531
      · exact prime_fifteenM_6763
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 462094662389) ^ 231047331194 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (2 : ZMod 462094662389) ^ 27182038964 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (2 : ZMod 462094662389) ^ 1163966404 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (2 : ZMod 462094662389) ^ 182573948 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (2 : ZMod 462094662389) ^ 68326876 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide

private theorem prime_fifteenM_1667237541899513 : Nat.Prime 1667237541899513 := by
  apply lucas_primality 1667237541899513 (3 : ZMod 1667237541899513)
  · rw [← fifteenMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (11, 1), (41, 1), (462094662389, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (11, 1), (41, 1), (462094662389, 1)] : List FactorBlock).map factorBlockValue).prod = 1667237541899513 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fifteenM_2
      · exact prime_fifteenM_11
      · exact prime_fifteenM_41
      · exact prime_fifteenM_462094662389
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1667237541899513) ^ 833618770949756 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (3 : ZMod 1667237541899513) ^ 151567049263592 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (3 : ZMod 1667237541899513) ^ 40664330290232 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (3 : ZMod 1667237541899513) ^ 3608 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide

private theorem prime_fifteenM_483498887150858771 : Nat.Prime 483498887150858771 := by
  apply lucas_primality 483498887150858771 (2 : ZMod 483498887150858771)
  · rw [← fifteenMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 1), (29, 1), (1667237541899513, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 1), (29, 1), (1667237541899513, 1)] : List FactorBlock).map factorBlockValue).prod = 483498887150858771 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fifteenM_2
      · exact prime_fifteenM_5
      · exact prime_fifteenM_29
      · exact prime_fifteenM_1667237541899513
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 483498887150858771) ^ 241749443575429385 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (2 : ZMod 483498887150858771) ^ 96699777430171754 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (2 : ZMod 483498887150858771) ^ 16672375418995130 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (2 : ZMod 483498887150858771) ^ 290 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide

private theorem prime_fifteenM_15073 : Nat.Prime 15073 := by norm_num
private theorem prime_fifteenM_4979131 : Nat.Prime 4979131 := by norm_num
private theorem prime_fifteenM_1191109 : Nat.Prime 1191109 := by norm_num
private theorem prime_fifteenM_33351053 : Nat.Prime 33351053 := by
  apply lucas_primality 33351053 (2 : ZMod 33351053)
  · rw [← fifteenMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (7, 1), (1191109, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (7, 1), (1191109, 1)] : List FactorBlock).map factorBlockValue).prod = 33351053 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fifteenM_2
      · exact prime_fifteenM_7
      · exact prime_fifteenM_1191109
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 33351053) ^ 16675526 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (2 : ZMod 33351053) ^ 4764436 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (2 : ZMod 33351053) ^ 28 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide

private theorem prime_fifteenM_541589 : Nat.Prime 541589 := by norm_num
private theorem prime_fifteenM_228550559 : Nat.Prime 228550559 := by
  apply lucas_primality 228550559 (37 : ZMod 228550559)
  · rw [← fifteenMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (211, 1), (541589, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (211, 1), (541589, 1)] : List FactorBlock).map factorBlockValue).prod = 228550559 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fifteenM_2
      · exact prime_fifteenM_211
      · exact prime_fifteenM_541589
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (37 : ZMod 228550559) ^ 114275279 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (37 : ZMod 228550559) ^ 1083178 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (37 : ZMod 228550559) ^ 422 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide

private theorem prime_fifteenM_947 : Nat.Prime 947 := by norm_num
private theorem prime_fifteenM_1983689 : Nat.Prime 1983689 := by norm_num
private theorem prime_fifteenM_7514213933 : Nat.Prime 7514213933 := by
  apply lucas_primality 7514213933 (2 : ZMod 7514213933)
  · rw [← fifteenMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (947, 1), (1983689, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (947, 1), (1983689, 1)] : List FactorBlock).map factorBlockValue).prod = 7514213933 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fifteenM_2
      · exact prime_fifteenM_947
      · exact prime_fifteenM_1983689
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 7514213933) ^ 3757106966 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (2 : ZMod 7514213933) ^ 7934756 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (2 : ZMod 7514213933) ^ 3788 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide

private theorem prime_fifteenM_12864823 : Nat.Prime 12864823 := by norm_num
private theorem prime_fifteenM_16568887 : Nat.Prime 16568887 := by norm_num
private theorem prime_fifteenM_73751906302452347 : Nat.Prime 73751906302452347 := by
  apply lucas_primality 73751906302452347 (2 : ZMod 73751906302452347)
  · rw [← fifteenMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (173, 1), (12864823, 1), (16568887, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (173, 1), (12864823, 1), (16568887, 1)] : List FactorBlock).map factorBlockValue).prod = 73751906302452347 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fifteenM_2
      · exact prime_fifteenM_173
      · exact prime_fifteenM_12864823
      · exact prime_fifteenM_16568887
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 73751906302452347) ^ 36875953151226173 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (2 : ZMod 73751906302452347) ^ 426311597124002 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (2 : ZMod 73751906302452347) ^ 5732834902 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (2 : ZMod 73751906302452347) ^ 4451228758 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide

private theorem prime_fifteenM_21347 : Nat.Prime 21347 := by norm_num
private theorem prime_fifteenM_26687336297 : Nat.Prime 26687336297 := by
  apply lucas_primality 26687336297 (3 : ZMod 26687336297)
  · rw [← fifteenMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (31, 1), (71, 2), (21347, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (31, 1), (71, 2), (21347, 1)] : List FactorBlock).map factorBlockValue).prod = 26687336297 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fifteenM_2
      · exact prime_fifteenM_31
      · exact prime_fifteenM_71
      · exact prime_fifteenM_21347
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 26687336297) ^ 13343668148 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (3 : ZMod 26687336297) ^ 860881816 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (3 : ZMod 26687336297) ^ 375877976 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (3 : ZMod 26687336297) ^ 1250168 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide

private theorem prime_fifteenM_1163 : Nat.Prime 1163 := by norm_num
private theorem prime_fifteenM_1663 : Nat.Prime 1663 := by norm_num
private theorem prime_fifteenM_13147 : Nat.Prime 13147 := by norm_num
private theorem prime_fifteenM_283615046165023 : Nat.Prime 283615046165023 := by
  apply lucas_primality 283615046165023 (3 : ZMod 283615046165023)
  · rw [← fifteenMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (11, 1), (13, 2), (1163, 1), (1663, 1), (13147, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (11, 1), (13, 2), (1163, 1), (1663, 1), (13147, 1)] : List FactorBlock).map factorBlockValue).prod = 283615046165023 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fifteenM_2
      · exact prime_fifteenM_3
      · exact prime_fifteenM_11
      · exact prime_fifteenM_13
      · exact prime_fifteenM_1163
      · exact prime_fifteenM_1663
      · exact prime_fifteenM_13147
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 283615046165023) ^ 141807523082511 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (3 : ZMod 283615046165023) ^ 94538348721674 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (3 : ZMod 283615046165023) ^ 25783186015002 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (3 : ZMod 283615046165023) ^ 21816542012694 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (3 : ZMod 283615046165023) ^ 243865043994 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (3 : ZMod 283615046165023) ^ 170544224994 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (3 : ZMod 283615046165023) ^ 21572605626 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide

private theorem prime_fifteenM_14266177 : Nat.Prime 14266177 := by norm_num
private theorem prime_fifteenM_85597063 : Nat.Prime 85597063 := by
  apply lucas_primality 85597063 (5 : ZMod 85597063)
  · rw [← fifteenMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (14266177, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (14266177, 1)] : List FactorBlock).map factorBlockValue).prod = 85597063 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fifteenM_2
      · exact prime_fifteenM_3
      · exact prime_fifteenM_14266177
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 85597063) ^ 42798531 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (5 : ZMod 85597063) ^ 28532354 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (5 : ZMod 85597063) ^ 6 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide

private theorem prime_fifteenM_4451047277 : Nat.Prime 4451047277 := by
  apply lucas_primality 4451047277 (2 : ZMod 4451047277)
  · rw [← fifteenMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (13, 1), (85597063, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (13, 1), (85597063, 1)] : List FactorBlock).map factorBlockValue).prod = 4451047277 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fifteenM_2
      · exact prime_fifteenM_13
      · exact prime_fifteenM_85597063
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 4451047277) ^ 2225523638 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (2 : ZMod 4451047277) ^ 342388252 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (2 : ZMod 4451047277) ^ 52 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide

private theorem prime_fifteenM_293769120283 : Nat.Prime 293769120283 := by
  apply lucas_primality 293769120283 (7 : ZMod 293769120283)
  · rw [← fifteenMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (11, 1), (4451047277, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (11, 1), (4451047277, 1)] : List FactorBlock).map factorBlockValue).prod = 293769120283 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fifteenM_2
      · exact prime_fifteenM_3
      · exact prime_fifteenM_11
      · exact prime_fifteenM_4451047277
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 293769120283) ^ 146884560141 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (7 : ZMod 293769120283) ^ 97923040094 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (7 : ZMod 293769120283) ^ 26706283662 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (7 : ZMod 293769120283) ^ 66 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide

private theorem prime_fifteenM_163 : Nat.Prime 163 := by norm_num
private theorem prime_fifteenM_2932487 : Nat.Prime 2932487 := by norm_num
private theorem prime_fifteenM_26500063922641 : Nat.Prime 26500063922641 := by
  apply lucas_primality 26500063922641 (19 : ZMod 26500063922641)
  · rw [← fifteenMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 4), (3, 2), (5, 1), (7, 1), (11, 1), (163, 1), (2932487, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 4), (3, 2), (5, 1), (7, 1), (11, 1), (163, 1), (2932487, 1)] : List FactorBlock).map factorBlockValue).prod = 26500063922641 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fifteenM_2
      · exact prime_fifteenM_3
      · exact prime_fifteenM_5
      · exact prime_fifteenM_7
      · exact prime_fifteenM_11
      · exact prime_fifteenM_163
      · exact prime_fifteenM_2932487
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (19 : ZMod 26500063922641) ^ 13250031961320 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (19 : ZMod 26500063922641) ^ 8833354640880 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (19 : ZMod 26500063922641) ^ 5300012784528 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (19 : ZMod 26500063922641) ^ 3785723417520 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (19 : ZMod 26500063922641) ^ 2409096720240 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (19 : ZMod 26500063922641) ^ 162577079280 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (19 : ZMod 26500063922641) ^ 9036720 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide

private theorem prime_fifteenM_727 : Nat.Prime 727 := by norm_num
private theorem prime_fifteenM_517267 : Nat.Prime 517267 := by norm_num
private theorem prime_fifteenM_40346827 : Nat.Prime 40346827 := by
  apply lucas_primality 40346827 (2 : ZMod 40346827)
  · rw [← fifteenMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (13, 1), (517267, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (13, 1), (517267, 1)] : List FactorBlock).map factorBlockValue).prod = 40346827 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fifteenM_2
      · exact prime_fifteenM_3
      · exact prime_fifteenM_13
      · exact prime_fifteenM_517267
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 40346827) ^ 20173413 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (2 : ZMod 40346827) ^ 13448942 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (2 : ZMod 40346827) ^ 3103602 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (2 : ZMod 40346827) ^ 78 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide

private theorem prime_fifteenM_4159 : Nat.Prime 4159 := by norm_num
private theorem prime_fifteenM_16453 : Nat.Prime 16453 := by norm_num
private theorem prime_fifteenM_910838081 : Nat.Prime 910838081 := by
  apply lucas_primality 910838081 (3 : ZMod 910838081)
  · rw [← fifteenMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 6), (5, 1), (173, 1), (16453, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 6), (5, 1), (173, 1), (16453, 1)] : List FactorBlock).map factorBlockValue).prod = 910838081 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fifteenM_2
      · exact prime_fifteenM_5
      · exact prime_fifteenM_173
      · exact prime_fifteenM_16453
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 910838081) ^ 455419040 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (3 : ZMod 910838081) ^ 182167616 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (3 : ZMod 910838081) ^ 5264960 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (3 : ZMod 910838081) ^ 55360 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide

private theorem prime_fifteenM_75763511577581 : Nat.Prime 75763511577581 := by
  apply lucas_primality 75763511577581 (3 : ZMod 75763511577581)
  · rw [← fifteenMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (5, 1), (4159, 1), (910838081, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (5, 1), (4159, 1), (910838081, 1)] : List FactorBlock).map factorBlockValue).prod = 75763511577581 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fifteenM_2
      · exact prime_fifteenM_5
      · exact prime_fifteenM_4159
      · exact prime_fifteenM_910838081
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 75763511577581) ^ 37881755788790 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (3 : ZMod 75763511577581) ^ 15152702315516 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (3 : ZMod 75763511577581) ^ 18216761620 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (3 : ZMod 75763511577581) ^ 83180 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide

private theorem prime_fifteenM_17274080639688469 : Nat.Prime 17274080639688469 := by
  apply lucas_primality 17274080639688469 (2 : ZMod 17274080639688469)
  · rw [← fifteenMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (19, 1), (75763511577581, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (19, 1), (75763511577581, 1)] : List FactorBlock).map factorBlockValue).prod = 17274080639688469 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fifteenM_2
      · exact prime_fifteenM_3
      · exact prime_fifteenM_19
      · exact prime_fifteenM_75763511577581
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 17274080639688469) ^ 8637040319844234 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (2 : ZMod 17274080639688469) ^ 5758026879896156 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (2 : ZMod 17274080639688469) ^ 909162138930972 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (2 : ZMod 17274080639688469) ^ 228 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide

private theorem prime_fifteenM_762563 : Nat.Prime 762563 := by norm_num
private theorem prime_fifteenM_14719189 : Nat.Prime 14719189 := by norm_num
private theorem prime_fifteenM_500452427 : Nat.Prime 500452427 := by
  apply lucas_primality 500452427 (2 : ZMod 500452427)
  · rw [← fifteenMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (17, 1), (14719189, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (17, 1), (14719189, 1)] : List FactorBlock).map factorBlockValue).prod = 500452427 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fifteenM_2
      · exact prime_fifteenM_17
      · exact prime_fifteenM_14719189
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 500452427) ^ 250226213 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (2 : ZMod 500452427) ^ 29438378 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (2 : ZMod 500452427) ^ 34 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide

private theorem prime_fifteenM_15383 : Nat.Prime 15383 := by norm_num
private theorem prime_fifteenM_64153 : Nat.Prime 64153 := by norm_num
private theorem prime_fifteenM_11842387189 : Nat.Prime 11842387189 := by
  apply lucas_primality 11842387189 (2 : ZMod 11842387189)
  · rw [← fifteenMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (15383, 1), (64153, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (15383, 1), (64153, 1)] : List FactorBlock).map factorBlockValue).prod = 11842387189 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fifteenM_2
      · exact prime_fifteenM_3
      · exact prime_fifteenM_15383
      · exact prime_fifteenM_64153
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 11842387189) ^ 5921193594 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (2 : ZMod 11842387189) ^ 3947462396 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (2 : ZMod 11842387189) ^ 769836 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (2 : ZMod 11842387189) ^ 184596 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide

private theorem prime_fifteenM_1211593 : Nat.Prime 1211593 := by norm_num
private theorem prime_fifteenM_45481 : Nat.Prime 45481 := by norm_num
private theorem prime_fifteenM_2003 : Nat.Prime 2003 := by norm_num
private theorem prime_fifteenM_264527 : Nat.Prime 264527 := by norm_num
private theorem prime_fifteenM_25432683889 : Nat.Prime 25432683889 := by
  apply lucas_primality 25432683889 (13 : ZMod 25432683889)
  · rw [← fifteenMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 4), (3, 1), (2003, 1), (264527, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 4), (3, 1), (2003, 1), (264527, 1)] : List FactorBlock).map factorBlockValue).prod = 25432683889 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fifteenM_2
      · exact prime_fifteenM_3
      · exact prime_fifteenM_2003
      · exact prime_fifteenM_264527
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (13 : ZMod 25432683889) ^ 12716341944 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (13 : ZMod 25432683889) ^ 8477561296 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (13 : ZMod 25432683889) ^ 12697296 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (13 : ZMod 25432683889) ^ 96144 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide

private theorem prime_fifteenM_867527921966706751 : Nat.Prime 867527921966706751 := by
  apply lucas_primality 867527921966706751 (6 : ZMod 867527921966706751)
  · rw [← fifteenMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (5, 3), (45481, 1), (25432683889, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (5, 3), (45481, 1), (25432683889, 1)] : List FactorBlock).map factorBlockValue).prod = 867527921966706751 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fifteenM_2
      · exact prime_fifteenM_3
      · exact prime_fifteenM_5
      · exact prime_fifteenM_45481
      · exact prime_fifteenM_25432683889
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 867527921966706751) ^ 433763960983353375 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (6 : ZMod 867527921966706751) ^ 289175973988902250 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (6 : ZMod 867527921966706751) ^ 173505584393341350 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (6 : ZMod 867527921966706751) ^ 19074512916750 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (6 : ZMod 867527921966706751) ^ 34110750 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide

private theorem prime_fifteenM_395592732416818278457 : Nat.Prime 395592732416818278457 := by
  apply lucas_primality 395592732416818278457 (7 : ZMod 395592732416818278457)
  · rw [← fifteenMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (3, 1), (19, 1), (867527921966706751, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (3, 1), (19, 1), (867527921966706751, 1)] : List FactorBlock).map factorBlockValue).prod = 395592732416818278457 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fifteenM_2
      · exact prime_fifteenM_3
      · exact prime_fifteenM_19
      · exact prime_fifteenM_867527921966706751
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 395592732416818278457) ^ 197796366208409139228 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (7 : ZMod 395592732416818278457) ^ 131864244138939426152 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (7 : ZMod 395592732416818278457) ^ 20820670127200962024 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (7 : ZMod 395592732416818278457) ^ 456 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide

private theorem prime_fifteenM_2089 : Nat.Prime 2089 := by norm_num
private theorem prime_fifteenM_18671 : Nat.Prime 18671 := by norm_num
private theorem prime_fifteenM_251162293 : Nat.Prime 251162293 := by
  apply lucas_primality 251162293 (2 : ZMod 251162293)
  · rw [← fifteenMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (19, 1), (59, 1), (18671, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (19, 1), (59, 1), (18671, 1)] : List FactorBlock).map factorBlockValue).prod = 251162293 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fifteenM_2
      · exact prime_fifteenM_3
      · exact prime_fifteenM_19
      · exact prime_fifteenM_59
      · exact prime_fifteenM_18671
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 251162293) ^ 125581146 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (2 : ZMod 251162293) ^ 83720764 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (2 : ZMod 251162293) ^ 13219068 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (2 : ZMod 251162293) ^ 4256988 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (2 : ZMod 251162293) ^ 13452 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide

private theorem prime_fifteenM_4283 : Nat.Prime 4283 := by norm_num
private theorem prime_fifteenM_33724343 : Nat.Prime 33724343 := by
  apply lucas_primality 33724343 (5 : ZMod 33724343)
  · rw [← fifteenMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (31, 1), (127, 1), (4283, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (31, 1), (127, 1), (4283, 1)] : List FactorBlock).map factorBlockValue).prod = 33724343 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fifteenM_2
      · exact prime_fifteenM_31
      · exact prime_fifteenM_127
      · exact prime_fifteenM_4283
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 33724343) ^ 16862171 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (5 : ZMod 33724343) ^ 1087882 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (5 : ZMod 33724343) ^ 265546 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (5 : ZMod 33724343) ^ 7874 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide

private theorem prime_fifteenM_67448687 : Nat.Prime 67448687 := by
  apply lucas_primality 67448687 (5 : ZMod 67448687)
  · rw [← fifteenMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (33724343, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (33724343, 1)] : List FactorBlock).map factorBlockValue).prod = 67448687 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_fifteenM_2
      · exact prime_fifteenM_33724343
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 67448687) ^ 33724343 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (5 : ZMod 67448687) ^ 2 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide

private theorem prime_fifteenM_332387129537 : Nat.Prime 332387129537 := by
  apply lucas_primality 332387129537 (3 : ZMod 332387129537)
  · rw [← fifteenMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 6), (7, 1), (11, 1), (67448687, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 6), (7, 1), (11, 1), (67448687, 1)] : List FactorBlock).map factorBlockValue).prod = 332387129537 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fifteenM_2
      · exact prime_fifteenM_7
      · exact prime_fifteenM_11
      · exact prime_fifteenM_67448687
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 332387129537) ^ 166193564768 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (3 : ZMod 332387129537) ^ 47483875648 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (3 : ZMod 332387129537) ^ 30217011776 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (3 : ZMod 332387129537) ^ 4928 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide

private theorem prime_fifteenM_889467958641013 : Nat.Prime 889467958641013 := by
  apply lucas_primality 889467958641013 (2 : ZMod 889467958641013)
  · rw [← fifteenMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (223, 1), (332387129537, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (223, 1), (332387129537, 1)] : List FactorBlock).map factorBlockValue).prod = 889467958641013 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fifteenM_2
      · exact prime_fifteenM_3
      · exact prime_fifteenM_223
      · exact prime_fifteenM_332387129537
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 889467958641013) ^ 444733979320506 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (2 : ZMod 889467958641013) ^ 296489319547004 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (2 : ZMod 889467958641013) ^ 3988645554444 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (2 : ZMod 889467958641013) ^ 2676 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide

private theorem prime_fifteenM_599 : Nat.Prime 599 := by norm_num
private theorem prime_fifteenM_1811 : Nat.Prime 1811 := by norm_num
private theorem prime_fifteenM_33809 : Nat.Prime 33809 := by norm_num
private theorem prime_fifteenM_97 : Nat.Prime 97 := by norm_num
private theorem prime_fifteenM_227 : Nat.Prime 227 := by norm_num
private theorem prime_fifteenM_247757789 : Nat.Prime 247757789 := by
  apply lucas_primality 247757789 (2 : ZMod 247757789)
  · rw [← fifteenMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (29, 1), (97, 2), (227, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (29, 1), (97, 2), (227, 1)] : List FactorBlock).map factorBlockValue).prod = 247757789 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fifteenM_2
      · exact prime_fifteenM_29
      · exact prime_fifteenM_97
      · exact prime_fifteenM_227
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 247757789) ^ 123878894 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (2 : ZMod 247757789) ^ 8543372 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (2 : ZMod 247757789) ^ 2554204 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (2 : ZMod 247757789) ^ 1091444 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide

private theorem prime_fifteenM_12398369604474701 : Nat.Prime 12398369604474701 := by
  apply lucas_primality 12398369604474701 (2 : ZMod 12398369604474701)
  · rw [← fifteenMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (5, 2), (7, 1), (11, 1), (67, 1), (97, 1), (247757789, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (5, 2), (7, 1), (11, 1), (67, 1), (97, 1), (247757789, 1)] : List FactorBlock).map factorBlockValue).prod = 12398369604474701 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fifteenM_2
      · exact prime_fifteenM_5
      · exact prime_fifteenM_7
      · exact prime_fifteenM_11
      · exact prime_fifteenM_67
      · exact prime_fifteenM_97
      · exact prime_fifteenM_247757789
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 12398369604474701) ^ 6199184802237350 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (2 : ZMod 12398369604474701) ^ 2479673920894940 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (2 : ZMod 12398369604474701) ^ 1771195657782100 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (2 : ZMod 12398369604474701) ^ 1127124509497700 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (2 : ZMod 12398369604474701) ^ 185050292604100 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (2 : ZMod 12398369604474701) ^ 127818243345100 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (2 : ZMod 12398369604474701) ^ 50042300 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide

private theorem prime_fifteenM_373 : Nat.Prime 373 := by norm_num
private theorem prime_fifteenM_55249 : Nat.Prime 55249 := by norm_num
private theorem prime_fifteenM_157429 : Nat.Prime 157429 := by norm_num
private theorem prime_fifteenM_773027 : Nat.Prime 773027 := by norm_num
private theorem prime_fifteenM_17678041 : Nat.Prime 17678041 := by norm_num
private theorem prime_fifteenM_176780411 : Nat.Prime 176780411 := by
  apply lucas_primality 176780411 (2 : ZMod 176780411)
  · rw [← fifteenMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 1), (17678041, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 1), (17678041, 1)] : List FactorBlock).map factorBlockValue).prod = 176780411 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fifteenM_2
      · exact prime_fifteenM_5
      · exact prime_fifteenM_17678041
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 176780411) ^ 88390205 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (2 : ZMod 176780411) ^ 35356082 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (2 : ZMod 176780411) ^ 10 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide

private theorem prime_fifteenM_42743 : Nat.Prime 42743 := by norm_num
private theorem prime_fifteenM_68483 : Nat.Prime 68483 := by norm_num
private theorem prime_fifteenM_324773 : Nat.Prime 324773 := by norm_num
private theorem prime_fifteenM_77945521 : Nat.Prime 77945521 := by
  apply lucas_primality 77945521 (7 : ZMod 77945521)
  · rw [← fifteenMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 4), (3, 1), (5, 1), (324773, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 4), (3, 1), (5, 1), (324773, 1)] : List FactorBlock).map factorBlockValue).prod = 77945521 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fifteenM_2
      · exact prime_fifteenM_3
      · exact prime_fifteenM_5
      · exact prime_fifteenM_324773
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 77945521) ^ 38972760 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (7 : ZMod 77945521) ^ 25981840 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (7 : ZMod 77945521) ^ 15589104 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (7 : ZMod 77945521) ^ 240 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide

private theorem prime_fifteenM_243421 : Nat.Prime 243421 := by norm_num
private theorem prime_fifteenM_1895762749 : Nat.Prime 1895762749 := by
  apply lucas_primality 1895762749 (2 : ZMod 1895762749)
  · rw [← fifteenMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (11, 1), (59, 1), (243421, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (11, 1), (59, 1), (243421, 1)] : List FactorBlock).map factorBlockValue).prod = 1895762749 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fifteenM_2
      · exact prime_fifteenM_3
      · exact prime_fifteenM_11
      · exact prime_fifteenM_59
      · exact prime_fifteenM_243421
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1895762749) ^ 947881374 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (2 : ZMod 1895762749) ^ 631920916 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (2 : ZMod 1895762749) ^ 172342068 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (2 : ZMod 1895762749) ^ 32131572 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (2 : ZMod 1895762749) ^ 7788 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide

private theorem prime_fifteenM_409 : Nat.Prime 409 := by norm_num
private theorem prime_fifteenM_443 : Nat.Prime 443 := by norm_num
private theorem prime_fifteenM_1153 : Nat.Prime 1153 := by norm_num
private theorem prime_fifteenM_1671268889 : Nat.Prime 1671268889 := by
  apply lucas_primality 1671268889 (3 : ZMod 1671268889)
  · rw [← fifteenMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (409, 1), (443, 1), (1153, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (409, 1), (443, 1), (1153, 1)] : List FactorBlock).map factorBlockValue).prod = 1671268889 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fifteenM_2
      · exact prime_fifteenM_409
      · exact prime_fifteenM_443
      · exact prime_fifteenM_1153
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1671268889) ^ 835634444 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (3 : ZMod 1671268889) ^ 4086232 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (3 : ZMod 1671268889) ^ 3772616 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (3 : ZMod 1671268889) ^ 1449496 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide

private theorem prime_fifteenM_13421 : Nat.Prime 13421 := by norm_num
private theorem prime_fifteenM_99611 : Nat.Prime 99611 := by norm_num
private theorem prime_fifteenM_50261 : Nat.Prime 50261 := by norm_num
private theorem prime_fifteenM_23622671 : Nat.Prime 23622671 := by
  apply lucas_primality 23622671 (7 : ZMod 23622671)
  · rw [← fifteenMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 1), (47, 1), (50261, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 1), (47, 1), (50261, 1)] : List FactorBlock).map factorBlockValue).prod = 23622671 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fifteenM_2
      · exact prime_fifteenM_5
      · exact prime_fifteenM_47
      · exact prime_fifteenM_50261
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 23622671) ^ 11811335 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (7 : ZMod 23622671) ^ 4724534 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (7 : ZMod 23622671) ^ 502610 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (7 : ZMod 23622671) ^ 470 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide

private theorem prime_fifteenM_252645265925168009 : Nat.Prime 252645265925168009 := by
  apply lucas_primality 252645265925168009 (3 : ZMod 252645265925168009)
  · rw [← fifteenMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (13421, 1), (99611, 1), (23622671, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (13421, 1), (99611, 1), (23622671, 1)] : List FactorBlock).map factorBlockValue).prod = 252645265925168009 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fifteenM_2
      · exact prime_fifteenM_13421
      · exact prime_fifteenM_99611
      · exact prime_fifteenM_23622671
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 252645265925168009) ^ 126322632962584004 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (3 : ZMod 252645265925168009) ^ 18824623047848 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (3 : ZMod 252645265925168009) ^ 2536318939928 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (3 : ZMod 252645265925168009) ^ 10695033848 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide

private theorem prime_fifteenM_653 : Nat.Prime 653 := by norm_num
private theorem prime_fifteenM_911 : Nat.Prime 911 := by norm_num
private theorem prime_fifteenM_1367 : Nat.Prime 1367 := by norm_num
private theorem prime_fifteenM_12073 : Nat.Prime 12073 := by norm_num
private theorem prime_fifteenM_2069 : Nat.Prime 2069 := by norm_num
private theorem prime_fifteenM_379235287 : Nat.Prime 379235287 := by
  apply lucas_primality 379235287 (3 : ZMod 379235287)
  · rw [← fifteenMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 2), (17, 1), (599, 1), (2069, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 2), (17, 1), (599, 1), (2069, 1)] : List FactorBlock).map factorBlockValue).prod = 379235287 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fifteenM_2
      · exact prime_fifteenM_3
      · exact prime_fifteenM_17
      · exact prime_fifteenM_599
      · exact prime_fifteenM_2069
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 379235287) ^ 189617643 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (3 : ZMod 379235287) ^ 126411762 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (3 : ZMod 379235287) ^ 22307958 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (3 : ZMod 379235287) ^ 633114 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (3 : ZMod 379235287) ^ 183294 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide

private theorem prime_fifteenM_17444823203 : Nat.Prime 17444823203 := by
  apply lucas_primality 17444823203 (2 : ZMod 17444823203)
  · rw [← fifteenMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (23, 1), (379235287, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (23, 1), (379235287, 1)] : List FactorBlock).map factorBlockValue).prod = 17444823203 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fifteenM_2
      · exact prime_fifteenM_23
      · exact prime_fifteenM_379235287
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 17444823203) ^ 8722411601 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (2 : ZMod 17444823203) ^ 758470574 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (2 : ZMod 17444823203) ^ 46 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide

private theorem prime_fifteenM_2948558907417467 : Nat.Prime 2948558907417467 := by
  apply lucas_primality 2948558907417467 (2 : ZMod 2948558907417467)
  · rw [← fifteenMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (7, 1), (12073, 1), (17444823203, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (7, 1), (12073, 1), (17444823203, 1)] : List FactorBlock).map factorBlockValue).prod = 2948558907417467 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fifteenM_2
      · exact prime_fifteenM_7
      · exact prime_fifteenM_12073
      · exact prime_fifteenM_17444823203
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 2948558907417467) ^ 1474279453708733 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (2 : ZMod 2948558907417467) ^ 421222701059638 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (2 : ZMod 2948558907417467) ^ 244227524842 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (2 : ZMod 2948558907417467) ^ 169022 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide

private theorem prime_fifteenM_7343899008173092202759 : Nat.Prime 7343899008173092202759 := by
  apply lucas_primality 7343899008173092202759 (11 : ZMod 7343899008173092202759)
  · rw [← fifteenMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (911, 1), (1367, 1), (2948558907417467, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (911, 1), (1367, 1), (2948558907417467, 1)] : List FactorBlock).map factorBlockValue).prod = 7343899008173092202759 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fifteenM_2
      · exact prime_fifteenM_911
      · exact prime_fifteenM_1367
      · exact prime_fifteenM_2948558907417467
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 7343899008173092202759) ^ 3671949504086546101379 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (11 : ZMod 7343899008173092202759) ^ 8061360052879354778 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (11 : ZMod 7343899008173092202759) ^ 5372274329314624874 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (11 : ZMod 7343899008173092202759) ^ 2490674 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide

private theorem prime_fifteenM_14687798016346184405519 : Nat.Prime 14687798016346184405519 := by
  apply lucas_primality 14687798016346184405519 (7 : ZMod 14687798016346184405519)
  · rw [← fifteenMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (7343899008173092202759, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (7343899008173092202759, 1)] : List FactorBlock).map factorBlockValue).prod = 14687798016346184405519 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_fifteenM_2
      · exact prime_fifteenM_7343899008173092202759
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (7 : ZMod 14687798016346184405519) ^ 7343899008173092202759 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (7 : ZMod 14687798016346184405519) ^ 2 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide

private theorem prime_fifteenM_389 : Nat.Prime 389 := by norm_num
private theorem prime_fifteenM_853 : Nat.Prime 853 := by norm_num
private theorem prime_fifteenM_1279 : Nat.Prime 1279 := by norm_num
private theorem prime_fifteenM_305476361 : Nat.Prime 305476361 := by
  apply lucas_primality 305476361 (6 : ZMod 305476361)
  · rw [← fifteenMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (5, 1), (7, 1), (853, 1), (1279, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (5, 1), (7, 1), (853, 1), (1279, 1)] : List FactorBlock).map factorBlockValue).prod = 305476361 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fifteenM_2
      · exact prime_fifteenM_5
      · exact prime_fifteenM_7
      · exact prime_fifteenM_853
      · exact prime_fifteenM_1279
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 305476361) ^ 152738180 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (6 : ZMod 305476361) ^ 61095272 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (6 : ZMod 305476361) ^ 43639480 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (6 : ZMod 305476361) ^ 358120 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (6 : ZMod 305476361) ^ 238840 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide

private theorem prime_fifteenM_151 : Nat.Prime 151 := by norm_num
private theorem prime_fifteenM_1698461 : Nat.Prime 1698461 := by norm_num
private theorem prime_fifteenM_101907661 : Nat.Prime 101907661 := by
  apply lucas_primality 101907661 (6 : ZMod 101907661)
  · rw [← fifteenMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (5, 1), (1698461, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (5, 1), (1698461, 1)] : List FactorBlock).map factorBlockValue).prod = 101907661 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fifteenM_2
      · exact prime_fifteenM_3
      · exact prime_fifteenM_5
      · exact prime_fifteenM_1698461
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 101907661) ^ 50953830 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (6 : ZMod 101907661) ^ 33969220 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (6 : ZMod 101907661) ^ 20381532 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (6 : ZMod 101907661) ^ 60 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide

private theorem prime_fifteenM_45654632129 : Nat.Prime 45654632129 := by
  apply lucas_primality 45654632129 (3 : ZMod 45654632129)
  · rw [← fifteenMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 6), (7, 1), (101907661, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 6), (7, 1), (101907661, 1)] : List FactorBlock).map factorBlockValue).prod = 45654632129 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fifteenM_2
      · exact prime_fifteenM_7
      · exact prime_fifteenM_101907661
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 45654632129) ^ 22827316064 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (3 : ZMod 45654632129) ^ 6522090304 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (3 : ZMod 45654632129) ^ 448 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide

private theorem prime_fifteenM_3391773930127669 : Nat.Prime 3391773930127669 := by
  apply lucas_primality 3391773930127669 (2 : ZMod 3391773930127669)
  · rw [← fifteenMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (41, 1), (151, 1), (45654632129, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (41, 1), (151, 1), (45654632129, 1)] : List FactorBlock).map factorBlockValue).prod = 3391773930127669 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fifteenM_2
      · exact prime_fifteenM_3
      · exact prime_fifteenM_41
      · exact prime_fifteenM_151
      · exact prime_fifteenM_45654632129
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 3391773930127669) ^ 1695886965063834 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (2 : ZMod 3391773930127669) ^ 1130591310042556 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (2 : ZMod 3391773930127669) ^ 82726193417748 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (2 : ZMod 3391773930127669) ^ 22462079007468 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (2 : ZMod 3391773930127669) ^ 74292 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide

private theorem prime_fifteenM_394088961367607422503787201 : Nat.Prime 394088961367607422503787201 := by
  apply lucas_primality 394088961367607422503787201 (103 : ZMod 394088961367607422503787201)
  · rw [← fifteenMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 6), (3, 2), (5, 2), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 6), (3, 2), (5, 2), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod = 394088961367607422503787201 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fifteenM_2
      · exact prime_fifteenM_3
      · exact prime_fifteenM_5
      · exact prime_fifteenM_7
      · exact prime_fifteenM_11
      · exact prime_fifteenM_13
      · exact prime_fifteenM_17
      · exact prime_fifteenM_19
      · exact prime_fifteenM_23
      · exact prime_fifteenM_29
      · exact prime_fifteenM_31
      · exact prime_fifteenM_37
      · exact prime_fifteenM_41
      · exact prime_fifteenM_43
      · exact prime_fifteenM_47
      · exact prime_fifteenM_53
      · exact prime_fifteenM_59
      · exact prime_fifteenM_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (103 : ZMod 394088961367607422503787201) ^ 197044480683803711251893600 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 131362987122535807501262400 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 78817792273521484500757440 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 56298423052515346071969600 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 35826269215237038409435200 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 30314535489815955577214400 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 23181703609859260147281600 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 20741524282505653815988800 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 17134302668156844456686400 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 13589274529917497327716800 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 12712547140890562016251200 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 10651053009935335743345600 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 9611925887014815183019200 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 9164859566688544709390400 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 8384871518459732393697600 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 7435640780520894764222400 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 6679473921484871567860800 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 6460474776518154467275200 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide

private theorem prime_fifteenM_181 : Nat.Prime 181 := by norm_num
private theorem prime_fifteenM_682049 : Nat.Prime 682049 := by norm_num
private theorem prime_fifteenM_1728312167 : Nat.Prime 1728312167 := by
  apply lucas_primality 1728312167 (5 : ZMod 1728312167)
  · rw [← fifteenMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (7, 1), (181, 1), (682049, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (7, 1), (181, 1), (682049, 1)] : List FactorBlock).map factorBlockValue).prod = 1728312167 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fifteenM_2
      · exact prime_fifteenM_7
      · exact prime_fifteenM_181
      · exact prime_fifteenM_682049
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 1728312167) ^ 864156083 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (5 : ZMod 1728312167) ^ 246901738 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (5 : ZMod 1728312167) ^ 9548686 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (5 : ZMod 1728312167) ^ 2534 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide

private theorem prime_fifteenM_4111 : Nat.Prime 4111 := by norm_num
private theorem prime_fifteenM_616871 : Nat.Prime 616871 := by norm_num
private theorem prime_fifteenM_6282853 : Nat.Prime 6282853 := by norm_num
private theorem prime_fifteenM_223062602575272503 : Nat.Prime 223062602575272503 := by
  apply lucas_primality 223062602575272503 (5 : ZMod 223062602575272503)
  · rw [← fifteenMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (7, 1), (4111, 1), (616871, 1), (6282853, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (7, 1), (4111, 1), (616871, 1), (6282853, 1)] : List FactorBlock).map factorBlockValue).prod = 223062602575272503 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fifteenM_2
      · exact prime_fifteenM_7
      · exact prime_fifteenM_4111
      · exact prime_fifteenM_616871
      · exact prime_fifteenM_6282853
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 223062602575272503) ^ 111531301287636251 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (5 : ZMod 223062602575272503) ^ 31866086082181786 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (5 : ZMod 223062602575272503) ^ 54259937381482 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (5 : ZMod 223062602575272503) ^ 361603321562 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (5 : ZMod 223062602575272503) ^ 35503393534 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide

private theorem prime_fifteenM_401 : Nat.Prime 401 := by norm_num
private theorem prime_fifteenM_3203 : Nat.Prime 3203 := by norm_num
private theorem prime_fifteenM_13845864341 : Nat.Prime 13845864341 := by
  apply lucas_primality 13845864341 (2 : ZMod 13845864341)
  · rw [← fifteenMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (5, 1), (7, 2), (11, 1), (401, 1), (3203, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (5, 1), (7, 2), (11, 1), (401, 1), (3203, 1)] : List FactorBlock).map factorBlockValue).prod = 13845864341 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fifteenM_2
      · exact prime_fifteenM_5
      · exact prime_fifteenM_7
      · exact prime_fifteenM_11
      · exact prime_fifteenM_401
      · exact prime_fifteenM_3203
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 13845864341) ^ 6922932170 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (2 : ZMod 13845864341) ^ 2769172868 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (2 : ZMod 13845864341) ^ 1977980620 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (2 : ZMod 13845864341) ^ 1258714940 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (2 : ZMod 13845864341) ^ 34528340 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (2 : ZMod 13845864341) ^ 4322780 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide

private theorem prime_fifteenM_139 : Nat.Prime 139 := by norm_num
private theorem prime_fifteenM_2442487 : Nat.Prime 2442487 := by norm_num
private theorem prime_fifteenM_18186758203 : Nat.Prime 18186758203 := by
  apply lucas_primality 18186758203 (2 : ZMod 18186758203)
  · rw [← fifteenMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (17, 1), (73, 1), (2442487, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (17, 1), (73, 1), (2442487, 1)] : List FactorBlock).map factorBlockValue).prod = 18186758203 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fifteenM_2
      · exact prime_fifteenM_3
      · exact prime_fifteenM_17
      · exact prime_fifteenM_73
      · exact prime_fifteenM_2442487
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 18186758203) ^ 9093379101 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (2 : ZMod 18186758203) ^ 6062252734 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (2 : ZMod 18186758203) ^ 1069809306 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (2 : ZMod 18186758203) ^ 249133674 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (2 : ZMod 18186758203) ^ 7446 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide

private theorem prime_fifteenM_27251402226539261 : Nat.Prime 27251402226539261 := by
  apply lucas_primality 27251402226539261 (3 : ZMod 27251402226539261)
  · rw [← fifteenMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (5, 1), (7, 2), (11, 1), (139, 1), (18186758203, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (5, 1), (7, 2), (11, 1), (139, 1), (18186758203, 1)] : List FactorBlock).map factorBlockValue).prod = 27251402226539261 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fifteenM_2
      · exact prime_fifteenM_5
      · exact prime_fifteenM_7
      · exact prime_fifteenM_11
      · exact prime_fifteenM_139
      · exact prime_fifteenM_18186758203
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 27251402226539261) ^ 13625701113269630 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (3 : ZMod 27251402226539261) ^ 5450280445307852 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (3 : ZMod 27251402226539261) ^ 3893057460934180 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (3 : ZMod 27251402226539261) ^ 2477400202412660 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (3 : ZMod 27251402226539261) ^ 196053253428340 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (3 : ZMod 27251402226539261) ^ 1498420 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide

private theorem prime_fifteenM_2122619 : Nat.Prime 2122619 := by norm_num
private theorem prime_fifteenM_433014277 : Nat.Prime 433014277 := by
  apply lucas_primality 433014277 (5 : ZMod 433014277)
  · rw [← fifteenMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (17, 1), (2122619, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (17, 1), (2122619, 1)] : List FactorBlock).map factorBlockValue).prod = 433014277 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fifteenM_2
      · exact prime_fifteenM_3
      · exact prime_fifteenM_17
      · exact prime_fifteenM_2122619
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 433014277) ^ 216507138 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (5 : ZMod 433014277) ^ 144338092 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (5 : ZMod 433014277) ^ 25471428 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (5 : ZMod 433014277) ^ 204 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide

private theorem prime_fifteenM_5075167 : Nat.Prime 5075167 := by norm_num
private theorem prime_fifteenM_152255011 : Nat.Prime 152255011 := by
  apply lucas_primality 152255011 (3 : ZMod 152255011)
  · rw [← fifteenMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (5, 1), (5075167, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (5, 1), (5075167, 1)] : List FactorBlock).map factorBlockValue).prod = 152255011 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fifteenM_2
      · exact prime_fifteenM_3
      · exact prime_fifteenM_5
      · exact prime_fifteenM_5075167
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 152255011) ^ 76127505 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (3 : ZMod 152255011) ^ 50751670 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (3 : ZMod 152255011) ^ 30451002 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (3 : ZMod 152255011) ^ 30 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide

private theorem prime_fifteenM_1045618291773007 : Nat.Prime 1045618291773007 := by
  apply lucas_primality 1045618291773007 (5 : ZMod 1045618291773007)
  · rw [← fifteenMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (7, 3), (47, 1), (71, 1), (152255011, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (7, 3), (47, 1), (71, 1), (152255011, 1)] : List FactorBlock).map factorBlockValue).prod = 1045618291773007 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fifteenM_2
      · exact prime_fifteenM_3
      · exact prime_fifteenM_7
      · exact prime_fifteenM_47
      · exact prime_fifteenM_71
      · exact prime_fifteenM_152255011
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 1045618291773007) ^ 522809145886503 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (5 : ZMod 1045618291773007) ^ 348539430591002 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (5 : ZMod 1045618291773007) ^ 149374041681858 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (5 : ZMod 1045618291773007) ^ 22247197697298 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (5 : ZMod 1045618291773007) ^ 14727018193986 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (5 : ZMod 1045618291773007) ^ 6867546 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide

private theorem prime_fifteenM_853224526086773713 : Nat.Prime 853224526086773713 := by
  apply lucas_primality 853224526086773713 (5 : ZMod 853224526086773713)
  · rw [← fifteenMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 4), (3, 1), (17, 1), (1045618291773007, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 4), (3, 1), (17, 1), (1045618291773007, 1)] : List FactorBlock).map factorBlockValue).prod = 853224526086773713 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fifteenM_2
      · exact prime_fifteenM_3
      · exact prime_fifteenM_17
      · exact prime_fifteenM_1045618291773007
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 853224526086773713) ^ 426612263043386856 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (5 : ZMod 853224526086773713) ^ 284408175362257904 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (5 : ZMod 853224526086773713) ^ 50189678005104336 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (5 : ZMod 853224526086773713) ^ 816 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide

private theorem prime_fifteenM_101 : Nat.Prime 101 := by norm_num
private theorem prime_fifteenM_25577 : Nat.Prime 25577 := by norm_num
private theorem prime_fifteenM_323797 : Nat.Prime 323797 := by norm_num
private theorem prime_fifteenM_120623 : Nat.Prime 120623 := by norm_num
private theorem prime_fifteenM_171767153 : Nat.Prime 171767153 := by
  apply lucas_primality 171767153 (3 : ZMod 171767153)
  · rw [← fifteenMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 4), (89, 1), (120623, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 4), (89, 1), (120623, 1)] : List FactorBlock).map factorBlockValue).prod = 171767153 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fifteenM_2
      · exact prime_fifteenM_89
      · exact prime_fifteenM_120623
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 171767153) ^ 85883576 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (3 : ZMod 171767153) ^ 1929968 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (3 : ZMod 171767153) ^ 1424 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide

private theorem prime_fifteenM_1030602919 : Nat.Prime 1030602919 := by
  apply lucas_primality 1030602919 (3 : ZMod 1030602919)
  · rw [← fifteenMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (171767153, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (171767153, 1)] : List FactorBlock).map factorBlockValue).prod = 1030602919 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fifteenM_2
      · exact prime_fifteenM_3
      · exact prime_fifteenM_171767153
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 1030602919) ^ 515301459 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (3 : ZMod 1030602919) ^ 343534306 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (3 : ZMod 1030602919) ^ 6 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide

private theorem prime_fifteenM_735850484167 : Nat.Prime 735850484167 := by
  apply lucas_primality 735850484167 (3 : ZMod 735850484167)
  · rw [← fifteenMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (7, 1), (17, 1), (1030602919, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (7, 1), (17, 1), (1030602919, 1)] : List FactorBlock).map factorBlockValue).prod = 735850484167 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fifteenM_2
      · exact prime_fifteenM_3
      · exact prime_fifteenM_7
      · exact prime_fifteenM_17
      · exact prime_fifteenM_1030602919
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 735850484167) ^ 367925242083 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (3 : ZMod 735850484167) ^ 245283494722 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (3 : ZMod 735850484167) ^ 105121497738 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (3 : ZMod 735850484167) ^ 43285322598 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (3 : ZMod 735850484167) ^ 714 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide

private theorem prime_fifteenM_140100513382431394213 : Nat.Prime 140100513382431394213 := by
  apply lucas_primality 140100513382431394213 (5 : ZMod 140100513382431394213)
  · rw [← fifteenMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (7, 2), (323797, 1), (735850484167, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (7, 2), (323797, 1), (735850484167, 1)] : List FactorBlock).map factorBlockValue).prod = 140100513382431394213 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fifteenM_2
      · exact prime_fifteenM_3
      · exact prime_fifteenM_7
      · exact prime_fifteenM_323797
      · exact prime_fifteenM_735850484167
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 140100513382431394213) ^ 70050256691215697106 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (5 : ZMod 140100513382431394213) ^ 46700171127477131404 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (5 : ZMod 140100513382431394213) ^ 20014359054633056316 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (5 : ZMod 140100513382431394213) ^ 432680084690196 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (5 : ZMod 140100513382431394213) ^ 190392636 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide

private theorem prime_fifteenM_180533 : Nat.Prime 180533 := by norm_num
private theorem prime_fifteenM_2161 : Nat.Prime 2161 := by norm_num
private theorem prime_fifteenM_8537 : Nat.Prime 8537 := by norm_num
private theorem prime_fifteenM_561521 : Nat.Prime 561521 := by norm_num
private theorem prime_fifteenM_19518469961 : Nat.Prime 19518469961 := by
  apply lucas_primality 19518469961 (3 : ZMod 19518469961)
  · rw [← fifteenMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (5, 1), (11, 1), (79, 1), (561521, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (5, 1), (11, 1), (79, 1), (561521, 1)] : List FactorBlock).map factorBlockValue).prod = 19518469961 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fifteenM_2
      · exact prime_fifteenM_5
      · exact prime_fifteenM_11
      · exact prime_fifteenM_79
      · exact prime_fifteenM_561521
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 19518469961) ^ 9759234980 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (3 : ZMod 19518469961) ^ 3903693992 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (3 : ZMod 19518469961) ^ 1774406360 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (3 : ZMod 19518469961) ^ 247069240 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (3 : ZMod 19518469961) ^ 34760 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide

private theorem prime_fifteenM_44650621068881221949 : Nat.Prime 44650621068881221949 := by
  apply lucas_primality 44650621068881221949 (2 : ZMod 44650621068881221949)
  · rw [← fifteenMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (31, 1), (2161, 1), (8537, 1), (19518469961, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (31, 1), (2161, 1), (8537, 1), (19518469961, 1)] : List FactorBlock).map factorBlockValue).prod = 44650621068881221949 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fifteenM_2
      · exact prime_fifteenM_31
      · exact prime_fifteenM_2161
      · exact prime_fifteenM_8537
      · exact prime_fifteenM_19518469961
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 44650621068881221949) ^ 22325310534440610974 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (2 : ZMod 44650621068881221949) ^ 1440342615125200708 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (2 : ZMod 44650621068881221949) ^ 20662018079075068 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (2 : ZMod 44650621068881221949) ^ 5230247284629404 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (2 : ZMod 44650621068881221949) ^ 2287608668 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide

private theorem prime_fifteenM_1964627327030773765757 : Nat.Prime 1964627327030773765757 := by
  apply lucas_primality 1964627327030773765757 (3 : ZMod 1964627327030773765757)
  · rw [← fifteenMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (11, 1), (44650621068881221949, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (11, 1), (44650621068881221949, 1)] : List FactorBlock).map factorBlockValue).prod = 1964627327030773765757 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fifteenM_2
      · exact prime_fifteenM_11
      · exact prime_fifteenM_44650621068881221949
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 1964627327030773765757) ^ 982313663515386882878 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (3 : ZMod 1964627327030773765757) ^ 178602484275524887796 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (3 : ZMod 1964627327030773765757) ^ 44 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide

private theorem prime_fifteenM_3421567 : Nat.Prime 3421567 := by norm_num
private theorem prime_fifteenM_3833 : Nat.Prime 3833 := by norm_num
private theorem prime_fifteenM_156521 : Nat.Prime 156521 := by norm_num
private theorem prime_fifteenM_18947 : Nat.Prime 18947 := by norm_num
private theorem prime_fifteenM_522823519 : Nat.Prime 522823519 := by
  apply lucas_primality 522823519 (6 : ZMod 522823519)
  · rw [← fifteenMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 3), (7, 1), (73, 1), (18947, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 3), (7, 1), (73, 1), (18947, 1)] : List FactorBlock).map factorBlockValue).prod = 522823519 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fifteenM_2
      · exact prime_fifteenM_3
      · exact prime_fifteenM_7
      · exact prime_fifteenM_73
      · exact prime_fifteenM_18947
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 522823519) ^ 261411759 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (6 : ZMod 522823519) ^ 174274506 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (6 : ZMod 522823519) ^ 74689074 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (6 : ZMod 522823519) ^ 7161966 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (6 : ZMod 522823519) ^ 27594 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide

private theorem prime_fifteenM_1472991480313183 : Nat.Prime 1472991480313183 := by
  apply lucas_primality 1472991480313183 (5 : ZMod 1472991480313183)
  · rw [← fifteenMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 2), (156521, 1), (522823519, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 2), (156521, 1), (522823519, 1)] : List FactorBlock).map factorBlockValue).prod = 1472991480313183 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fifteenM_2
      · exact prime_fifteenM_3
      · exact prime_fifteenM_156521
      · exact prime_fifteenM_522823519
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 1472991480313183) ^ 736495740156591 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (5 : ZMod 1472991480313183) ^ 490997160104394 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (5 : ZMod 1472991480313183) ^ 9410823342 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (5 : ZMod 1472991480313183) ^ 2817378 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide

private theorem prime_fifteenM_101627574192727747903 : Nat.Prime 101627574192727747903 := by
  apply lucas_primality 101627574192727747903 (3 : ZMod 101627574192727747903)
  · rw [← fifteenMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 2), (3833, 1), (1472991480313183, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 2), (3833, 1), (1472991480313183, 1)] : List FactorBlock).map factorBlockValue).prod = 101627574192727747903 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fifteenM_2
      · exact prime_fifteenM_3
      · exact prime_fifteenM_3833
      · exact prime_fifteenM_1472991480313183
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 101627574192727747903) ^ 50813787096363873951 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (3 : ZMod 101627574192727747903) ^ 33875858064242582634 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (3 : ZMod 101627574192727747903) ^ 26513846645637294 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (3 : ZMod 101627574192727747903) ^ 68994 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide

private theorem prime_fifteenM_44491 : Nat.Prime 44491 := by norm_num
private theorem prime_fifteenM_1032992039 : Nat.Prime 1032992039 := by
  apply lucas_primality 1032992039 (7 : ZMod 1032992039)
  · rw [← fifteenMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (13, 1), (19, 1), (47, 1), (44491, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (13, 1), (19, 1), (47, 1), (44491, 1)] : List FactorBlock).map factorBlockValue).prod = 1032992039 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fifteenM_2
      · exact prime_fifteenM_13
      · exact prime_fifteenM_19
      · exact prime_fifteenM_47
      · exact prime_fifteenM_44491
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 1032992039) ^ 516496019 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (7 : ZMod 1032992039) ^ 79460926 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (7 : ZMod 1032992039) ^ 54368002 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (7 : ZMod 1032992039) ^ 21978554 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (7 : ZMod 1032992039) ^ 23218 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide

private theorem prime_fifteenM_37501 : Nat.Prime 37501 := by norm_num
private theorem prime_fifteenM_121867 : Nat.Prime 121867 := by norm_num
private theorem prime_fifteenM_138923 : Nat.Prime 138923 := by norm_num
private theorem prime_fifteenM_338602584821 : Nat.Prime 338602584821 := by
  apply lucas_primality 338602584821 (3 : ZMod 338602584821)
  · rw [← fifteenMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (5, 1), (121867, 1), (138923, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (5, 1), (121867, 1), (138923, 1)] : List FactorBlock).map factorBlockValue).prod = 338602584821 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fifteenM_2
      · exact prime_fifteenM_5
      · exact prime_fifteenM_121867
      · exact prime_fifteenM_138923
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 338602584821) ^ 169301292410 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (3 : ZMod 338602584821) ^ 67720516964 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (3 : ZMod 338602584821) ^ 2778460 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (3 : ZMod 338602584821) ^ 2437340 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide

private theorem prime_fifteenM_25395871066744643 : Nat.Prime 25395871066744643 := by
  apply lucas_primality 25395871066744643 (2 : ZMod 25395871066744643)
  · rw [← fifteenMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (37501, 1), (338602584821, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (37501, 1), (338602584821, 1)] : List FactorBlock).map factorBlockValue).prod = 25395871066744643 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fifteenM_2
      · exact prime_fifteenM_37501
      · exact prime_fifteenM_338602584821
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 25395871066744643) ^ 12697935533372321 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (2 : ZMod 25395871066744643) ^ 677205169642 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (2 : ZMod 25395871066744643) ^ 75002 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide

private theorem prime_fifteenM_3727 : Nat.Prime 3727 := by norm_num
private theorem prime_fifteenM_239 : Nat.Prime 239 := by norm_num
private theorem prime_fifteenM_5059 : Nat.Prime 5059 := by norm_num
private theorem prime_fifteenM_2589239 : Nat.Prime 2589239 := by norm_num
private theorem prime_fifteenM_157187521213 : Nat.Prime 157187521213 := by
  apply lucas_primality 157187521213 (5 : ZMod 157187521213)
  · rw [← fifteenMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (5059, 1), (2589239, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (5059, 1), (2589239, 1)] : List FactorBlock).map factorBlockValue).prod = 157187521213 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fifteenM_2
      · exact prime_fifteenM_3
      · exact prime_fifteenM_5059
      · exact prime_fifteenM_2589239
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 157187521213) ^ 78593760606 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (5 : ZMod 157187521213) ^ 52395840404 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (5 : ZMod 157187521213) ^ 31070868 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (5 : ZMod 157187521213) ^ 60708 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide

private theorem prime_fifteenM_5600905755861617 : Nat.Prime 5600905755861617 := by
  apply lucas_primality 5600905755861617 (5 : ZMod 5600905755861617)
  · rw [← fifteenMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 4), (17, 1), (131, 1), (157187521213, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 4), (17, 1), (131, 1), (157187521213, 1)] : List FactorBlock).map factorBlockValue).prod = 5600905755861617 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fifteenM_2
      · exact prime_fifteenM_17
      · exact prime_fifteenM_131
      · exact prime_fifteenM_157187521213
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 5600905755861617) ^ 2800452877930808 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (5 : ZMod 5600905755861617) ^ 329465044462448 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (5 : ZMod 5600905755861617) ^ 42755005769936 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (5 : ZMod 5600905755861617) ^ 35632 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide

private theorem prime_fifteenM_8031698853905558779 : Nat.Prime 8031698853905558779 := by
  apply lucas_primality 8031698853905558779 (2 : ZMod 8031698853905558779)
  · rw [← fifteenMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (239, 1), (5600905755861617, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (239, 1), (5600905755861617, 1)] : List FactorBlock).map factorBlockValue).prod = 8031698853905558779 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fifteenM_2
      · exact prime_fifteenM_3
      · exact prime_fifteenM_239
      · exact prime_fifteenM_5600905755861617
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 8031698853905558779) ^ 4015849426952779389 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (2 : ZMod 8031698853905558779) ^ 2677232951301852926 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (2 : ZMod 8031698853905558779) ^ 33605434535169702 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (2 : ZMod 8031698853905558779) ^ 1434 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide

private theorem prime_fifteenM_89778329788956336031663 : Nat.Prime 89778329788956336031663 := by
  apply lucas_primality 89778329788956336031663 (3 : ZMod 89778329788956336031663)
  · rw [← fifteenMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 5), (23, 1), (8031698853905558779, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 5), (23, 1), (8031698853905558779, 1)] : List FactorBlock).map factorBlockValue).prod = 89778329788956336031663 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fifteenM_2
      · exact prime_fifteenM_3
      · exact prime_fifteenM_23
      · exact prime_fifteenM_8031698853905558779
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 89778329788956336031663) ^ 44889164894478168015831 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (3 : ZMod 89778329788956336031663) ^ 29926109929652112010554 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (3 : ZMod 89778329788956336031663) ^ 3903405642998101566594 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (3 : ZMod 89778329788956336031663) ^ 11178 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide

private theorem prime_fifteenM_7294097 : Nat.Prime 7294097 := by norm_num
private theorem prime_fifteenM_7411 : Nat.Prime 7411 := by norm_num
private theorem prime_fifteenM_93287 : Nat.Prime 93287 := by norm_num
private theorem prime_fifteenM_2098079 : Nat.Prime 2098079 := by norm_num
private theorem prime_fifteenM_4070273261 : Nat.Prime 4070273261 := by
  apply lucas_primality 4070273261 (2 : ZMod 4070273261)
  · rw [← fifteenMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (5, 1), (97, 1), (2098079, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (5, 1), (97, 1), (2098079, 1)] : List FactorBlock).map factorBlockValue).prod = 4070273261 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fifteenM_2
      · exact prime_fifteenM_5
      · exact prime_fifteenM_97
      · exact prime_fifteenM_2098079
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 4070273261) ^ 2035136630 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (2 : ZMod 4070273261) ^ 814054652 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (2 : ZMod 4070273261) ^ 41961580 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (2 : ZMod 4070273261) ^ 1940 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide

private theorem prime_fifteenM_45023731903529596433 : Nat.Prime 45023731903529596433 := by
  apply lucas_primality 45023731903529596433 (3 : ZMod 45023731903529596433)
  · rw [← fifteenMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 4), (7411, 1), (93287, 1), (4070273261, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 4), (7411, 1), (93287, 1), (4070273261, 1)] : List FactorBlock).map factorBlockValue).prod = 45023731903529596433 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fifteenM_2
      · exact prime_fifteenM_7411
      · exact prime_fifteenM_93287
      · exact prime_fifteenM_4070273261
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 45023731903529596433) ^ 22511865951764798216 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (3 : ZMod 45023731903529596433) ^ 6075257307182512 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (3 : ZMod 45023731903529596433) ^ 482636722196336 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (3 : ZMod 45023731903529596433) ^ 11061599312 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide

private theorem prime_fifteenM_4637 : Nat.Prime 4637 := by norm_num
private theorem prime_fifteenM_13311821 : Nat.Prime 13311821 := by norm_num
private theorem prime_fifteenM_2076644077 : Nat.Prime 2076644077 := by
  apply lucas_primality 2076644077 (2 : ZMod 2076644077)
  · rw [← fifteenMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (13, 1), (13311821, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (13, 1), (13311821, 1)] : List FactorBlock).map factorBlockValue).prod = 2076644077 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fifteenM_2
      · exact prime_fifteenM_3
      · exact prime_fifteenM_13
      · exact prime_fifteenM_13311821
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 2076644077) ^ 1038322038 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (2 : ZMod 2076644077) ^ 692214692 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (2 : ZMod 2076644077) ^ 159741852 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (2 : ZMod 2076644077) ^ 156 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide

private theorem prime_fifteenM_809 : Nat.Prime 809 := by norm_num
private theorem prime_fifteenM_1873 : Nat.Prime 1873 := by norm_num
private theorem prime_fifteenM_14851 : Nat.Prime 14851 := by norm_num
private theorem prime_fifteenM_166895539 : Nat.Prime 166895539 := by
  apply lucas_primality 166895539 (2 : ZMod 166895539)
  · rw [← fifteenMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (1873, 1), (14851, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (1873, 1), (14851, 1)] : List FactorBlock).map factorBlockValue).prod = 166895539 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fifteenM_2
      · exact prime_fifteenM_3
      · exact prime_fifteenM_1873
      · exact prime_fifteenM_14851
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 166895539) ^ 83447769 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (2 : ZMod 166895539) ^ 55631846 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (2 : ZMod 166895539) ^ 89106 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (2 : ZMod 166895539) ^ 11238 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide

private theorem prime_fifteenM_33484585780649 : Nat.Prime 33484585780649 := by
  apply lucas_primality 33484585780649 (3 : ZMod 33484585780649)
  · rw [← fifteenMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (31, 1), (809, 1), (166895539, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (31, 1), (809, 1), (166895539, 1)] : List FactorBlock).map factorBlockValue).prod = 33484585780649 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fifteenM_2
      · exact prime_fifteenM_31
      · exact prime_fifteenM_809
      · exact prime_fifteenM_166895539
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 33484585780649) ^ 16742292890324 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (3 : ZMod 33484585780649) ^ 1080147928408 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (3 : ZMod 33484585780649) ^ 41390093672 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (3 : ZMod 33484585780649) ^ 200632 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide

private theorem prime_fifteenM_29429 : Nat.Prime 29429 := by norm_num
private theorem prime_fifteenM_7252633 : Nat.Prime 7252633 := by norm_num
private theorem prime_fifteenM_87031597 : Nat.Prime 87031597 := by
  apply lucas_primality 87031597 (2 : ZMod 87031597)
  · rw [← fifteenMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (7252633, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (7252633, 1)] : List FactorBlock).map factorBlockValue).prod = 87031597 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fifteenM_2
      · exact prime_fifteenM_3
      · exact prime_fifteenM_7252633
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 87031597) ^ 43515798 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (2 : ZMod 87031597) ^ 29010532 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (2 : ZMod 87031597) ^ 12 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide

private theorem prime_fifteenM_17754445789 : Nat.Prime 17754445789 := by
  apply lucas_primality 17754445789 (2 : ZMod 17754445789)
  · rw [← fifteenMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (17, 1), (87031597, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (17, 1), (87031597, 1)] : List FactorBlock).map factorBlockValue).prod = 17754445789 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fifteenM_2
      · exact prime_fifteenM_3
      · exact prime_fifteenM_17
      · exact prime_fifteenM_87031597
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 17754445789) ^ 8877222894 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (2 : ZMod 17754445789) ^ 5918148596 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (2 : ZMod 17754445789) ^ 1044379164 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (2 : ZMod 17754445789) ^ 204 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide

private theorem prime_fifteenM_487 : Nat.Prime 487 := by norm_num
private theorem prime_fifteenM_997 : Nat.Prime 997 := by norm_num
private theorem prime_fifteenM_2837 : Nat.Prime 2837 := by norm_num
private theorem prime_fifteenM_606088622921 : Nat.Prime 606088622921 := by
  apply lucas_primality 606088622921 (7 : ZMod 606088622921)
  · rw [← fifteenMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (5, 1), (11, 1), (487, 1), (997, 1), (2837, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (5, 1), (11, 1), (487, 1), (997, 1), (2837, 1)] : List FactorBlock).map factorBlockValue).prod = 606088622921 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fifteenM_2
      · exact prime_fifteenM_5
      · exact prime_fifteenM_11
      · exact prime_fifteenM_487
      · exact prime_fifteenM_997
      · exact prime_fifteenM_2837
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 606088622921) ^ 303044311460 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (7 : ZMod 606088622921) ^ 121217724584 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (7 : ZMod 606088622921) ^ 55098965720 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (7 : ZMod 606088622921) ^ 1244535160 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (7 : ZMod 606088622921) ^ 607912360 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (7 : ZMod 606088622921) ^ 213637160 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide

private theorem prime_fifteenM_431 : Nat.Prime 431 := by norm_num
private theorem prime_fifteenM_28031 : Nat.Prime 28031 := by norm_num
private theorem prime_fifteenM_193301777 : Nat.Prime 193301777 := by
  apply lucas_primality 193301777 (3 : ZMod 193301777)
  · rw [← fifteenMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 4), (431, 1), (28031, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 4), (431, 1), (28031, 1)] : List FactorBlock).map factorBlockValue).prod = 193301777 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fifteenM_2
      · exact prime_fifteenM_431
      · exact prime_fifteenM_28031
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 193301777) ^ 96650888 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (3 : ZMod 193301777) ^ 448496 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (3 : ZMod 193301777) ^ 6896 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide

private theorem prime_fifteenM_9278485297 : Nat.Prime 9278485297 := by
  apply lucas_primality 9278485297 (5 : ZMod 9278485297)
  · rw [← fifteenMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 4), (3, 1), (193301777, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 4), (3, 1), (193301777, 1)] : List FactorBlock).map factorBlockValue).prod = 9278485297 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fifteenM_2
      · exact prime_fifteenM_3
      · exact prime_fifteenM_193301777
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 9278485297) ^ 4639242648 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (5 : ZMod 9278485297) ^ 3092828432 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (5 : ZMod 9278485297) ^ 48 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide

private theorem prime_fifteenM_509 : Nat.Prime 509 := by norm_num
private theorem prime_fifteenM_9473 : Nat.Prime 9473 := by norm_num
private theorem prime_fifteenM_170447 : Nat.Prime 170447 := by norm_num
private theorem prime_fifteenM_1372447766351 : Nat.Prime 1372447766351 := by
  apply lucas_primality 1372447766351 (7 : ZMod 1372447766351)
  · rw [← fifteenMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 2), (17, 1), (9473, 1), (170447, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 2), (17, 1), (9473, 1), (170447, 1)] : List FactorBlock).map factorBlockValue).prod = 1372447766351 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fifteenM_2
      · exact prime_fifteenM_5
      · exact prime_fifteenM_17
      · exact prime_fifteenM_9473
      · exact prime_fifteenM_170447
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 1372447766351) ^ 686223883175 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (7 : ZMod 1372447766351) ^ 274489553270 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (7 : ZMod 1372447766351) ^ 80732221550 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (7 : ZMod 1372447766351) ^ 144879950 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (7 : ZMod 1372447766351) ^ 8052050 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide

private theorem prime_fifteenM_33531643827487633 : Nat.Prime 33531643827487633 := by
  apply lucas_primality 33531643827487633 (15 : ZMod 33531643827487633)
  · rw [← fifteenMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 4), (3, 1), (509, 1), (1372447766351, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 4), (3, 1), (509, 1), (1372447766351, 1)] : List FactorBlock).map factorBlockValue).prod = 33531643827487633 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fifteenM_2
      · exact prime_fifteenM_3
      · exact prime_fifteenM_509
      · exact prime_fifteenM_1372447766351
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (15 : ZMod 33531643827487633) ^ 16765821913743816 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (15 : ZMod 33531643827487633) ^ 11177214609162544 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (15 : ZMod 33531643827487633) ^ 65877492784848 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (15 : ZMod 33531643827487633) ^ 24432 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide

private theorem prime_fifteenM_7873 : Nat.Prime 7873 := by norm_num
private theorem prime_fifteenM_9467 : Nat.Prime 9467 := by norm_num
private theorem prime_fifteenM_265241 : Nat.Prime 265241 := by norm_num
private theorem prime_fifteenM_7556611 : Nat.Prime 7556611 := by norm_num
private theorem prime_fifteenM_75566111 : Nat.Prime 75566111 := by
  apply lucas_primality 75566111 (11 : ZMod 75566111)
  · rw [← fifteenMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 1), (7556611, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 1), (7556611, 1)] : List FactorBlock).map factorBlockValue).prod = 75566111 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fifteenM_2
      · exact prime_fifteenM_5
      · exact prime_fifteenM_7556611
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (11 : ZMod 75566111) ^ 37783055 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (11 : ZMod 75566111) ^ 15113222 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (11 : ZMod 75566111) ^ 10 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide

private theorem prime_fifteenM_1042248004083053 : Nat.Prime 1042248004083053 := by
  apply lucas_primality 1042248004083053 (2 : ZMod 1042248004083053)
  · rw [← fifteenMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (13, 1), (265241, 1), (75566111, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (13, 1), (265241, 1), (75566111, 1)] : List FactorBlock).map factorBlockValue).prod = 1042248004083053 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fifteenM_2
      · exact prime_fifteenM_13
      · exact prime_fifteenM_265241
      · exact prime_fifteenM_75566111
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1042248004083053) ^ 521124002041526 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (2 : ZMod 1042248004083053) ^ 80172923391004 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (2 : ZMod 1042248004083053) ^ 3929437772 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (2 : ZMod 1042248004083053) ^ 13792532 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide

private theorem prime_fifteenM_38836361859919178187937 : Nat.Prime 38836361859919178187937 := by
  apply lucas_primality 38836361859919178187937 (5 : ZMod 38836361859919178187937)
  · rw [← fifteenMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 5), (3, 1), (41, 1), (9467, 1), (1042248004083053, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 5), (3, 1), (41, 1), (9467, 1), (1042248004083053, 1)] : List FactorBlock).map factorBlockValue).prod = 38836361859919178187937 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fifteenM_2
      · exact prime_fifteenM_3
      · exact prime_fifteenM_41
      · exact prime_fifteenM_9467
      · exact prime_fifteenM_1042248004083053
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 38836361859919178187937) ^ 19418180929959589093968 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (5 : ZMod 38836361859919178187937) ^ 12945453953306392729312 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (5 : ZMod 38836361859919178187937) ^ 947228338046809224096 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (5 : ZMod 38836361859919178187937) ^ 4102288144070896608 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (5 : ZMod 38836361859919178187937) ^ 37262112 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide

private theorem prime_fifteenM_233 : Nat.Prime 233 := by norm_num
private theorem prime_fifteenM_3007847 : Nat.Prime 3007847 := by norm_num
private theorem prime_fifteenM_6581 : Nat.Prime 6581 := by norm_num
private theorem prime_fifteenM_20072051 : Nat.Prime 20072051 := by
  apply lucas_primality 20072051 (14 : ZMod 20072051)
  · rw [← fifteenMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 2), (61, 1), (6581, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 2), (61, 1), (6581, 1)] : List FactorBlock).map factorBlockValue).prod = 20072051 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fifteenM_2
      · exact prime_fifteenM_5
      · exact prime_fifteenM_61
      · exact prime_fifteenM_6581
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (14 : ZMod 20072051) ^ 10036025 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (14 : ZMod 20072051) ^ 4014410 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (14 : ZMod 20072051) ^ 329050 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (14 : ZMod 20072051) ^ 3050 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide

private theorem prime_fifteenM_40144103 : Nat.Prime 40144103 := by
  apply lucas_primality 40144103 (5 : ZMod 40144103)
  · rw [← fifteenMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (20072051, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (20072051, 1)] : List FactorBlock).map factorBlockValue).prod = 40144103 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_fifteenM_2
      · exact prime_fifteenM_20072051
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 40144103) ^ 20072051 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (5 : ZMod 40144103) ^ 2 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide

private theorem prime_fifteenM_293 : Nat.Prime 293 := by norm_num
private theorem prime_fifteenM_651127 : Nat.Prime 651127 := by norm_num
private theorem prime_fifteenM_10683691817 : Nat.Prime 10683691817 := by
  apply lucas_primality 10683691817 (3 : ZMod 10683691817)
  · rw [← fifteenMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (7, 1), (293, 1), (651127, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (7, 1), (293, 1), (651127, 1)] : List FactorBlock).map factorBlockValue).prod = 10683691817 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fifteenM_2
      · exact prime_fifteenM_7
      · exact prime_fifteenM_293
      · exact prime_fifteenM_651127
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 10683691817) ^ 5341845908 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (3 : ZMod 10683691817) ^ 1526241688 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (3 : ZMod 10683691817) ^ 36463112 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (3 : ZMod 10683691817) ^ 16408 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide

private theorem prime_fifteenM_18959 : Nat.Prime 18959 := by norm_num
private theorem prime_fifteenM_20930737 : Nat.Prime 20930737 := by
  apply lucas_primality 20930737 (5 : ZMod 20930737)
  · rw [← fifteenMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 4), (3, 1), (23, 1), (18959, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 4), (3, 1), (23, 1), (18959, 1)] : List FactorBlock).map factorBlockValue).prod = 20930737 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fifteenM_2
      · exact prime_fifteenM_3
      · exact prime_fifteenM_23
      · exact prime_fifteenM_18959
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 20930737) ^ 10465368 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (5 : ZMod 20930737) ^ 6976912 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (5 : ZMod 20930737) ^ 910032 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (5 : ZMod 20930737) ^ 1104 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide

private theorem prime_fifteenM_28807 : Nat.Prime 28807 := by norm_num
private theorem prime_fifteenM_1849103 : Nat.Prime 1849103 := by norm_num
private theorem prime_fifteenM_456818736397697 : Nat.Prime 456818736397697 := by
  apply lucas_primality 456818736397697 (3 : ZMod 456818736397697)
  · rw [← fifteenMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 7), (67, 1), (28807, 1), (1849103, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 7), (67, 1), (28807, 1), (1849103, 1)] : List FactorBlock).map factorBlockValue).prod = 456818736397697 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fifteenM_2
      · exact prime_fifteenM_67
      · exact prime_fifteenM_28807
      · exact prime_fifteenM_1849103
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 456818736397697) ^ 228409368198848 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (3 : ZMod 456818736397697) ^ 6818190095488 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (3 : ZMod 456818736397697) ^ 15857907328 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (3 : ZMod 456818736397697) ^ 247048832 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide

private theorem prime_fifteenM_6395462309567759 : Nat.Prime 6395462309567759 := by
  apply lucas_primality 6395462309567759 (7 : ZMod 6395462309567759)
  · rw [← fifteenMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (7, 1), (456818736397697, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (7, 1), (456818736397697, 1)] : List FactorBlock).map factorBlockValue).prod = 6395462309567759 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fifteenM_2
      · exact prime_fifteenM_7
      · exact prime_fifteenM_456818736397697
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 6395462309567759) ^ 3197731154783879 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (7 : ZMod 6395462309567759) ^ 913637472795394 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (7 : ZMod 6395462309567759) ^ 14 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide

private theorem prime_fifteenM_14121180779525611873 : Nat.Prime 14121180779525611873 := by
  apply lucas_primality 14121180779525611873 (5 : ZMod 14121180779525611873)
  · rw [← fifteenMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 5), (3, 1), (23, 1), (6395462309567759, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 5), (3, 1), (23, 1), (6395462309567759, 1)] : List FactorBlock).map factorBlockValue).prod = 14121180779525611873 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fifteenM_2
      · exact prime_fifteenM_3
      · exact prime_fifteenM_23
      · exact prime_fifteenM_6395462309567759
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 14121180779525611873) ^ 7060590389762805936 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (5 : ZMod 14121180779525611873) ^ 4707060259841870624 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (5 : ZMod 14121180779525611873) ^ 613964381718504864 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (5 : ZMod 14121180779525611873) ^ 2208 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide

private theorem prime_fifteenM_290721364943316951027384001 : Nat.Prime 290721364943316951027384001 := by
  apply lucas_primality 290721364943316951027384001 (122 : ZMod 290721364943316951027384001)
  · rw [← fifteenMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 6), (3, 4), (5, 3), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 6), (3, 4), (5, 3), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1)] : List FactorBlock).map factorBlockValue).prod = 290721364943316951027384001 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fifteenM_2
      · exact prime_fifteenM_3
      · exact prime_fifteenM_5
      · exact prime_fifteenM_7
      · exact prime_fifteenM_11
      · exact prime_fifteenM_13
      · exact prime_fifteenM_17
      · exact prime_fifteenM_19
      · exact prime_fifteenM_23
      · exact prime_fifteenM_29
      · exact prime_fifteenM_31
      · exact prime_fifteenM_37
      · exact prime_fifteenM_41
      · exact prime_fifteenM_43
      · exact prime_fifteenM_47
      · exact prime_fifteenM_53
      · exact prime_fifteenM_59
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (122 : ZMod 290721364943316951027384001) ^ 145360682471658475513692000 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (122 : ZMod 290721364943316951027384001) ^ 96907121647772317009128000 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (122 : ZMod 290721364943316951027384001) ^ 58144272988663390205476800 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (122 : ZMod 290721364943316951027384001) ^ 41531623563330993003912000 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (122 : ZMod 290721364943316951027384001) ^ 26429214994846995547944000 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (122 : ZMod 290721364943316951027384001) ^ 22363181918716688540568000 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (122 : ZMod 290721364943316951027384001) ^ 17101256761371585354552000 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (122 : ZMod 290721364943316951027384001) ^ 15301124470700892159336000 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (122 : ZMod 290721364943316951027384001) ^ 12640059345361606566408000 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (122 : ZMod 290721364943316951027384001) ^ 10024874653217825897496000 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (122 : ZMod 290721364943316951027384001) ^ 9378108546558611323464000 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (122 : ZMod 290721364943316951027384001) ^ 7857334187657214892632000 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (122 : ZMod 290721364943316951027384001) ^ 7090764998617486610424000 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (122 : ZMod 290721364943316951027384001) ^ 6760961975425975605288000 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (122 : ZMod 290721364943316951027384001) ^ 6185560956240786192072000 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (122 : ZMod 290721364943316951027384001) ^ 5485308772515414170328000 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (122 : ZMod 290721364943316951027384001) ^ 4927480761751134763176000 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide

private theorem prime_fifteenM_286032310670037645365652001 : Nat.Prime 286032310670037645365652001 := by
  apply lucas_primality 286032310670037645365652001 (71 : ZMod 286032310670037645365652001)
  · rw [← fifteenMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 5), (3, 4), (5, 3), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 5), (3, 4), (5, 3), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod = 286032310670037645365652001 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fifteenM_2
      · exact prime_fifteenM_3
      · exact prime_fifteenM_5
      · exact prime_fifteenM_7
      · exact prime_fifteenM_11
      · exact prime_fifteenM_13
      · exact prime_fifteenM_17
      · exact prime_fifteenM_19
      · exact prime_fifteenM_23
      · exact prime_fifteenM_29
      · exact prime_fifteenM_37
      · exact prime_fifteenM_41
      · exact prime_fifteenM_43
      · exact prime_fifteenM_47
      · exact prime_fifteenM_53
      · exact prime_fifteenM_59
      · exact prime_fifteenM_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (71 : ZMod 286032310670037645365652001) ^ 143016155335018822682826000 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (71 : ZMod 286032310670037645365652001) ^ 95344103556679215121884000 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (71 : ZMod 286032310670037645365652001) ^ 57206462134007529073130400 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (71 : ZMod 286032310670037645365652001) ^ 40861758667148235052236000 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (71 : ZMod 286032310670037645365652001) ^ 26002937333639785942332000 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (71 : ZMod 286032310670037645365652001) ^ 22002485436156741951204000 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (71 : ZMod 286032310670037645365652001) ^ 16825430039413979139156000 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (71 : ZMod 286032310670037645365652001) ^ 15054332140528297124508000 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (71 : ZMod 286032310670037645365652001) ^ 12436187420436419363724000 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (71 : ZMod 286032310670037645365652001) ^ 9863183126553022253988000 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (71 : ZMod 286032310670037645365652001) ^ 7730602991082098523396000 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (71 : ZMod 286032310670037645365652001) ^ 6976397821220430374772000 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (71 : ZMod 286032310670037645365652001) ^ 6651914201628782450364000 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (71 : ZMod 286032310670037645365652001) ^ 6085793844043354156716000 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (71 : ZMod 286032310670037645365652001) ^ 5396836050378068780484000 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (71 : ZMod 286032310670037645365652001) ^ 4848005265593858396028000 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (71 : ZMod 286032310670037645365652001) ^ 4689054273279305661732000 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide

private theorem prime_fifteenM_659 : Nat.Prime 659 := by norm_num
private theorem prime_fifteenM_55001 : Nat.Prime 55001 := by norm_num
private theorem prime_fifteenM_197 : Nat.Prime 197 := by norm_num
private theorem prime_fifteenM_13297 : Nat.Prime 13297 := by norm_num
private theorem prime_fifteenM_1087747789 : Nat.Prime 1087747789 := by
  apply lucas_primality 1087747789 (2 : ZMod 1087747789)
  · rw [← fifteenMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (17, 1), (401, 1), (13297, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (17, 1), (401, 1), (13297, 1)] : List FactorBlock).map factorBlockValue).prod = 1087747789 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fifteenM_2
      · exact prime_fifteenM_3
      · exact prime_fifteenM_17
      · exact prime_fifteenM_401
      · exact prime_fifteenM_13297
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1087747789) ^ 543873894 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (2 : ZMod 1087747789) ^ 362582596 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (2 : ZMod 1087747789) ^ 63985164 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (2 : ZMod 1087747789) ^ 2712588 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (2 : ZMod 1087747789) ^ 81804 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide

private theorem prime_fifteenM_121827752369 : Nat.Prime 121827752369 := by
  apply lucas_primality 121827752369 (3 : ZMod 121827752369)
  · rw [← fifteenMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 4), (7, 1), (1087747789, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 4), (7, 1), (1087747789, 1)] : List FactorBlock).map factorBlockValue).prod = 121827752369 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fifteenM_2
      · exact prime_fifteenM_7
      · exact prime_fifteenM_1087747789
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 121827752369) ^ 60913876184 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (3 : ZMod 121827752369) ^ 17403964624 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (3 : ZMod 121827752369) ^ 112 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide

private theorem prime_fifteenM_576001613200633 : Nat.Prime 576001613200633 := by
  apply lucas_primality 576001613200633 (5 : ZMod 576001613200633)
  · rw [← fifteenMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (3, 1), (197, 1), (121827752369, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (3, 1), (197, 1), (121827752369, 1)] : List FactorBlock).map factorBlockValue).prod = 576001613200633 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fifteenM_2
      · exact prime_fifteenM_3
      · exact prime_fifteenM_197
      · exact prime_fifteenM_121827752369
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 576001613200633) ^ 288000806600316 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (5 : ZMod 576001613200633) ^ 192000537733544 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (5 : ZMod 576001613200633) ^ 2923866056856 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (5 : ZMod 576001613200633) ^ 4728 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide

private theorem prime_fifteenM_18126523 : Nat.Prime 18126523 := by norm_num
private theorem prime_fifteenM_359 : Nat.Prime 359 := by norm_num
private theorem prime_fifteenM_3477841 : Nat.Prime 3477841 := by norm_num
private theorem prime_fifteenM_20867047 : Nat.Prime 20867047 := by
  apply lucas_primality 20867047 (5 : ZMod 20867047)
  · rw [← fifteenMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (3477841, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (3477841, 1)] : List FactorBlock).map factorBlockValue).prod = 20867047 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fifteenM_2
      · exact prime_fifteenM_3
      · exact prime_fifteenM_3477841
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 20867047) ^ 10433523 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (5 : ZMod 20867047) ^ 6955682 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (5 : ZMod 20867047) ^ 6 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide

private theorem prime_fifteenM_13146239611 : Nat.Prime 13146239611 := by
  apply lucas_primality 13146239611 (13 : ZMod 13146239611)
  · rw [← fifteenMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 2), (5, 1), (7, 1), (20867047, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 2), (5, 1), (7, 1), (20867047, 1)] : List FactorBlock).map factorBlockValue).prod = 13146239611 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fifteenM_2
      · exact prime_fifteenM_3
      · exact prime_fifteenM_5
      · exact prime_fifteenM_7
      · exact prime_fifteenM_20867047
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 13146239611) ^ 6573119805 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (13 : ZMod 13146239611) ^ 4382079870 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (13 : ZMod 13146239611) ^ 2629247922 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (13 : ZMod 13146239611) ^ 1878034230 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (13 : ZMod 13146239611) ^ 630 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide

private theorem prime_fifteenM_66073000284887 : Nat.Prime 66073000284887 := by
  apply lucas_primality 66073000284887 (5 : ZMod 66073000284887)
  · rw [← fifteenMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (7, 1), (359, 1), (13146239611, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (7, 1), (359, 1), (13146239611, 1)] : List FactorBlock).map factorBlockValue).prod = 66073000284887 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fifteenM_2
      · exact prime_fifteenM_7
      · exact prime_fifteenM_359
      · exact prime_fifteenM_13146239611
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 66073000284887) ^ 33036500142443 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (5 : ZMod 66073000284887) ^ 9439000040698 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (5 : ZMod 66073000284887) ^ 184047354554 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (5 : ZMod 66073000284887) ^ 5026 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide

private theorem prime_fifteenM_17318362560099935559248461 : Nat.Prime 17318362560099935559248461 := by
  apply lucas_primality 17318362560099935559248461 (2 : ZMod 17318362560099935559248461)
  · rw [← fifteenMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (5, 1), (241, 1), (18126523, 1), (66073000284887, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (5, 1), (241, 1), (18126523, 1), (66073000284887, 1)] : List FactorBlock).map factorBlockValue).prod = 17318362560099935559248461 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fifteenM_2
      · exact prime_fifteenM_3
      · exact prime_fifteenM_5
      · exact prime_fifteenM_241
      · exact prime_fifteenM_18126523
      · exact prime_fifteenM_66073000284887
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 17318362560099935559248461) ^ 8659181280049967779624230 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (2 : ZMod 17318362560099935559248461) ^ 5772787520033311853082820 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (2 : ZMod 17318362560099935559248461) ^ 3463672512019987111849692 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (2 : ZMod 17318362560099935559248461) ^ 71860425560580645474060 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (2 : ZMod 17318362560099935559248461) ^ 955415584119466020 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (2 : ZMod 17318362560099935559248461) ^ 262109522580 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide

private theorem prime_fifteenM_272830819408343600194929601 : Nat.Prime 272830819408343600194929601 := by
  apply lucas_primality 272830819408343600194929601 (39 : ZMod 272830819408343600194929601)
  · rw [← fifteenMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 6), (3, 4), (5, 2), (7, 2), (11, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 6), (3, 4), (5, 2), (7, 2), (11, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod = 272830819408343600194929601 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fifteenM_2
      · exact prime_fifteenM_3
      · exact prime_fifteenM_5
      · exact prime_fifteenM_7
      · exact prime_fifteenM_11
      · exact prime_fifteenM_17
      · exact prime_fifteenM_19
      · exact prime_fifteenM_23
      · exact prime_fifteenM_29
      · exact prime_fifteenM_31
      · exact prime_fifteenM_37
      · exact prime_fifteenM_41
      · exact prime_fifteenM_43
      · exact prime_fifteenM_47
      · exact prime_fifteenM_53
      · exact prime_fifteenM_59
      · exact prime_fifteenM_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (39 : ZMod 272830819408343600194929601) ^ 136415409704171800097464800 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (39 : ZMod 272830819408343600194929601) ^ 90943606469447866731643200 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (39 : ZMod 272830819408343600194929601) ^ 54566163881668720038985920 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (39 : ZMod 272830819408343600194929601) ^ 38975831344049085742132800 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (39 : ZMod 272830819408343600194929601) ^ 24802801764394872744993600 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (39 : ZMod 272830819408343600194929601) ^ 16048871729902564717348800 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (39 : ZMod 272830819408343600194929601) ^ 14359516810965452641838400 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (39 : ZMod 272830819408343600194929601) ^ 11862209539493200008475200 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (39 : ZMod 272830819408343600194929601) ^ 9407959289942882765342400 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (39 : ZMod 272830819408343600194929601) ^ 8800994174462696780481600 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (39 : ZMod 272830819408343600194929601) ^ 7373805929955232437700800 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (39 : ZMod 272830819408343600194929601) ^ 6654410229471795126705600 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (39 : ZMod 272830819408343600194929601) ^ 6344902776938223260347200 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (39 : ZMod 272830819408343600194929601) ^ 5804911051241353195636800 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (39 : ZMod 272830819408343600194929601) ^ 5147751309591388682923200 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (39 : ZMod 272830819408343600194929601) ^ 4624251176412603393134400 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (39 : ZMod 272830819408343600194929601) ^ 4472636383743337708113600 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide

private theorem prime_fifteenM_1471 : Nat.Prime 1471 := by norm_num
private theorem prime_fifteenM_48383 : Nat.Prime 48383 := by norm_num
private theorem prime_fifteenM_124459 : Nat.Prime 124459 := by norm_num
private theorem prime_fifteenM_52023863 : Nat.Prime 52023863 := by
  apply lucas_primality 52023863 (5 : ZMod 52023863)
  · rw [← fifteenMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (11, 1), (19, 1), (124459, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (11, 1), (19, 1), (124459, 1)] : List FactorBlock).map factorBlockValue).prod = 52023863 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fifteenM_2
      · exact prime_fifteenM_11
      · exact prime_fifteenM_19
      · exact prime_fifteenM_124459
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 52023863) ^ 26011931 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (5 : ZMod 52023863) ^ 4729442 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (5 : ZMod 52023863) ^ 2738098 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (5 : ZMod 52023863) ^ 418 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide

private theorem prime_fifteenM_2267800291 : Nat.Prime 2267800291 := by
  apply lucas_primality 2267800291 (26 : ZMod 2267800291)
  · rw [← fifteenMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 2), (5, 1), (7, 1), (19, 1), (29, 1), (47, 1), (139, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 2), (5, 1), (7, 1), (19, 1), (29, 1), (47, 1), (139, 1)] : List FactorBlock).map factorBlockValue).prod = 2267800291 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fifteenM_2
      · exact prime_fifteenM_3
      · exact prime_fifteenM_5
      · exact prime_fifteenM_7
      · exact prime_fifteenM_19
      · exact prime_fifteenM_29
      · exact prime_fifteenM_47
      · exact prime_fifteenM_139
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (26 : ZMod 2267800291) ^ 1133900145 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (26 : ZMod 2267800291) ^ 755933430 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (26 : ZMod 2267800291) ^ 453560058 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (26 : ZMod 2267800291) ^ 323971470 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (26 : ZMod 2267800291) ^ 119357910 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (26 : ZMod 2267800291) ^ 78200010 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (26 : ZMod 2267800291) ^ 48251070 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (26 : ZMod 2267800291) ^ 16315110 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide

private theorem prime_fifteenM_3775351412811012257 : Nat.Prime 3775351412811012257 := by
  apply lucas_primality 3775351412811012257 (3 : ZMod 3775351412811012257)
  · rw [← fifteenMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 5), (52023863, 1), (2267800291, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 5), (52023863, 1), (2267800291, 1)] : List FactorBlock).map factorBlockValue).prod = 3775351412811012257 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fifteenM_2
      · exact prime_fifteenM_52023863
      · exact prime_fifteenM_2267800291
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 3775351412811012257) ^ 1887675706405506128 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (3 : ZMod 3775351412811012257) ^ 72569609312 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (3 : ZMod 3775351412811012257) ^ 1664763616 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide

private theorem prime_fifteenM_543841 : Nat.Prime 543841 := by norm_num
private theorem prime_fifteenM_8864759 : Nat.Prime 8864759 := by norm_num
private theorem prime_fifteenM_10710001 : Nat.Prime 10710001 := by norm_num
private theorem prime_fifteenM_35887916391298903 : Nat.Prime 35887916391298903 := by
  apply lucas_primality 35887916391298903 (3 : ZMod 35887916391298903)
  · rw [← fifteenMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 3), (7, 1), (8864759, 1), (10710001, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 3), (7, 1), (8864759, 1), (10710001, 1)] : List FactorBlock).map factorBlockValue).prod = 35887916391298903 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fifteenM_2
      · exact prime_fifteenM_3
      · exact prime_fifteenM_7
      · exact prime_fifteenM_8864759
      · exact prime_fifteenM_10710001
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 35887916391298903) ^ 17943958195649451 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (3 : ZMod 35887916391298903) ^ 11962638797099634 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (3 : ZMod 35887916391298903) ^ 5126845198756986 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (3 : ZMod 35887916391298903) ^ 4048380378 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (3 : ZMod 35887916391298903) ^ 3350878902 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide

private theorem prime_fifteenM_677 : Nat.Prime 677 := by norm_num
private theorem prime_fifteenM_6527627 : Nat.Prime 6527627 := by norm_num
private theorem prime_fifteenM_53951 : Nat.Prime 53951 := by norm_num
private theorem prime_fifteenM_70244203 : Nat.Prime 70244203 := by
  apply lucas_primality 70244203 (7 : ZMod 70244203)
  · rw [← fifteenMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (7, 1), (31, 1), (53951, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (7, 1), (31, 1), (53951, 1)] : List FactorBlock).map factorBlockValue).prod = 70244203 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fifteenM_2
      · exact prime_fifteenM_3
      · exact prime_fifteenM_7
      · exact prime_fifteenM_31
      · exact prime_fifteenM_53951
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 70244203) ^ 35122101 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (7 : ZMod 70244203) ^ 23414734 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (7 : ZMod 70244203) ^ 10034886 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (7 : ZMod 70244203) ^ 2265942 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (7 : ZMod 70244203) ^ 1302 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide

private theorem prime_fifteenM_5502335473155373 : Nat.Prime 5502335473155373 := by
  apply lucas_primality 5502335473155373 (5 : ZMod 5502335473155373)
  · rw [← fifteenMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (6527627, 1), (70244203, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (6527627, 1), (70244203, 1)] : List FactorBlock).map factorBlockValue).prod = 5502335473155373 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fifteenM_2
      · exact prime_fifteenM_3
      · exact prime_fifteenM_6527627
      · exact prime_fifteenM_70244203
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 5502335473155373) ^ 2751167736577686 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (5 : ZMod 5502335473155373) ^ 1834111824385124 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (5 : ZMod 5502335473155373) ^ 842930436 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (5 : ZMod 5502335473155373) ^ 78331524 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide

private theorem prime_fifteenM_14944343145089993069 : Nat.Prime 14944343145089993069 := by
  apply lucas_primality 14944343145089993069 (2 : ZMod 14944343145089993069)
  · rw [← fifteenMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (7, 1), (97, 1), (5502335473155373, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (7, 1), (97, 1), (5502335473155373, 1)] : List FactorBlock).map factorBlockValue).prod = 14944343145089993069 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fifteenM_2
      · exact prime_fifteenM_7
      · exact prime_fifteenM_97
      · exact prime_fifteenM_5502335473155373
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 14944343145089993069) ^ 7472171572544996534 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (2 : ZMod 14944343145089993069) ^ 2134906163584284724 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (2 : ZMod 14944343145089993069) ^ 154065393248350444 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (2 : ZMod 14944343145089993069) ^ 2716 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide

private theorem prime_fifteenM_46681 : Nat.Prime 46681 := by norm_num
private theorem prime_fifteenM_56297287 : Nat.Prime 56297287 := by
  apply lucas_primality 56297287 (3 : ZMod 56297287)
  · rw [← fifteenMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 2), (67, 1), (46681, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 2), (67, 1), (46681, 1)] : List FactorBlock).map factorBlockValue).prod = 56297287 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fifteenM_2
      · exact prime_fifteenM_3
      · exact prime_fifteenM_67
      · exact prime_fifteenM_46681
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 56297287) ^ 28148643 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (3 : ZMod 56297287) ^ 18765762 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (3 : ZMod 56297287) ^ 840258 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (3 : ZMod 56297287) ^ 1206 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide

private theorem prime_fifteenM_64144099 : Nat.Prime 64144099 := by
  apply lucas_primality 64144099 (2 : ZMod 64144099)
  · rw [← fifteenMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 2), (53, 1), (71, 1), (947, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 2), (53, 1), (71, 1), (947, 1)] : List FactorBlock).map factorBlockValue).prod = 64144099 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fifteenM_2
      · exact prime_fifteenM_3
      · exact prime_fifteenM_53
      · exact prime_fifteenM_71
      · exact prime_fifteenM_947
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 64144099) ^ 32072049 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (2 : ZMod 64144099) ^ 21381366 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (2 : ZMod 64144099) ^ 1210266 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (2 : ZMod 64144099) ^ 903438 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (2 : ZMod 64144099) ^ 67734 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide

private theorem prime_fifteenM_641057 : Nat.Prime 641057 := by norm_num
private theorem prime_fifteenM_659006597 : Nat.Prime 659006597 := by
  apply lucas_primality 659006597 (2 : ZMod 659006597)
  · rw [← fifteenMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (257, 1), (641057, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (257, 1), (641057, 1)] : List FactorBlock).map factorBlockValue).prod = 659006597 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fifteenM_2
      · exact prime_fifteenM_257
      · exact prime_fifteenM_641057
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 659006597) ^ 329503298 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (2 : ZMod 659006597) ^ 2564228 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (2 : ZMod 659006597) ^ 1028 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide

private theorem prime_fifteenM_71172712477 : Nat.Prime 71172712477 := by
  apply lucas_primality 71172712477 (2 : ZMod 71172712477)
  · rw [← fifteenMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 3), (659006597, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 3), (659006597, 1)] : List FactorBlock).map factorBlockValue).prod = 71172712477 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fifteenM_2
      · exact prime_fifteenM_3
      · exact prime_fifteenM_659006597
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 71172712477) ^ 35586356238 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (2 : ZMod 71172712477) ^ 23724237492 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (2 : ZMod 71172712477) ^ 108 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide

private theorem prime_fifteenM_339389 : Nat.Prime 339389 := by norm_num
private theorem prime_fifteenM_545911 : Nat.Prime 545911 := by norm_num
private theorem prime_fifteenM_2940799 : Nat.Prime 2940799 := by norm_num
private theorem prime_fifteenM_1723 : Nat.Prime 1723 := by norm_num
private theorem prime_fifteenM_464968781 : Nat.Prime 464968781 := by
  apply lucas_primality 464968781 (2 : ZMod 464968781)
  · rw [← fifteenMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (5, 1), (103, 1), (131, 1), (1723, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (5, 1), (103, 1), (131, 1), (1723, 1)] : List FactorBlock).map factorBlockValue).prod = 464968781 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fifteenM_2
      · exact prime_fifteenM_5
      · exact prime_fifteenM_103
      · exact prime_fifteenM_131
      · exact prime_fifteenM_1723
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 464968781) ^ 232484390 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (2 : ZMod 464968781) ^ 92993756 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (2 : ZMod 464968781) ^ 4514260 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (2 : ZMod 464968781) ^ 3549380 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (2 : ZMod 464968781) ^ 269860 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide

private theorem prime_fifteenM_120431 : Nat.Prime 120431 := by norm_num
private theorem prime_fifteenM_1243088783 : Nat.Prime 1243088783 := by
  apply lucas_primality 1243088783 (5 : ZMod 1243088783)
  · rw [← fifteenMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (13, 1), (397, 1), (120431, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (13, 1), (397, 1), (120431, 1)] : List FactorBlock).map factorBlockValue).prod = 1243088783 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fifteenM_2
      · exact prime_fifteenM_13
      · exact prime_fifteenM_397
      · exact prime_fifteenM_120431
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 1243088783) ^ 621544391 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (5 : ZMod 1243088783) ^ 95622214 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (5 : ZMod 1243088783) ^ 3131206 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (5 : ZMod 1243088783) ^ 10322 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide

private theorem prime_fifteenM_1951 : Nat.Prime 1951 := by norm_num
private theorem prime_fifteenM_5285201 : Nat.Prime 5285201 := by norm_num
private theorem prime_fifteenM_2742839622167 : Nat.Prime 2742839622167 := by
  apply lucas_primality 2742839622167 (5 : ZMod 2742839622167)
  · rw [← fifteenMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (7, 1), (19, 1), (1951, 1), (5285201, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (7, 1), (19, 1), (1951, 1), (5285201, 1)] : List FactorBlock).map factorBlockValue).prod = 2742839622167 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fifteenM_2
      · exact prime_fifteenM_7
      · exact prime_fifteenM_19
      · exact prime_fifteenM_1951
      · exact prime_fifteenM_5285201
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 2742839622167) ^ 1371419811083 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (5 : ZMod 2742839622167) ^ 391834231738 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (5 : ZMod 2742839622167) ^ 144359980114 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (5 : ZMod 2742839622167) ^ 1405863466 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (5 : ZMod 2742839622167) ^ 518966 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide

private theorem prime_fifteenM_14266079385531977737 : Nat.Prime 14266079385531977737 := by
  apply lucas_primality 14266079385531977737 (13 : ZMod 14266079385531977737)
  · rw [← fifteenMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (3, 2), (29, 1), (47, 1), (53, 1), (2742839622167, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (3, 2), (29, 1), (47, 1), (53, 1), (2742839622167, 1)] : List FactorBlock).map factorBlockValue).prod = 14266079385531977737 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fifteenM_2
      · exact prime_fifteenM_3
      · exact prime_fifteenM_29
      · exact prime_fifteenM_47
      · exact prime_fifteenM_53
      · exact prime_fifteenM_2742839622167
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 14266079385531977737) ^ 7133039692765988868 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (13 : ZMod 14266079385531977737) ^ 4755359795177325912 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (13 : ZMod 14266079385531977737) ^ 491933771914895784 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (13 : ZMod 14266079385531977737) ^ 303533603947488888 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (13 : ZMod 14266079385531977737) ^ 269171309160980712 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (13 : ZMod 14266079385531977737) ^ 5201208 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide

private theorem prime_fifteenM_246305600854754639064867001 : Nat.Prime 246305600854754639064867001 := by
  apply lucas_primality 246305600854754639064867001 (103 : ZMod 246305600854754639064867001)
  · rw [← fifteenMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (3, 2), (5, 3), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (3, 2), (5, 3), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod = 246305600854754639064867001 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fifteenM_2
      · exact prime_fifteenM_3
      · exact prime_fifteenM_5
      · exact prime_fifteenM_7
      · exact prime_fifteenM_11
      · exact prime_fifteenM_13
      · exact prime_fifteenM_17
      · exact prime_fifteenM_19
      · exact prime_fifteenM_23
      · exact prime_fifteenM_29
      · exact prime_fifteenM_31
      · exact prime_fifteenM_37
      · exact prime_fifteenM_41
      · exact prime_fifteenM_43
      · exact prime_fifteenM_47
      · exact prime_fifteenM_53
      · exact prime_fifteenM_59
      · exact prime_fifteenM_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (103 : ZMod 246305600854754639064867001) ^ 123152800427377319532433500 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (103 : ZMod 246305600854754639064867001) ^ 82101866951584879688289000 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (103 : ZMod 246305600854754639064867001) ^ 49261120170950927812973400 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (103 : ZMod 246305600854754639064867001) ^ 35186514407822091294981000 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (103 : ZMod 246305600854754639064867001) ^ 22391418259523149005897000 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (103 : ZMod 246305600854754639064867001) ^ 18946584681134972235759000 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (103 : ZMod 246305600854754639064867001) ^ 14488564756162037592051000 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (103 : ZMod 246305600854754639064867001) ^ 12963452676566033634993000 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (103 : ZMod 246305600854754639064867001) ^ 10708939167598027785429000 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (103 : ZMod 246305600854754639064867001) ^ 8493296581198435829823000 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (103 : ZMod 246305600854754639064867001) ^ 7945341963056601260157000 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (103 : ZMod 246305600854754639064867001) ^ 6656908131209584839591000 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (103 : ZMod 246305600854754639064867001) ^ 6007453679384259489387000 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (103 : ZMod 246305600854754639064867001) ^ 5728037229180340443369000 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (103 : ZMod 246305600854754639064867001) ^ 5240544699037332746061000 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (103 : ZMod 246305600854754639064867001) ^ 4647275487825559227639000 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (103 : ZMod 246305600854754639064867001) ^ 4174671200928044729913000 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (103 : ZMod 246305600854754639064867001) ^ 4037796735323846542047000 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide

private theorem prime_fifteenM_17734003261542334012670424073 : Nat.Prime 17734003261542334012670424073 := by
  apply lucas_primality 17734003261542334012670424073 (5 : ZMod 17734003261542334012670424073)
  · rw [← fifteenMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (3, 2), (246305600854754639064867001, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (3, 2), (246305600854754639064867001, 1)] : List FactorBlock).map factorBlockValue).prod = 17734003261542334012670424073 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fifteenM_2
      · exact prime_fifteenM_3
      · exact prime_fifteenM_246305600854754639064867001
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 17734003261542334012670424073) ^ 8867001630771167006335212036 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (5 : ZMod 17734003261542334012670424073) ^ 5911334420514111337556808024 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (5 : ZMod 17734003261542334012670424073) ^ 72 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide

private theorem prime_fifteenM_2473 : Nat.Prime 2473 := by norm_num
private theorem prime_fifteenM_50971 : Nat.Prime 50971 := by norm_num
private theorem prime_fifteenM_34213 : Nat.Prime 34213 := by norm_num
private theorem prime_fifteenM_141025987 : Nat.Prime 141025987 := by
  apply lucas_primality 141025987 (2 : ZMod 141025987)
  · rw [← fifteenMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 2), (229, 1), (34213, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 2), (229, 1), (34213, 1)] : List FactorBlock).map factorBlockValue).prod = 141025987 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fifteenM_2
      · exact prime_fifteenM_3
      · exact prime_fifteenM_229
      · exact prime_fifteenM_34213
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 141025987) ^ 70512993 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (2 : ZMod 141025987) ^ 47008662 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (2 : ZMod 141025987) ^ 615834 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (2 : ZMod 141025987) ^ 4122 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide

private theorem prime_fifteenM_984079337287 : Nat.Prime 984079337287 := by
  apply lucas_primality 984079337287 (3 : ZMod 984079337287)
  · rw [← fifteenMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (1163, 1), (141025987, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (1163, 1), (141025987, 1)] : List FactorBlock).map factorBlockValue).prod = 984079337287 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fifteenM_2
      · exact prime_fifteenM_3
      · exact prime_fifteenM_1163
      · exact prime_fifteenM_141025987
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 984079337287) ^ 492039668643 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (3 : ZMod 984079337287) ^ 328026445762 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (3 : ZMod 984079337287) ^ 846155922 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (3 : ZMod 984079337287) ^ 6978 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide

private theorem prime_fifteenM_1901199948306317947 : Nat.Prime 1901199948306317947 := by
  apply lucas_primality 1901199948306317947 (5 : ZMod 1901199948306317947)
  · rw [← fifteenMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 3), (7, 1), (19, 1), (269, 1), (984079337287, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 3), (7, 1), (19, 1), (269, 1), (984079337287, 1)] : List FactorBlock).map factorBlockValue).prod = 1901199948306317947 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fifteenM_2
      · exact prime_fifteenM_3
      · exact prime_fifteenM_7
      · exact prime_fifteenM_19
      · exact prime_fifteenM_269
      · exact prime_fifteenM_984079337287
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 1901199948306317947) ^ 950599974153158973 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (5 : ZMod 1901199948306317947) ^ 633733316102105982 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (5 : ZMod 1901199948306317947) ^ 271599992615188278 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (5 : ZMod 1901199948306317947) ^ 100063155174016734 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (5 : ZMod 1901199948306317947) ^ 7067657800395234 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (5 : ZMod 1901199948306317947) ^ 1931958 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide

private theorem prime_fifteenM_1355153 : Nat.Prime 1355153 := by norm_num
private theorem prime_fifteenM_626080687 : Nat.Prime 626080687 := by
  apply lucas_primality 626080687 (5 : ZMod 626080687)
  · rw [← fifteenMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (7, 1), (11, 1), (1355153, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (7, 1), (11, 1), (1355153, 1)] : List FactorBlock).map factorBlockValue).prod = 626080687 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fifteenM_2
      · exact prime_fifteenM_3
      · exact prime_fifteenM_7
      · exact prime_fifteenM_11
      · exact prime_fifteenM_1355153
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 626080687) ^ 313040343 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (5 : ZMod 626080687) ^ 208693562 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (5 : ZMod 626080687) ^ 89440098 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (5 : ZMod 626080687) ^ 56916426 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (5 : ZMod 626080687) ^ 462 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide

private theorem prime_fifteenM_5037757 : Nat.Prime 5037757 := by norm_num
private theorem prime_fifteenM_14751743 : Nat.Prime 14751743 := by norm_num
private theorem prime_fifteenM_377672369920211983 : Nat.Prime 377672369920211983 := by
  apply lucas_primality 377672369920211983 (3 : ZMod 377672369920211983)
  · rw [← fifteenMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (7, 1), (11, 2), (5037757, 1), (14751743, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (7, 1), (11, 2), (5037757, 1), (14751743, 1)] : List FactorBlock).map factorBlockValue).prod = 377672369920211983 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fifteenM_2
      · exact prime_fifteenM_3
      · exact prime_fifteenM_7
      · exact prime_fifteenM_11
      · exact prime_fifteenM_5037757
      · exact prime_fifteenM_14751743
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 377672369920211983) ^ 188836184960105991 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (3 : ZMod 377672369920211983) ^ 125890789973403994 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (3 : ZMod 377672369920211983) ^ 53953195702887426 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (3 : ZMod 377672369920211983) ^ 34333851810928362 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (3 : ZMod 377672369920211983) ^ 74968357926 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (3 : ZMod 377672369920211983) ^ 25601881074 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide

private theorem prime_fifteenM_1327 : Nat.Prime 1327 := by norm_num
private theorem prime_fifteenM_95651 : Nat.Prime 95651 := by norm_num
private theorem prime_fifteenM_19869803 : Nat.Prime 19869803 := by norm_num
private theorem prime_fifteenM_991 : Nat.Prime 991 := by norm_num
private theorem prime_fifteenM_69774329 : Nat.Prime 69774329 := by
  apply lucas_primality 69774329 (3 : ZMod 69774329)
  · rw [← fifteenMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (13, 1), (677, 1), (991, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (13, 1), (677, 1), (991, 1)] : List FactorBlock).map factorBlockValue).prod = 69774329 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fifteenM_2
      · exact prime_fifteenM_13
      · exact prime_fifteenM_677
      · exact prime_fifteenM_991
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 69774329) ^ 34887164 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (3 : ZMod 69774329) ^ 5367256 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (3 : ZMod 69774329) ^ 103064 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (3 : ZMod 69774329) ^ 70408 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide

private theorem prime_fifteenM_175841859968491790075263 : Nat.Prime 175841859968491790075263 := by
  apply lucas_primality 175841859968491790075263 (7 : ZMod 175841859968491790075263)
  · rw [← fifteenMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (13, 1), (17, 1), (95651, 1), (19869803, 1), (69774329, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (13, 1), (17, 1), (95651, 1), (19869803, 1), (69774329, 1)] : List FactorBlock).map factorBlockValue).prod = 175841859968491790075263 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fifteenM_2
      · exact prime_fifteenM_3
      · exact prime_fifteenM_13
      · exact prime_fifteenM_17
      · exact prime_fifteenM_95651
      · exact prime_fifteenM_19869803
      · exact prime_fifteenM_69774329
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 175841859968491790075263) ^ 87920929984245895037631 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (7 : ZMod 175841859968491790075263) ^ 58613953322830596691754 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (7 : ZMod 175841859968491790075263) ^ 13526296920653214621174 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (7 : ZMod 175841859968491790075263) ^ 10343638821675987651486 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (7 : ZMod 175841859968491790075263) ^ 1838369279657209962 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (7 : ZMod 175841859968491790075263) ^ 8849703239055354 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (7 : ZMod 175841859968491790075263) ^ 2520151214474478 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide

private theorem prime_fifteenM_1091 : Nat.Prime 1091 := by norm_num
private theorem prime_fifteenM_271 : Nat.Prime 271 := by norm_num
private theorem prime_fifteenM_881 : Nat.Prime 881 := by norm_num
private theorem prime_fifteenM_25523 : Nat.Prime 25523 := by norm_num
private theorem prime_fifteenM_8117 : Nat.Prime 8117 := by norm_num
private theorem prime_fifteenM_21477583 : Nat.Prime 21477583 := by
  apply lucas_primality 21477583 (5 : ZMod 21477583)
  · rw [← fifteenMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 3), (7, 2), (8117, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 3), (7, 2), (8117, 1)] : List FactorBlock).map factorBlockValue).prod = 21477583 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fifteenM_2
      · exact prime_fifteenM_3
      · exact prime_fifteenM_7
      · exact prime_fifteenM_8117
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 21477583) ^ 10738791 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (5 : ZMod 21477583) ^ 7159194 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (5 : ZMod 21477583) ^ 3068226 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (5 : ZMod 21477583) ^ 2646 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide

private theorem prime_fifteenM_33633894979 : Nat.Prime 33633894979 := by
  apply lucas_primality 33633894979 (2 : ZMod 33633894979)
  · rw [← fifteenMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 3), (29, 1), (21477583, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 3), (29, 1), (21477583, 1)] : List FactorBlock).map factorBlockValue).prod = 33633894979 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fifteenM_2
      · exact prime_fifteenM_3
      · exact prime_fifteenM_29
      · exact prime_fifteenM_21477583
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 33633894979) ^ 16816947489 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (2 : ZMod 33633894979) ^ 11211298326 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (2 : ZMod 33633894979) ^ 1159789482 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (2 : ZMod 33633894979) ^ 1566 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide

private theorem prime_fifteenM_211101494655711238500011 : Nat.Prime 211101494655711238500011 := by
  apply lucas_primality 211101494655711238500011 (2 : ZMod 211101494655711238500011)
  · rw [← fifteenMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 1), (103, 1), (271, 1), (881, 1), (25523, 1), (33633894979, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 1), (103, 1), (271, 1), (881, 1), (25523, 1), (33633894979, 1)] : List FactorBlock).map factorBlockValue).prod = 211101494655711238500011 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fifteenM_2
      · exact prime_fifteenM_5
      · exact prime_fifteenM_103
      · exact prime_fifteenM_271
      · exact prime_fifteenM_881
      · exact prime_fifteenM_25523
      · exact prime_fifteenM_33633894979
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 211101494655711238500011) ^ 105550747327855619250005 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (2 : ZMod 211101494655711238500011) ^ 42220298931142247700002 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (2 : ZMod 211101494655711238500011) ^ 2049529074327293577670 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (2 : ZMod 211101494655711238500011) ^ 778972305002624496310 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (2 : ZMod 211101494655711238500011) ^ 239615771459377115210 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (2 : ZMod 211101494655711238500011) ^ 8271029841935165870 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (2 : ZMod 211101494655711238500011) ^ 6276451026190 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide

private theorem prime_fifteenM_577 : Nat.Prime 577 := by norm_num
private theorem prime_fifteenM_685493 : Nat.Prime 685493 := by norm_num
private theorem prime_fifteenM_24522826583 : Nat.Prime 24522826583 := by
  apply lucas_primality 24522826583 (5 : ZMod 24522826583)
  · rw [← fifteenMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (31, 1), (577, 1), (685493, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (31, 1), (577, 1), (685493, 1)] : List FactorBlock).map factorBlockValue).prod = 24522826583 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fifteenM_2
      · exact prime_fifteenM_31
      · exact prime_fifteenM_577
      · exact prime_fifteenM_685493
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 24522826583) ^ 12261413291 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (5 : ZMod 24522826583) ^ 791058922 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (5 : ZMod 24522826583) ^ 42500566 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (5 : ZMod 24522826583) ^ 35774 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide

private theorem prime_fifteenM_2153 : Nat.Prime 2153 := by norm_num
private theorem prime_fifteenM_52579 : Nat.Prime 52579 := by norm_num
private theorem prime_fifteenM_518323783 : Nat.Prime 518323783 := by
  apply lucas_primality 518323783 (5 : ZMod 518323783)
  · rw [← fifteenMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (31, 1), (53, 1), (52579, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (31, 1), (53, 1), (52579, 1)] : List FactorBlock).map factorBlockValue).prod = 518323783 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fifteenM_2
      · exact prime_fifteenM_3
      · exact prime_fifteenM_31
      · exact prime_fifteenM_53
      · exact prime_fifteenM_52579
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 518323783) ^ 259161891 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (5 : ZMod 518323783) ^ 172774594 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (5 : ZMod 518323783) ^ 16720122 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (5 : ZMod 518323783) ^ 9779694 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (5 : ZMod 518323783) ^ 9858 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide

private theorem prime_fifteenM_2231902209599 : Nat.Prime 2231902209599 := by
  apply lucas_primality 2231902209599 (19 : ZMod 2231902209599)
  · rw [← fifteenMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (2153, 1), (518323783, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (2153, 1), (518323783, 1)] : List FactorBlock).map factorBlockValue).prod = 2231902209599 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fifteenM_2
      · exact prime_fifteenM_2153
      · exact prime_fifteenM_518323783
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (19 : ZMod 2231902209599) ^ 1115951104799 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (19 : ZMod 2231902209599) ^ 1036647566 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (19 : ZMod 2231902209599) ^ 4306 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide

private theorem prime_fifteenM_9271321778674247 : Nat.Prime 9271321778674247 := by
  apply lucas_primality 9271321778674247 (5 : ZMod 9271321778674247)
  · rw [← fifteenMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (31, 1), (67, 1), (2231902209599, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (31, 1), (67, 1), (2231902209599, 1)] : List FactorBlock).map factorBlockValue).prod = 9271321778674247 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fifteenM_2
      · exact prime_fifteenM_31
      · exact prime_fifteenM_67
      · exact prime_fifteenM_2231902209599
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 9271321778674247) ^ 4635660889337123 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (5 : ZMod 9271321778674247) ^ 299074896086266 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (5 : ZMod 9271321778674247) ^ 138377936995138 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (5 : ZMod 9271321778674247) ^ 4154 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide

private theorem prime_fifteenM_1733 : Nat.Prime 1733 := by norm_num
private theorem prime_fifteenM_138917 : Nat.Prime 138917 := by norm_num
private theorem prime_fifteenM_469543 : Nat.Prime 469543 := by norm_num
private theorem prime_fifteenM_92867 : Nat.Prime 92867 := by norm_num
private theorem prime_fifteenM_264113749 : Nat.Prime 264113749 := by
  apply lucas_primality 264113749 (2 : ZMod 264113749)
  · rw [← fifteenMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 2), (79, 1), (92867, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 2), (79, 1), (92867, 1)] : List FactorBlock).map factorBlockValue).prod = 264113749 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fifteenM_2
      · exact prime_fifteenM_3
      · exact prime_fifteenM_79
      · exact prime_fifteenM_92867
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 264113749) ^ 132056874 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (2 : ZMod 264113749) ^ 88037916 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (2 : ZMod 264113749) ^ 3343212 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (2 : ZMod 264113749) ^ 2844 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide

private theorem prime_fifteenM_4754047483 : Nat.Prime 4754047483 := by
  apply lucas_primality 4754047483 (2 : ZMod 4754047483)
  · rw [← fifteenMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 2), (264113749, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 2), (264113749, 1)] : List FactorBlock).map factorBlockValue).prod = 4754047483 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fifteenM_2
      · exact prime_fifteenM_3
      · exact prime_fifteenM_264113749
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 4754047483) ^ 2377023741 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (2 : ZMod 4754047483) ^ 1584682494 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (2 : ZMod 4754047483) ^ 18 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide

private theorem prime_fifteenM_104589044627 : Nat.Prime 104589044627 := by
  apply lucas_primality 104589044627 (6 : ZMod 104589044627)
  · rw [← fifteenMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (11, 1), (4754047483, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (11, 1), (4754047483, 1)] : List FactorBlock).map factorBlockValue).prod = 104589044627 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fifteenM_2
      · exact prime_fifteenM_11
      · exact prime_fifteenM_4754047483
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (6 : ZMod 104589044627) ^ 52294522313 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (6 : ZMod 104589044627) ^ 9508094966 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (6 : ZMod 104589044627) ^ 22 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide

private theorem prime_fifteenM_78441783470251 : Nat.Prime 78441783470251 := by
  apply lucas_primality 78441783470251 (2 : ZMod 78441783470251)
  · rw [← fifteenMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (5, 3), (104589044627, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (5, 3), (104589044627, 1)] : List FactorBlock).map factorBlockValue).prod = 78441783470251 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fifteenM_2
      · exact prime_fifteenM_3
      · exact prime_fifteenM_5
      · exact prime_fifteenM_104589044627
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 78441783470251) ^ 39220891735125 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (2 : ZMod 78441783470251) ^ 26147261156750 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (2 : ZMod 78441783470251) ^ 15688356694050 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (2 : ZMod 78441783470251) ^ 750 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide

private theorem prime_fifteenM_10233123636204462788615363 : Nat.Prime 10233123636204462788615363 := by
  apply lucas_primality 10233123636204462788615363 (2 : ZMod 10233123636204462788615363)
  · rw [← fifteenMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (138917, 1), (469543, 1), (78441783470251, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (138917, 1), (469543, 1), (78441783470251, 1)] : List FactorBlock).map factorBlockValue).prod = 10233123636204462788615363 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fifteenM_2
      · exact prime_fifteenM_138917
      · exact prime_fifteenM_469543
      · exact prime_fifteenM_78441783470251
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 10233123636204462788615363) ^ 5116561818102231394307681 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (2 : ZMod 10233123636204462788615363) ^ 73663580671944130586 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (2 : ZMod 10233123636204462788615363) ^ 21793794468673716334 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (2 : ZMod 10233123636204462788615363) ^ 130455009862 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide

private theorem prime_fifteenM_152441 : Nat.Prime 152441 := by norm_num
private theorem prime_fifteenM_82529 : Nat.Prime 82529 := by norm_num
private theorem prime_fifteenM_1244879 : Nat.Prime 1244879 := by norm_num
private theorem prime_fifteenM_27238268144131903 : Nat.Prime 27238268144131903 := by
  apply lucas_primality 27238268144131903 (3 : ZMod 27238268144131903)
  · rw [← fifteenMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 2), (11, 1), (13, 1), (103, 1), (82529, 1), (1244879, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 2), (11, 1), (13, 1), (103, 1), (82529, 1), (1244879, 1)] : List FactorBlock).map factorBlockValue).prod = 27238268144131903 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fifteenM_2
      · exact prime_fifteenM_3
      · exact prime_fifteenM_11
      · exact prime_fifteenM_13
      · exact prime_fifteenM_103
      · exact prime_fifteenM_82529
      · exact prime_fifteenM_1244879
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 27238268144131903) ^ 13619134072065951 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (3 : ZMod 27238268144131903) ^ 9079422714710634 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (3 : ZMod 27238268144131903) ^ 2476206194921082 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (3 : ZMod 27238268144131903) ^ 2095251395702454 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (3 : ZMod 27238268144131903) ^ 264449205282834 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (3 : ZMod 27238268144131903) ^ 330044810238 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (3 : ZMod 27238268144131903) ^ 21880253538 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide

private theorem prime_fifteenM_73819 : Nat.Prime 73819 := by norm_num
private theorem prime_fifteenM_344873 : Nat.Prime 344873 := by norm_num
private theorem prime_fifteenM_47659 : Nat.Prime 47659 := by norm_num
private theorem prime_fifteenM_197212943 : Nat.Prime 197212943 := by
  apply lucas_primality 197212943 (5 : ZMod 197212943)
  · rw [← fifteenMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (2069, 1), (47659, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (2069, 1), (47659, 1)] : List FactorBlock).map factorBlockValue).prod = 197212943 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fifteenM_2
      · exact prime_fifteenM_2069
      · exact prime_fifteenM_47659
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 197212943) ^ 98606471 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (5 : ZMod 197212943) ^ 95318 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (5 : ZMod 197212943) ^ 4138 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide

private theorem prime_fifteenM_953929693745394630791 : Nat.Prime 953929693745394630791 := by
  apply lucas_primality 953929693745394630791 (7 : ZMod 953929693745394630791)
  · rw [← fifteenMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 1), (19, 1), (73819, 1), (344873, 1), (197212943, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 1), (19, 1), (73819, 1), (344873, 1), (197212943, 1)] : List FactorBlock).map factorBlockValue).prod = 953929693745394630791 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fifteenM_2
      · exact prime_fifteenM_5
      · exact prime_fifteenM_19
      · exact prime_fifteenM_73819
      · exact prime_fifteenM_344873
      · exact prime_fifteenM_197212943
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 953929693745394630791) ^ 476964846872697315395 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (7 : ZMod 953929693745394630791) ^ 190785938749078926158 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (7 : ZMod 953929693745394630791) ^ 50206825986599717410 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (7 : ZMod 953929693745394630791) ^ 12922549665335410 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (7 : ZMod 953929693745394630791) ^ 2766031825470230 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (7 : ZMod 953929693745394630791) ^ 4837054197530 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide

private theorem prime_fifteenM_36489718645148835417017333 : Nat.Prime 36489718645148835417017333 := by
  apply lucas_primality 36489718645148835417017333 (2 : ZMod 36489718645148835417017333)
  · rw [← fifteenMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (73, 1), (131, 1), (953929693745394630791, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (73, 1), (131, 1), (953929693745394630791, 1)] : List FactorBlock).map factorBlockValue).prod = 36489718645148835417017333 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fifteenM_2
      · exact prime_fifteenM_73
      · exact prime_fifteenM_131
      · exact prime_fifteenM_953929693745394630791
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 36489718645148835417017333) ^ 18244859322574417708508666 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (2 : ZMod 36489718645148835417017333) ^ 499859159522586786534484 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (2 : ZMod 36489718645148835417017333) ^ 278547470573655232190972 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (2 : ZMod 36489718645148835417017333) ^ 38252 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide

private theorem prime_fifteenM_72979437290297670834034667 : Nat.Prime 72979437290297670834034667 := by
  apply lucas_primality 72979437290297670834034667 (2 : ZMod 72979437290297670834034667)
  · rw [← fifteenMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (36489718645148835417017333, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (36489718645148835417017333, 1)] : List FactorBlock).map factorBlockValue).prod = 72979437290297670834034667 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_fifteenM_2
      · exact prime_fifteenM_36489718645148835417017333
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 72979437290297670834034667) ^ 36489718645148835417017333 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (2 : ZMod 72979437290297670834034667) ^ 2 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide

private theorem prime_fifteenM_148667 : Nat.Prime 148667 := by norm_num
private theorem prime_fifteenM_158909 : Nat.Prime 158909 := by norm_num
private theorem prime_fifteenM_169837 : Nat.Prime 169837 := by norm_num
private theorem prime_fifteenM_68953823 : Nat.Prime 68953823 := by
  apply lucas_primality 68953823 (5 : ZMod 68953823)
  · rw [← fifteenMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (7, 1), (29, 1), (169837, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (7, 1), (29, 1), (169837, 1)] : List FactorBlock).map factorBlockValue).prod = 68953823 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fifteenM_2
      · exact prime_fifteenM_7
      · exact prime_fifteenM_29
      · exact prime_fifteenM_169837
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 68953823) ^ 34476911 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (5 : ZMod 68953823) ^ 9850546 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (5 : ZMod 68953823) ^ 2377718 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (5 : ZMod 68953823) ^ 406 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide

private theorem prime_fifteenM_720705357997 : Nat.Prime 720705357997 := by
  apply lucas_primality 720705357997 (6 : ZMod 720705357997)
  · rw [← fifteenMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (13, 1), (67, 1), (68953823, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (13, 1), (67, 1), (68953823, 1)] : List FactorBlock).map factorBlockValue).prod = 720705357997 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fifteenM_2
      · exact prime_fifteenM_3
      · exact prime_fifteenM_13
      · exact prime_fifteenM_67
      · exact prime_fifteenM_68953823
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 720705357997) ^ 360352678998 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (6 : ZMod 720705357997) ^ 240235119332 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (6 : ZMod 720705357997) ^ 55438873692 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (6 : ZMod 720705357997) ^ 10756796388 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (6 : ZMod 720705357997) ^ 10452 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide

private theorem prime_fifteenM_125402732291479 : Nat.Prime 125402732291479 := by
  apply lucas_primality 125402732291479 (6 : ZMod 125402732291479)
  · rw [← fifteenMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (29, 1), (720705357997, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (29, 1), (720705357997, 1)] : List FactorBlock).map factorBlockValue).prod = 125402732291479 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fifteenM_2
      · exact prime_fifteenM_3
      · exact prime_fifteenM_29
      · exact prime_fifteenM_720705357997
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 125402732291479) ^ 62701366145739 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (6 : ZMod 125402732291479) ^ 41800910763826 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (6 : ZMod 125402732291479) ^ 4324232147982 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (6 : ZMod 125402732291479) ^ 174 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide

private theorem prime_fifteenM_50993 : Nat.Prime 50993 := by norm_num
private theorem prime_fifteenM_288314423 : Nat.Prime 288314423 := by
  apply lucas_primality 288314423 (5 : ZMod 288314423)
  · rw [← fifteenMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (11, 1), (257, 1), (50993, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (11, 1), (257, 1), (50993, 1)] : List FactorBlock).map factorBlockValue).prod = 288314423 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fifteenM_2
      · exact prime_fifteenM_11
      · exact prime_fifteenM_257
      · exact prime_fifteenM_50993
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 288314423) ^ 144157211 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (5 : ZMod 288314423) ^ 26210402 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (5 : ZMod 288314423) ^ 1121846 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (5 : ZMod 288314423) ^ 5654 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide

private theorem prime_fifteenM_1019 : Nat.Prime 1019 := by norm_num
private theorem prime_fifteenM_3511 : Nat.Prime 3511 := by norm_num
private theorem prime_fifteenM_10663 : Nat.Prime 10663 := by norm_num
private theorem prime_fifteenM_20327 : Nat.Prime 20327 := by norm_num
private theorem prime_fifteenM_286539270923 : Nat.Prime 286539270923 := by
  apply lucas_primality 286539270923 (2 : ZMod 286539270923)
  · rw [← fifteenMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (661, 1), (10663, 1), (20327, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (661, 1), (10663, 1), (20327, 1)] : List FactorBlock).map factorBlockValue).prod = 286539270923 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fifteenM_2
      · exact prime_fifteenM_661
      · exact prime_fifteenM_10663
      · exact prime_fifteenM_20327
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 286539270923) ^ 143269635461 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (2 : ZMod 286539270923) ^ 433493602 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (2 : ZMod 286539270923) ^ 26872294 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (2 : ZMod 286539270923) ^ 14096486 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide

private theorem prime_fifteenM_61509247706079324421 : Nat.Prime 61509247706079324421 := by
  apply lucas_primality 61509247706079324421 (2 : ZMod 61509247706079324421)
  · rw [← fifteenMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (5, 1), (1019, 1), (3511, 1), (286539270923, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (5, 1), (1019, 1), (3511, 1), (286539270923, 1)] : List FactorBlock).map factorBlockValue).prod = 61509247706079324421 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fifteenM_2
      · exact prime_fifteenM_3
      · exact prime_fifteenM_5
      · exact prime_fifteenM_1019
      · exact prime_fifteenM_3511
      · exact prime_fifteenM_286539270923
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 61509247706079324421) ^ 30754623853039662210 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (2 : ZMod 61509247706079324421) ^ 20503082568693108140 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (2 : ZMod 61509247706079324421) ^ 12301849541215864884 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (2 : ZMod 61509247706079324421) ^ 60362362812639180 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (2 : ZMod 61509247706079324421) ^ 17519011024232220 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (2 : ZMod 61509247706079324421) ^ 214662540 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide

private theorem prime_fifteenM_701 : Nat.Prime 701 := by norm_num
private theorem prime_fifteenM_266957 : Nat.Prime 266957 := by norm_num
private theorem prime_fifteenM_53813 : Nat.Prime 53813 := by norm_num
private theorem prime_fifteenM_359147963 : Nat.Prime 359147963 := by
  apply lucas_primality 359147963 (2 : ZMod 359147963)
  · rw [← fifteenMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (47, 1), (71, 1), (53813, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (47, 1), (71, 1), (53813, 1)] : List FactorBlock).map factorBlockValue).prod = 359147963 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fifteenM_2
      · exact prime_fifteenM_47
      · exact prime_fifteenM_71
      · exact prime_fifteenM_53813
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 359147963) ^ 179573981 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (2 : ZMod 359147963) ^ 7641446 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (2 : ZMod 359147963) ^ 5058422 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (2 : ZMod 359147963) ^ 6674 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide

private theorem prime_fifteenM_955333581581 : Nat.Prime 955333581581 := by
  apply lucas_primality 955333581581 (10 : ZMod 955333581581)
  · rw [← fifteenMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (5, 1), (7, 1), (19, 1), (359147963, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (5, 1), (7, 1), (19, 1), (359147963, 1)] : List FactorBlock).map factorBlockValue).prod = 955333581581 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fifteenM_2
      · exact prime_fifteenM_5
      · exact prime_fifteenM_7
      · exact prime_fifteenM_19
      · exact prime_fifteenM_359147963
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 955333581581) ^ 477666790790 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (10 : ZMod 955333581581) ^ 191066716316 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (10 : ZMod 955333581581) ^ 136476225940 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (10 : ZMod 955333581581) ^ 50280714820 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (10 : ZMod 955333581581) ^ 2660 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide

private theorem prime_fifteenM_301168454275224747175301 : Nat.Prime 301168454275224747175301 := by
  apply lucas_primality 301168454275224747175301 (3 : ZMod 301168454275224747175301)
  · rw [← fifteenMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (5, 2), (7, 2), (241, 1), (266957, 1), (955333581581, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (5, 2), (7, 2), (241, 1), (266957, 1), (955333581581, 1)] : List FactorBlock).map factorBlockValue).prod = 301168454275224747175301 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fifteenM_2
      · exact prime_fifteenM_5
      · exact prime_fifteenM_7
      · exact prime_fifteenM_241
      · exact prime_fifteenM_266957
      · exact prime_fifteenM_955333581581
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 301168454275224747175301) ^ 150584227137612373587650 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (3 : ZMod 301168454275224747175301) ^ 60233690855044949435060 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (3 : ZMod 301168454275224747175301) ^ 43024064896460678167900 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (3 : ZMod 301168454275224747175301) ^ 1249661635996783183300 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (3 : ZMod 301168454275224747175301) ^ 1128153426489002900 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (3 : ZMod 301168454275224747175301) ^ 315249521300 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide

private theorem prime_fifteenM_208635332488733341325534401 : Nat.Prime 208635332488733341325534401 := by
  apply lucas_primality 208635332488733341325534401 (79 : ZMod 208635332488733341325534401)
  · rw [← fifteenMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 6), (3, 4), (5, 2), (7, 2), (11, 1), (13, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 6), (3, 4), (5, 2), (7, 2), (11, 1), (13, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod = 208635332488733341325534401 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fifteenM_2
      · exact prime_fifteenM_3
      · exact prime_fifteenM_5
      · exact prime_fifteenM_7
      · exact prime_fifteenM_11
      · exact prime_fifteenM_13
      · exact prime_fifteenM_19
      · exact prime_fifteenM_23
      · exact prime_fifteenM_29
      · exact prime_fifteenM_31
      · exact prime_fifteenM_37
      · exact prime_fifteenM_41
      · exact prime_fifteenM_43
      · exact prime_fifteenM_47
      · exact prime_fifteenM_53
      · exact prime_fifteenM_59
      · exact prime_fifteenM_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (79 : ZMod 208635332488733341325534401) ^ 104317666244366670662767200 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (79 : ZMod 208635332488733341325534401) ^ 69545110829577780441844800 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (79 : ZMod 208635332488733341325534401) ^ 41727066497746668265106880 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (79 : ZMod 208635332488733341325534401) ^ 29805047498390477332219200 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (79 : ZMod 208635332488733341325534401) ^ 18966848408066667393230400 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (79 : ZMod 208635332488733341325534401) ^ 16048871729902564717348800 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (79 : ZMod 208635332488733341325534401) ^ 10980806973091228490817600 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (79 : ZMod 208635332488733341325534401) ^ 9071101412553623535892800 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (79 : ZMod 208635332488733341325534401) ^ 7194321809956322114673600 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (79 : ZMod 208635332488733341325534401) ^ 6730172015765591655662400 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (79 : ZMod 208635332488733341325534401) ^ 5638792769965765981771200 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (79 : ZMod 208635332488733341325534401) ^ 5088666646066666861598400 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (79 : ZMod 208635332488733341325534401) ^ 4851984476482170728500800 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (79 : ZMod 208635332488733341325534401) ^ 4439049627419858326075200 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (79 : ZMod 208635332488733341325534401) ^ 3936515707334591345764800 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (79 : ZMod 208635332488733341325534401) ^ 3536192076080226124161600 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (79 : ZMod 208635332488733341325534401) ^ 3420251352274317070910400 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide

private theorem prime_fifteenM_206209340250492255961284001 : Nat.Prime 206209340250492255961284001 := by
  apply lucas_primality 206209340250492255961284001 (67 : ZMod 206209340250492255961284001)
  · rw [← fifteenMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 5), (3, 4), (5, 3), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 5), (3, 4), (5, 3), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod = 206209340250492255961284001 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fifteenM_2
      · exact prime_fifteenM_3
      · exact prime_fifteenM_5
      · exact prime_fifteenM_7
      · exact prime_fifteenM_11
      · exact prime_fifteenM_13
      · exact prime_fifteenM_17
      · exact prime_fifteenM_19
      · exact prime_fifteenM_23
      · exact prime_fifteenM_29
      · exact prime_fifteenM_31
      · exact prime_fifteenM_37
      · exact prime_fifteenM_41
      · exact prime_fifteenM_47
      · exact prime_fifteenM_53
      · exact prime_fifteenM_59
      · exact prime_fifteenM_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (67 : ZMod 206209340250492255961284001) ^ 103104670125246127980642000 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (67 : ZMod 206209340250492255961284001) ^ 68736446750164085320428000 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (67 : ZMod 206209340250492255961284001) ^ 41241868050098451192256800 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (67 : ZMod 206209340250492255961284001) ^ 29458477178641750851612000 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (67 : ZMod 206209340250492255961284001) ^ 18746303659135659632844000 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (67 : ZMod 206209340250492255961284001) ^ 15862256942345558150868000 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (67 : ZMod 206209340250492255961284001) ^ 12129961191205426821252000 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (67 : ZMod 206209340250492255961284001) ^ 10853123171078539787436000 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (67 : ZMod 206209340250492255961284001) ^ 8965623489151837215708000 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (67 : ZMod 206209340250492255961284001) ^ 7110666905189388136596000 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (67 : ZMod 206209340250492255961284001) ^ 6651914201628782450364000 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (67 : ZMod 206209340250492255961284001) ^ 5573225412175466377332000 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (67 : ZMod 206209340250492255961284001) ^ 5029496103670542828324000 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (67 : ZMod 206209340250492255961284001) ^ 4387432771287069275772000 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (67 : ZMod 206209340250492255961284001) ^ 3890742268877212376628000 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (67 : ZMod 206209340250492255961284001) ^ 3495073563567665355276000 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (67 : ZMod 206209340250492255961284001) ^ 3380480987712987802644000 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide

private theorem prime_fifteenM_6397 : Nat.Prime 6397 := by norm_num
private theorem prime_fifteenM_2777 : Nat.Prime 2777 := by norm_num
private theorem prime_fifteenM_80567 : Nat.Prime 80567 := by norm_num
private theorem prime_fifteenM_894938237 : Nat.Prime 894938237 := by
  apply lucas_primality 894938237 (2 : ZMod 894938237)
  · rw [← fifteenMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (2777, 1), (80567, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (2777, 1), (80567, 1)] : List FactorBlock).map factorBlockValue).prod = 894938237 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fifteenM_2
      · exact prime_fifteenM_2777
      · exact prime_fifteenM_80567
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 894938237) ^ 447469118 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (2 : ZMod 894938237) ^ 322268 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (2 : ZMod 894938237) ^ 11108 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide

private theorem prime_fifteenM_47837 : Nat.Prime 47837 := by norm_num
private theorem prime_fifteenM_400062744481 : Nat.Prime 400062744481 := by
  apply lucas_primality 400062744481 (23 : ZMod 400062744481)
  · rw [← fifteenMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 5), (3, 1), (5, 1), (7, 1), (19, 1), (131, 1), (47837, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 5), (3, 1), (5, 1), (7, 1), (19, 1), (131, 1), (47837, 1)] : List FactorBlock).map factorBlockValue).prod = 400062744481 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fifteenM_2
      · exact prime_fifteenM_3
      · exact prime_fifteenM_5
      · exact prime_fifteenM_7
      · exact prime_fifteenM_19
      · exact prime_fifteenM_131
      · exact prime_fifteenM_47837
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (23 : ZMod 400062744481) ^ 200031372240 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (23 : ZMod 400062744481) ^ 133354248160 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (23 : ZMod 400062744481) ^ 80012548896 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (23 : ZMod 400062744481) ^ 57151820640 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (23 : ZMod 400062744481) ^ 21055933920 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (23 : ZMod 400062744481) ^ 3053914080 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (23 : ZMod 400062744481) ^ 8363040 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide

private theorem prime_fifteenM_263 : Nat.Prime 263 := by norm_num
private theorem prime_fifteenM_1657 : Nat.Prime 1657 := by norm_num
private theorem prime_fifteenM_1696543 : Nat.Prime 1696543 := by norm_num
private theorem prime_fifteenM_3761 : Nat.Prime 3761 := by norm_num
private theorem prime_fifteenM_9059154427 : Nat.Prime 9059154427 := by
  apply lucas_primality 9059154427 (3 : ZMod 9059154427)
  · rw [← fifteenMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 3), (7, 1), (41, 2), (53, 1), (269, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 3), (7, 1), (41, 2), (53, 1), (269, 1)] : List FactorBlock).map factorBlockValue).prod = 9059154427 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fifteenM_2
      · exact prime_fifteenM_3
      · exact prime_fifteenM_7
      · exact prime_fifteenM_41
      · exact prime_fifteenM_53
      · exact prime_fifteenM_269
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 9059154427) ^ 4529577213 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (3 : ZMod 9059154427) ^ 3019718142 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (3 : ZMod 9059154427) ^ 1294164918 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (3 : ZMod 9059154427) ^ 220954986 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (3 : ZMod 9059154427) ^ 170927442 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (3 : ZMod 9059154427) ^ 33677154 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide

private theorem prime_fifteenM_272571838399577 : Nat.Prime 272571838399577 := by
  apply lucas_primality 272571838399577 (3 : ZMod 272571838399577)
  · rw [← fifteenMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (3761, 1), (9059154427, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (3761, 1), (9059154427, 1)] : List FactorBlock).map factorBlockValue).prod = 272571838399577 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fifteenM_2
      · exact prime_fifteenM_3761
      · exact prime_fifteenM_9059154427
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 272571838399577) ^ 136285919199788 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (3 : ZMod 272571838399577) ^ 72473235416 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (3 : ZMod 272571838399577) ^ 30088 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide

private theorem prime_fifteenM_19531 : Nat.Prime 19531 := by norm_num
private theorem prime_fifteenM_2776871 : Nat.Prime 2776871 := by norm_num
private theorem prime_fifteenM_619997541913 : Nat.Prime 619997541913 := by
  apply lucas_primality 619997541913 (5 : ZMod 619997541913)
  · rw [← fifteenMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (3, 2), (7, 1), (443, 1), (2776871, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (3, 2), (7, 1), (443, 1), (2776871, 1)] : List FactorBlock).map factorBlockValue).prod = 619997541913 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fifteenM_2
      · exact prime_fifteenM_3
      · exact prime_fifteenM_7
      · exact prime_fifteenM_443
      · exact prime_fifteenM_2776871
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 619997541913) ^ 309998770956 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (5 : ZMod 619997541913) ^ 206665847304 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (5 : ZMod 619997541913) ^ 88571077416 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (5 : ZMod 619997541913) ^ 1399542984 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (5 : ZMod 619997541913) ^ 223272 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide

private theorem prime_fifteenM_6121 : Nat.Prime 6121 := by norm_num
private theorem prime_fifteenM_1464509982563 : Nat.Prime 1464509982563 := by
  apply lucas_primality 1464509982563 (2 : ZMod 1464509982563)
  · rw [← fifteenMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (11, 1), (31, 1), (461, 1), (761, 1), (6121, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (11, 1), (31, 1), (461, 1), (761, 1), (6121, 1)] : List FactorBlock).map factorBlockValue).prod = 1464509982563 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fifteenM_2
      · exact prime_fifteenM_11
      · exact prime_fifteenM_31
      · exact prime_fifteenM_461
      · exact prime_fifteenM_761
      · exact prime_fifteenM_6121
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1464509982563) ^ 732254991281 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (2 : ZMod 1464509982563) ^ 133137271142 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (2 : ZMod 1464509982563) ^ 47242257502 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (2 : ZMod 1464509982563) ^ 3176811242 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (2 : ZMod 1464509982563) ^ 1924454642 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (2 : ZMod 1464509982563) ^ 239259922 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide

private theorem prime_fifteenM_45127 : Nat.Prime 45127 := by norm_num
private theorem prime_fifteenM_1823 : Nat.Prime 1823 := by norm_num
private theorem prime_fifteenM_3271 : Nat.Prime 3271 := by norm_num
private theorem prime_fifteenM_908317 : Nat.Prime 908317 := by norm_num
private theorem prime_fifteenM_118081211 : Nat.Prime 118081211 := by
  apply lucas_primality 118081211 (14 : ZMod 118081211)
  · rw [← fifteenMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 1), (13, 1), (908317, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 1), (13, 1), (908317, 1)] : List FactorBlock).map factorBlockValue).prod = 118081211 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fifteenM_2
      · exact prime_fifteenM_5
      · exact prime_fifteenM_13
      · exact prime_fifteenM_908317
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (14 : ZMod 118081211) ^ 59040605 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (14 : ZMod 118081211) ^ 23616242 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (14 : ZMod 118081211) ^ 9083170 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (14 : ZMod 118081211) ^ 130 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide

private theorem prime_fifteenM_10675900157669865007 : Nat.Prime 10675900157669865007 := by
  apply lucas_primality 10675900157669865007 (10 : ZMod 10675900157669865007)
  · rw [← fifteenMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (7, 1), (19, 2), (1823, 1), (3271, 1), (118081211, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (7, 1), (19, 2), (1823, 1), (3271, 1), (118081211, 1)] : List FactorBlock).map factorBlockValue).prod = 10675900157669865007 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fifteenM_2
      · exact prime_fifteenM_3
      · exact prime_fifteenM_7
      · exact prime_fifteenM_19
      · exact prime_fifteenM_1823
      · exact prime_fifteenM_3271
      · exact prime_fifteenM_118081211
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 10675900157669865007) ^ 5337950078834932503 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (10 : ZMod 10675900157669865007) ^ 3558633385889955002 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (10 : ZMod 10675900157669865007) ^ 1525128593952837858 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (10 : ZMod 10675900157669865007) ^ 561889481982624474 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (10 : ZMod 10675900157669865007) ^ 5856226087586322 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (10 : ZMod 10675900157669865007) ^ 3263803166514786 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (10 : ZMod 10675900157669865007) ^ 90411506346 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide

private theorem prime_fifteenM_1093 : Nat.Prime 1093 := by norm_num
private theorem prime_fifteenM_1184461 : Nat.Prime 1184461 := by norm_num
private theorem prime_fifteenM_9380931121 : Nat.Prime 9380931121 := by
  apply lucas_primality 9380931121 (17 : ZMod 9380931121)
  · rw [← fifteenMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 4), (3, 2), (5, 1), (11, 1), (1184461, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 4), (3, 2), (5, 1), (11, 1), (1184461, 1)] : List FactorBlock).map factorBlockValue).prod = 9380931121 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fifteenM_2
      · exact prime_fifteenM_3
      · exact prime_fifteenM_5
      · exact prime_fifteenM_11
      · exact prime_fifteenM_1184461
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (17 : ZMod 9380931121) ^ 4690465560 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (17 : ZMod 9380931121) ^ 3126977040 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (17 : ZMod 9380931121) ^ 1876186224 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (17 : ZMod 9380931121) ^ 852811920 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (17 : ZMod 9380931121) ^ 7920 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide

private theorem prime_fifteenM_1947307 : Nat.Prime 1947307 := by norm_num
private theorem prime_fifteenM_125870029867 : Nat.Prime 125870029867 := by
  apply lucas_primality 125870029867 (2 : ZMod 125870029867)
  · rw [← fifteenMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 5), (7, 1), (19, 1), (1947307, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 5), (7, 1), (19, 1), (1947307, 1)] : List FactorBlock).map factorBlockValue).prod = 125870029867 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fifteenM_2
      · exact prime_fifteenM_3
      · exact prime_fifteenM_7
      · exact prime_fifteenM_19
      · exact prime_fifteenM_1947307
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 125870029867) ^ 62935014933 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (2 : ZMod 125870029867) ^ 41956676622 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (2 : ZMod 125870029867) ^ 17981432838 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (2 : ZMod 125870029867) ^ 6624738414 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (2 : ZMod 125870029867) ^ 64638 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide

private theorem prime_fifteenM_192760905016764500137722001 : Nat.Prime 192760905016764500137722001 := by
  apply lucas_primality 192760905016764500137722001 (139 : ZMod 192760905016764500137722001)
  · rw [← fifteenMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 4), (3, 4), (5, 3), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 4), (3, 4), (5, 3), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod = 192760905016764500137722001 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fifteenM_2
      · exact prime_fifteenM_3
      · exact prime_fifteenM_5
      · exact prime_fifteenM_7
      · exact prime_fifteenM_11
      · exact prime_fifteenM_13
      · exact prime_fifteenM_17
      · exact prime_fifteenM_19
      · exact prime_fifteenM_29
      · exact prime_fifteenM_31
      · exact prime_fifteenM_37
      · exact prime_fifteenM_41
      · exact prime_fifteenM_43
      · exact prime_fifteenM_47
      · exact prime_fifteenM_53
      · exact prime_fifteenM_59
      · exact prime_fifteenM_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (139 : ZMod 192760905016764500137722001) ^ 96380452508382250068861000 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (139 : ZMod 192760905016764500137722001) ^ 64253635005588166712574000 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (139 : ZMod 192760905016764500137722001) ^ 38552181003352900027544400 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (139 : ZMod 192760905016764500137722001) ^ 27537272145252071448246000 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (139 : ZMod 192760905016764500137722001) ^ 17523718637887681830702000 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (139 : ZMod 192760905016764500137722001) ^ 14827761924366500010594000 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (139 : ZMod 192760905016764500137722001) ^ 11338876765692029419866000 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (139 : ZMod 192760905016764500137722001) ^ 10145310790356026323038000 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (139 : ZMod 192760905016764500137722001) ^ 6646927759198775866818000 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (139 : ZMod 192760905016764500137722001) ^ 6218093710218209681862000 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (139 : ZMod 192760905016764500137722001) ^ 5209754189642283787506000 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (139 : ZMod 192760905016764500137722001) ^ 4701485488213768296042000 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (139 : ZMod 192760905016764500137722001) ^ 4482811744575918607854000 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (139 : ZMod 192760905016764500137722001) ^ 4101295851420521279526000 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (139 : ZMod 192760905016764500137722001) ^ 3636998207863481134674000 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (139 : ZMod 192760905016764500137722001) ^ 3267133983334991527758000 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide
    · change (139 : ZMod 192760905016764500137722001) ^ 3160014836340401641602000 ≠ 1
      rw [← fifteenMFastPow_eq_pow]
      decide

private theorem phi_fifteenM_17734003261542334012670423994 : Nat.totient 17734003261542334012670423994 = 5911040572802200311492366672 := by
  rw [← show ((([(2, 1), (3, 1), (20117, 1), (146923855955513032200547, 1)] : List FactorBlock).map factorBlockValue).prod) = 17734003261542334012670423994 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fifteenM_2, prime_fifteenM_3, prime_fifteenM_20117, prime_fifteenM_146923855955513032200547]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fifteenM_17734003261542334012670423995 : Nat.totient 17734003261542334012670423995 = 14183584462241545743906877440 := by
  rw [← show ((([(5, 1), (3923, 1), (8197093, 1), (110295707065568641, 1)] : List FactorBlock).map factorBlockValue).prod) = 17734003261542334012670423995 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fifteenM_5, prime_fifteenM_3923, prime_fifteenM_8197093, prime_fifteenM_110295707065568641]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fifteenM_17734003261542334012670423996 : Nat.totient 17734003261542334012670423996 = 8861972565448023872473835520 := by
  rw [← show ((([(2, 2), (1949, 1), (18481, 1), (1126858259, 1), (109229562569, 1)] : List FactorBlock).map factorBlockValue).prod) = 17734003261542334012670423996 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fifteenM_2, prime_fifteenM_1949, prime_fifteenM_18481, prime_fifteenM_1126858259, prime_fifteenM_109229562569]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fifteenM_17734003261542334012670423997 : Nat.totient 17734003261542334012670423997 = 11822668840998174197949986880 := by
  rw [← show ((([(3, 1), (393463482481, 1), (15023845118332079, 1)] : List FactorBlock).map factorBlockValue).prod) = 17734003261542334012670423997 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fifteenM_3, prime_fifteenM_393463482481, prime_fifteenM_15023845118332079]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fifteenM_17734003261542334012670423998 : Nat.totient 17734003261542334012670423998 = 8750584438901693921599292160 := by
  rw [← show ((([(2, 1), (89, 1), (661, 1), (2503, 1), (327583, 1), (183824382912019, 1)] : List FactorBlock).map factorBlockValue).prod) = 17734003261542334012670423998 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fifteenM_2, prime_fifteenM_89, prime_fifteenM_661, prime_fifteenM_2503, prime_fifteenM_327583, prime_fifteenM_183824382912019]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fifteenM_17734003261542334012670423999 : Nat.totient 17734003261542334012670423999 = 17725365169354539402824990664 := by
  rw [← show ((([(2053, 1), (8638092187794609845431283, 1)] : List FactorBlock).map factorBlockValue).prod) = 17734003261542334012670423999 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fifteenM_2053, prime_fifteenM_8638092187794609845431283]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fifteenM_17734003261542334012670424000 : Nat.totient 17734003261542334012670424000 = 2333570526890409590784000000 := by
  rw [← show ((([(2, 6), (3, 4), (5, 3), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 17734003261542334012670424000 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fifteenM_2, prime_fifteenM_3, prime_fifteenM_5, prime_fifteenM_7, prime_fifteenM_11, prime_fifteenM_13, prime_fifteenM_17, prime_fifteenM_19, prime_fifteenM_23, prime_fifteenM_29, prime_fifteenM_31, prime_fifteenM_37, prime_fifteenM_41, prime_fifteenM_43, prime_fifteenM_47, prime_fifteenM_53, prime_fifteenM_59, prime_fifteenM_61]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fifteenM_17734003261542334012670424001 : Nat.totient 17734003261542334012670424001 = 17713907915460003585022950720 := by
  rw [← show ((([(883, 1), (1535377, 1), (13080701940447819211, 1)] : List FactorBlock).map factorBlockValue).prod) = 17734003261542334012670424001 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fifteenM_883, prime_fifteenM_1535377, prime_fifteenM_13080701940447819211]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fifteenM_17734003261542334012670424002 : Nat.totient 17734003261542334012670424002 = 8863134643579378446803445552 := by
  rw [← show ((([(2, 1), (2293, 1), (3866987191788559531764157, 1)] : List FactorBlock).map factorBlockValue).prod) = 17734003261542334012670424002 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fifteenM_2, prime_fifteenM_2293, prime_fifteenM_3866987191788559531764157]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fifteenM_17734003261542334012670424003 : Nat.totient 17734003261542334012670424003 = 11822586549148761105448221024 := by
  rw [← show ((([(3, 1), (143669, 1), (13852339783, 1), (2970293224763, 1)] : List FactorBlock).map factorBlockValue).prod) = 17734003261542334012670424003 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fifteenM_3, prime_fifteenM_143669, prime_fifteenM_13852339783, prime_fifteenM_2970293224763]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fifteenM_17734003261542334012670424004 : Nat.totient 17734003261542334012670424004 = 8830203133997215364403916800 := by
  rw [← show ((([(2, 2), (241, 1), (1701391, 1), (11484449, 1), (941489444879, 1)] : List FactorBlock).map factorBlockValue).prod) = 17734003261542334012670424004 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fifteenM_2, prime_fifteenM_241, prime_fifteenM_1701391, prime_fifteenM_11484449, prime_fifteenM_941489444879]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fifteenM_17734003261542334012670424005 : Nat.totient 17734003261542334012670424005 = 14187202608767627957354904400 := by
  rw [← show ((([(5, 1), (30429025931, 1), (116559782766332771, 1)] : List FactorBlock).map factorBlockValue).prod) = 17734003261542334012670424005 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fifteenM_5, prime_fifteenM_30429025931, prime_fifteenM_116559782766332771]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fifteenM_17734003261542334012670424006 : Nat.totient 17734003261542334012670424006 = 5883617151582452919630148608 := by
  rw [← show ((([(2, 1), (3, 1), (223, 1), (5113, 1), (101287, 1), (25592998416424177, 1)] : List FactorBlock).map factorBlockValue).prod) = 17734003261542334012670424006 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fifteenM_2, prime_fifteenM_3, prime_fifteenM_223, prime_fifteenM_5113, prime_fifteenM_101287, prime_fifteenM_25592998416424177]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fifteenM_17734003261542334012670424007 : Nat.totient 17734003261542334012670424007 = 15084290360665353527528774400 := by
  rw [← show ((([(7, 1), (131, 1), (60607, 1), (275672333, 1), (1157501278441, 1)] : List FactorBlock).map factorBlockValue).prod) = 17734003261542334012670424007 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fifteenM_7, prime_fifteenM_131, prime_fifteenM_60607, prime_fifteenM_275672333, prime_fifteenM_1157501278441]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fifteenM_17734003261542334012670424008 : Nat.totient 17734003261542334012670424008 = 8824553926128630964713600000 := by
  rw [← show ((([(2, 3), (211, 1), (28751, 1), (75389, 1), (4847004293442769, 1)] : List FactorBlock).map factorBlockValue).prod) = 17734003261542334012670424008 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fifteenM_2, prime_fifteenM_211, prime_fifteenM_28751, prime_fifteenM_75389, prime_fifteenM_4847004293442769]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fifteenM_17734003261542334012670424009 : Nat.totient 17734003261542334012670424009 = 11660713454605173244211001600 := by
  rw [← show ((([(3, 2), (73, 1), (13737811, 1), (68784581, 1), (28564904807, 1)] : List FactorBlock).map factorBlockValue).prod) = 17734003261542334012670424009 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fifteenM_3, prime_fifteenM_73, prime_fifteenM_13737811, prime_fifteenM_68784581, prime_fifteenM_28564904807]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fifteenM_17734003261542334012670424010 : Nat.totient 17734003261542334012670424010 = 7092663234788967769154350080 := by
  rw [← show ((([(2, 1), (5, 1), (8233, 1), (93811, 1), (8274073, 1), (277508030299, 1)] : List FactorBlock).map factorBlockValue).prod) = 17734003261542334012670424010 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fifteenM_2, prime_fifteenM_5, prime_fifteenM_8233, prime_fifteenM_93811, prime_fifteenM_8274073, prime_fifteenM_277508030299]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fifteenM_17734003261542334012670424011 : Nat.totient 17734003261542334012670424011 = 16089469994230363967422824000 := by
  rw [← show ((([(11, 2), (499, 1), (375101, 1), (783019623353225509, 1)] : List FactorBlock).map factorBlockValue).prod) = 17734003261542334012670424011 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fifteenM_11, prime_fifteenM_499, prime_fifteenM_375101, prime_fifteenM_783019623353225509]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fifteenM_17734003261542334012670424012 : Nat.totient 17734003261542334012670424012 = 5911334420514111337556808000 := by
  rw [← show ((([(2, 2), (3, 1), (1477833605128527834389202001, 1)] : List FactorBlock).map factorBlockValue).prod) = 17734003261542334012670424012 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fifteenM_2, prime_fifteenM_3, prime_fifteenM_1477833605128527834389202001]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fifteenM_17734003261542334012670424013 : Nat.totient 17734003261542334012670424013 = 16298346731226508570939428096 := by
  rw [← show ((([(13, 1), (229, 1), (887599, 1), (1779481213, 1), (3771531487, 1)] : List FactorBlock).map factorBlockValue).prod) = 17734003261542334012670424013 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fifteenM_13, prime_fifteenM_229, prime_fifteenM_887599, prime_fifteenM_1779481213, prime_fifteenM_3771531487]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fifteenM_17734003261542334012670424014 : Nat.totient 17734003261542334012670424014 = 7600079380092701303391467328 := by
  rw [← show ((([(2, 1), (7, 1), (36587, 1), (107042151929, 1), (323442523387, 1)] : List FactorBlock).map factorBlockValue).prod) = 17734003261542334012670424014 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fifteenM_2, prime_fifteenM_7, prime_fifteenM_36587, prime_fifteenM_107042151929, prime_fifteenM_323442523387]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fifteenM_17734003261542334012670424015 : Nat.totient 17734003261542334012670424015 = 9364438622826365116007809536 := by
  rw [← show ((([(3, 1), (5, 1), (103, 1), (5009, 1), (2291539082278737626663, 1)] : List FactorBlock).map factorBlockValue).prod) = 17734003261542334012670424015 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fifteenM_3, prime_fifteenM_5, prime_fifteenM_103, prime_fifteenM_5009, prime_fifteenM_2291539082278737626663]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fifteenM_17734003261542334012670424016 : Nat.totient 17734003261542334012670424016 = 8866979059608099641364273024 := by
  rw [← show ((([(2, 4), (406247, 1), (11909399, 1), (229090346350717, 1)] : List FactorBlock).map factorBlockValue).prod) = 17734003261542334012670424016 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fifteenM_2, prime_fifteenM_406247, prime_fifteenM_11909399, prime_fifteenM_229090346350717]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fifteenM_17734003261542334012670424017 : Nat.totient 17734003261542334012670424017 = 16668893843475415322740876800 := by
  rw [← show ((([(17, 2), (761, 1), (29811610063, 1), (2704823010871, 1)] : List FactorBlock).map factorBlockValue).prod) = 17734003261542334012670424017 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fifteenM_17, prime_fifteenM_761, prime_fifteenM_29811610063, prime_fifteenM_2704823010871]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fifteenM_17734003261542334012670424018 : Nat.totient 17734003261542334012670424018 = 5880768161504026991300222976 := by
  rw [← show ((([(2, 1), (3, 2), (283, 1), (613, 1), (85303, 1), (66576822500643073, 1)] : List FactorBlock).map factorBlockValue).prod) = 17734003261542334012670424018 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fifteenM_2, prime_fifteenM_3, prime_fifteenM_283, prime_fifteenM_613, prime_fifteenM_85303, prime_fifteenM_66576822500643073]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fifteenM_17734003261542334012670424019 : Nat.totient 17734003261542334012670424019 = 16787282114794309790110433280 := by
  rw [← show ((([(19, 1), (2113, 1), (4871, 1), (11119, 1), (48179, 1), (230969, 1), (732923, 1)] : List FactorBlock).map factorBlockValue).prod) = 17734003261542334012670424019 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fifteenM_19, prime_fifteenM_2113, prime_fifteenM_4871, prime_fifteenM_11119, prime_fifteenM_48179, prime_fifteenM_230969, prime_fifteenM_732923]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fifteenM_17734003261542334012670424020 : Nat.totient 17734003261542334012670424020 = 7080246641613070805070643200 := by
  rw [← show ((([(2, 2), (5, 1), (769, 1), (2143, 1), (8597, 1), (9792301, 1), (6391408799, 1)] : List FactorBlock).map factorBlockValue).prod) = 17734003261542334012670424020 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fifteenM_2, prime_fifteenM_5, prime_fifteenM_769, prime_fifteenM_2143, prime_fifteenM_8597, prime_fifteenM_9792301, prime_fifteenM_6391408799]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fifteenM_17734003261542334012670424021 : Nat.totient 17734003261542334012670424021 = 10043852580825757730349465600 := by
  rw [← show ((([(3, 1), (7, 1), (113, 1), (54421, 1), (97654321, 1), (1406212853597, 1)] : List FactorBlock).map factorBlockValue).prod) = 17734003261542334012670424021 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fifteenM_3, prime_fifteenM_7, prime_fifteenM_113, prime_fifteenM_54421, prime_fifteenM_97654321, prime_fifteenM_1406212853597]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fifteenM_17734003261542334012670424022 : Nat.totient 17734003261542334012670424022 = 8038707276679890382913236800 := by
  rw [← show ((([(2, 1), (11, 1), (367, 1), (33641, 1), (65290371830632690583, 1)] : List FactorBlock).map factorBlockValue).prod) = 17734003261542334012670424022 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fifteenM_2, prime_fifteenM_11, prime_fifteenM_367, prime_fifteenM_33641, prime_fifteenM_65290371830632690583]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fifteenM_17734003261542334012670424023 : Nat.totient 17734003261542334012670424023 = 16748238333046423068674265600 := by
  rw [← show ((([(23, 1), (79, 1), (82621199, 1), (325800521, 1), (362583961, 1)] : List FactorBlock).map factorBlockValue).prod) = 17734003261542334012670424023 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fifteenM_23, prime_fifteenM_79, prime_fifteenM_82621199, prime_fifteenM_325800521, prime_fifteenM_362583961]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fifteenM_17734003261542334012670424024 : Nat.totient 17734003261542334012670424024 = 5840109395431937154145971200 := by
  rw [← show ((([(2, 3), (3, 1), (83, 1), (1433741, 1), (106163831, 1), (58488456857, 1)] : List FactorBlock).map factorBlockValue).prod) = 17734003261542334012670424024 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fifteenM_2, prime_fifteenM_3, prime_fifteenM_83, prime_fifteenM_1433741, prime_fifteenM_106163831, prime_fifteenM_58488456857]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fifteenM_17734003261542334012670424025 : Nat.totient 17734003261542334012670424025 = 14117584820985319161762892800 := by
  rw [← show ((([(5, 2), (281, 1), (739, 1), (3540386347, 1), (964862349257, 1)] : List FactorBlock).map factorBlockValue).prod) = 17734003261542334012670424025 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fifteenM_5, prime_fifteenM_281, prime_fifteenM_739, prime_fifteenM_3540386347, prime_fifteenM_964862349257]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fifteenM_17734003261542334012670424026 : Nat.totient 17734003261542334012670424026 = 8124919027229335929268589568 := by
  rw [← show ((([(2, 1), (13, 1), (137, 1), (31063, 1), (912772537, 1), (175592882183, 1)] : List FactorBlock).map factorBlockValue).prod) = 17734003261542334012670424026 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fifteenM_2, prime_fifteenM_13, prime_fifteenM_137, prime_fifteenM_31063, prime_fifteenM_912772537, prime_fifteenM_175592882183]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fifteenM_17734003261542334012670424027 : Nat.totient 17734003261542334012670424027 = 11801564591366053555799364864 := by
  rw [← show ((([(3, 3), (569, 1), (37039, 1), (1544987, 1), (20171893710853, 1)] : List FactorBlock).map factorBlockValue).prod) = 17734003261542334012670424027 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fifteenM_3, prime_fifteenM_569, prime_fifteenM_37039, prime_fifteenM_1544987, prime_fifteenM_20171893710853]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fifteenM_17734003261542334012670424028 : Nat.totient 17734003261542334012670424028 = 7600287112089571719715896000 := by
  rw [← show ((([(2, 2), (7, 1), (633357259340797643309658001, 1)] : List FactorBlock).map factorBlockValue).prod) = 17734003261542334012670424028 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fifteenM_2, prime_fifteenM_7, prime_fifteenM_633357259340797643309658001]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fifteenM_17734003261542334012670424029 : Nat.totient 17734003261542334012670424029 = 17077763509722148036096016640 := by
  rw [← show ((([(29, 1), (383, 1), (1056241, 1), (1511635180256161967, 1)] : List FactorBlock).map factorBlockValue).prod) = 17734003261542334012670424029 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fifteenM_29, prime_fifteenM_383, prime_fifteenM_1056241, prime_fifteenM_1511635180256161967]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fifteenM_17734003261542334012670424030 : Nat.totient 17734003261542334012670424030 = 4729067532543297963057648800 := by
  rw [← show ((([(2, 1), (3, 1), (5, 1), (1222615931, 1), (483498887150858771, 1)] : List FactorBlock).map factorBlockValue).prod) = 17734003261542334012670424030 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fifteenM_2, prime_fifteenM_3, prime_fifteenM_5, prime_fifteenM_1222615931, prime_fifteenM_483498887150858771]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fifteenM_17734003261542334012670424031 : Nat.totient 17734003261542334012670424031 = 17160796015907491722944332800 := by
  rw [← show ((([(31, 1), (15073, 1), (4979131, 1), (33351053, 1), (228550559, 1)] : List FactorBlock).map factorBlockValue).prod) = 17734003261542334012670424031 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fifteenM_31, prime_fifteenM_15073, prime_fifteenM_4979131, prime_fifteenM_33351053, prime_fifteenM_228550559]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fifteenM_17734003261542334012670424032 : Nat.totient 17734003261542334012670424032 = 8867001629591136385268551552 := by
  rw [← show ((([(2, 5), (7514213933, 1), (73751906302452347, 1)] : List FactorBlock).map factorBlockValue).prod) = 17734003261542334012670424032 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fifteenM_2, prime_fifteenM_7514213933, prime_fifteenM_73751906302452347]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fifteenM_17734003261542334012670424033 : Nat.totient 17734003261542334012670424033 = 10596502161856110116733916800 := by
  rw [← show ((([(3, 1), (11, 1), (71, 1), (26687336297, 1), (283615046165023, 1)] : List FactorBlock).map factorBlockValue).prod) = 17734003261542334012670424033 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fifteenM_3, prime_fifteenM_11, prime_fifteenM_71, prime_fifteenM_26687336297, prime_fifteenM_283615046165023]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fifteenM_17734003261542334012670424034 : Nat.totient 17734003261542334012670424034 = 8220854892065079161551610880 := by
  rw [← show ((([(2, 1), (17, 1), (67, 1), (293769120283, 1), (26500063922641, 1)] : List FactorBlock).map factorBlockValue).prod) = 17734003261542334012670424034 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fifteenM_2, prime_fifteenM_17, prime_fifteenM_67, prime_fifteenM_293769120283, prime_fifteenM_26500063922641]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fifteenM_17734003261542334012670424035 : Nat.totient 17734003261542334012670424035 = 12143732174124047542787144832 := by
  rw [← show ((([(5, 1), (7, 1), (727, 1), (40346827, 1), (17274080639688469, 1)] : List FactorBlock).map factorBlockValue).prod) = 17734003261542334012670424035 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fifteenM_5, prime_fifteenM_7, prime_fifteenM_727, prime_fifteenM_40346827, prime_fifteenM_17274080639688469]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fifteenM_17734003261542334012670424036 : Nat.totient 17734003261542334012670424036 = 5857094301629021576811806976 := by
  rw [← show ((([(2, 2), (3, 2), (109, 1), (762563, 1), (500452427, 1), (11842387189, 1)] : List FactorBlock).map factorBlockValue).prod) = 17734003261542334012670424036 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fifteenM_2, prime_fifteenM_3, prime_fifteenM_109, prime_fifteenM_762563, prime_fifteenM_500452427, prime_fifteenM_11842387189]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fifteenM_17734003261542334012670424037 : Nat.totient 17734003261542334012670424037 = 17254691634756876898718230272 := by
  rw [← show ((([(37, 1), (1211593, 1), (395592732416818278457, 1)] : List FactorBlock).map factorBlockValue).prod) = 17734003261542334012670424037 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fifteenM_37, prime_fifteenM_1211593, prime_fifteenM_395592732416818278457]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fifteenM_17734003261542334012670424038 : Nat.totient 17734003261542334012670424038 = 8396296086368255090427438336 := by
  rw [← show ((([(2, 1), (19, 1), (2089, 1), (251162293, 1), (889467958641013, 1)] : List FactorBlock).map factorBlockValue).prod) = 17734003261542334012670424038 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fifteenM_2, prime_fifteenM_19, prime_fifteenM_2089, prime_fifteenM_251162293, prime_fifteenM_889467958641013]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fifteenM_17734003261542334012670424039 : Nat.totient 17734003261542334012670424039 = 10888675595149121812154112000 := by
  rw [← show ((([(3, 1), (13, 1), (599, 1), (1811, 1), (33809, 1), (12398369604474701, 1)] : List FactorBlock).map factorBlockValue).prod) = 17734003261542334012670424039 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fifteenM_3, prime_fifteenM_13, prime_fifteenM_599, prime_fifteenM_1811, prime_fifteenM_33809, prime_fifteenM_12398369604474701]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fifteenM_17734003261542334012670424040 : Nat.totient 17734003261542334012670424040 = 7074401428646019176591278080 := by
  rw [← show ((([(2, 3), (5, 1), (373, 1), (55249, 1), (157429, 1), (773027, 1), (176780411, 1)] : List FactorBlock).map factorBlockValue).prod) = 17734003261542334012670424040 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fifteenM_2, prime_fifteenM_5, prime_fifteenM_373, prime_fifteenM_55249, prime_fifteenM_157429, prime_fifteenM_773027, prime_fifteenM_176780411]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fifteenM_17734003261542334012670424041 : Nat.totient 17734003261542334012670424041 = 17300808953649091232864409600 := by
  rw [← show ((([(41, 1), (42743, 1), (68483, 1), (77945521, 1), (1895762749, 1)] : List FactorBlock).map factorBlockValue).prod) = 17734003261542334012670424041 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fifteenM_41, prime_fifteenM_42743, prime_fifteenM_68483, prime_fifteenM_77945521, prime_fifteenM_1895762749]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fifteenM_17734003261542334012670424042 : Nat.totient 17734003261542334012670424042 = 5066858071694637935320021248 := by
  rw [← show ((([(2, 1), (3, 1), (7, 1), (1671268889, 1), (252645265925168009, 1)] : List FactorBlock).map factorBlockValue).prod) = 17734003261542334012670424042 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fifteenM_2, prime_fifteenM_3, prime_fifteenM_7, prime_fifteenM_1671268889, prime_fifteenM_252645265925168009]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fifteenM_17734003261542334012670424043 : Nat.totient 17734003261542334012670424043 = 17295058417823828291710311216 := by
  rw [← show ((([(43, 2), (653, 1), (14687798016346184405519, 1)] : List FactorBlock).map factorBlockValue).prod) = 17734003261542334012670424043 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fifteenM_43, prime_fifteenM_653, prime_fifteenM_14687798016346184405519]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fifteenM_17734003261542334012670424044 : Nat.totient 17734003261542334012670424044 = 8040188411957964202005004800 := by
  rw [← show ((([(2, 2), (11, 1), (389, 1), (305476361, 1), (3391773930127669, 1)] : List FactorBlock).map factorBlockValue).prod) = 17734003261542334012670424044 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fifteenM_2, prime_fifteenM_11, prime_fifteenM_389, prime_fifteenM_305476361, prime_fifteenM_3391773930127669]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fifteenM_17734003261542334012670424045 : Nat.totient 17734003261542334012670424045 = 9458135072822578140090892800 := by
  rw [← show ((([(3, 2), (5, 1), (394088961367607422503787201, 1)] : List FactorBlock).map factorBlockValue).prod) = 17734003261542334012670424045 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fifteenM_3, prime_fifteenM_5, prime_fifteenM_394088961367607422503787201]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fifteenM_17734003261542334012670424046 : Nat.totient 17734003261542334012670424046 = 8481479815830260711380905304 := by
  rw [← show ((([(2, 1), (23, 1), (1728312167, 1), (223062602575272503, 1)] : List FactorBlock).map factorBlockValue).prod) = 17734003261542334012670424046 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fifteenM_2, prime_fifteenM_23, prime_fifteenM_1728312167, prime_fifteenM_223062602575272503]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fifteenM_17734003261542334012670424047 : Nat.totient 17734003261542334012670424047 = 17356684041958080915623466400 := by
  rw [← show ((([(47, 1), (13845864341, 1), (27251402226539261, 1)] : List FactorBlock).map factorBlockValue).prod) = 17734003261542334012670424047 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fifteenM_47, prime_fifteenM_13845864341, prime_fifteenM_27251402226539261]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fifteenM_17734003261542334012670424048 : Nat.totient 17734003261542334012670424048 = 5911334406862518913240200192 := by
  rw [← show ((([(2, 4), (3, 1), (433014277, 1), (853224526086773713, 1)] : List FactorBlock).map factorBlockValue).prod) = 17734003261542334012670424048 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fifteenM_2, prime_fifteenM_3, prime_fifteenM_433014277, prime_fifteenM_853224526086773713]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fifteenM_17734003261542334012670424049 : Nat.totient 17734003261542334012670424049 = 15049485067130074421137670400 := by
  rw [← show ((([(7, 2), (101, 1), (25577, 1), (140100513382431394213, 1)] : List FactorBlock).map factorBlockValue).prod) = 17734003261542334012670424049 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fifteenM_7, prime_fifteenM_101, prime_fifteenM_25577, prime_fifteenM_140100513382431394213]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fifteenM_17734003261542334012670424050 : Nat.totient 17734003261542334012670424050 = 7093562012070392989589243840 := by
  rw [← show ((([(2, 1), (5, 2), (180533, 1), (1964627327030773765757, 1)] : List FactorBlock).map factorBlockValue).prod) = 17734003261542334012670424050 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fifteenM_2, prime_fifteenM_5, prime_fifteenM_180533, prime_fifteenM_1964627327030773765757]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fifteenM_17734003261542334012670424051 : Nat.totient 17734003261542334012670424051 = 11127214480650070703297745024 := by
  rw [← show ((([(3, 1), (17, 1), (3421567, 1), (101627574192727747903, 1)] : List FactorBlock).map factorBlockValue).prod) = 17734003261542334012670424051 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fifteenM_3, prime_fifteenM_17, prime_fifteenM_3421567, prime_fifteenM_101627574192727747903]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fifteenM_17734003261542334012670424052 : Nat.totient 17734003261542334012670424052 = 8184924574326795910730043552 := by
  rw [← show ((([(2, 2), (13, 2), (1032992039, 1), (25395871066744643, 1)] : List FactorBlock).map factorBlockValue).prod) = 17734003261542334012670424052 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fifteenM_2, prime_fifteenM_13, prime_fifteenM_1032992039, prime_fifteenM_25395871066744643]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fifteenM_17734003261542334012670424053 : Nat.totient 17734003261542334012670424053 = 17394730953269868018806575824 := by
  rw [← show ((([(53, 1), (3727, 1), (89778329788956336031663, 1)] : List FactorBlock).map factorBlockValue).prod) = 17734003261542334012670424053 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fifteenM_53, prime_fifteenM_3727, prime_fifteenM_89778329788956336031663]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fifteenM_17734003261542334012670424054 : Nat.totient 17734003261542334012670424054 = 5911333610086937073892778496 := by
  rw [← show ((([(2, 1), (3, 3), (7294097, 1), (45023731903529596433, 1)] : List FactorBlock).map factorBlockValue).prod) = 17734003261542334012670424054 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fifteenM_2, prime_fifteenM_3, prime_fifteenM_7294097, prime_fifteenM_45023731903529596433]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fifteenM_17734003261542334012670424055 : Nat.totient 17734003261542334012670424055 = 12894675488606279820673029120 := by
  rw [← show ((([(5, 1), (11, 1), (4637, 1), (2076644077, 1), (33484585780649, 1)] : List FactorBlock).map factorBlockValue).prod) = 17734003261542334012670424055 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fifteenM_5, prime_fifteenM_11, prime_fifteenM_4637, prime_fifteenM_2076644077, prime_fifteenM_33484585780649]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fifteenM_17734003261542334012670424056 : Nat.totient 17734003261542334012670424056 = 7600028853226593294516741120 := by
  rw [← show ((([(2, 3), (7, 1), (29429, 1), (17754445789, 1), (606088622921, 1)] : List FactorBlock).map factorBlockValue).prod) = 17734003261542334012670424056 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fifteenM_2, prime_fifteenM_7, prime_fifteenM_29429, prime_fifteenM_17754445789, prime_fifteenM_606088622921]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fifteenM_17734003261542334012670424057 : Nat.totient 17734003261542334012670424057 = 11200423111345913548818926592 := by
  rw [← show ((([(3, 1), (19, 1), (9278485297, 1), (33531643827487633, 1)] : List FactorBlock).map factorBlockValue).prod) = 17734003261542334012670424057 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fifteenM_3, prime_fifteenM_19, prime_fifteenM_9278485297, prime_fifteenM_33531643827487633]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fifteenM_17734003261542334012670424058 : Nat.totient 17734003261542334012670424058 = 8560155535715945579472101376 := by
  rw [← show ((([(2, 1), (29, 1), (7873, 1), (38836361859919178187937, 1)] : List FactorBlock).map factorBlockValue).prod) = 17734003261542334012670424058 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fifteenM_2, prime_fifteenM_29, prime_fifteenM_7873, prime_fifteenM_38836361859919178187937]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fifteenM_17734003261542334012670424059 : Nat.totient 17734003261542334012670424059 = 17358599155108382979046124032 := by
  rw [← show ((([(59, 1), (233, 1), (3007847, 1), (40144103, 1), (10683691817, 1)] : List FactorBlock).map factorBlockValue).prod) = 17734003261542334012670424059 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fifteenM_59, prime_fifteenM_233, prime_fifteenM_3007847, prime_fifteenM_40144103, prime_fifteenM_10683691817]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fifteenM_17734003261542334012670424060 : Nat.totient 17734003261542334012670424060 = 4729067310472396597300764672 := by
  rw [← show ((([(2, 2), (3, 1), (5, 1), (20930737, 1), (14121180779525611873, 1)] : List FactorBlock).map factorBlockValue).prod) = 17734003261542334012670424060 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fifteenM_2, prime_fifteenM_3, prime_fifteenM_5, prime_fifteenM_20930737, prime_fifteenM_14121180779525611873]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fifteenM_17734003261542334012670424061 : Nat.totient 17734003261542334012670424061 = 17443281896599017061643040000 := by
  rw [← show ((([(61, 1), (290721364943316951027384001, 1)] : List FactorBlock).map factorBlockValue).prod) = 17734003261542334012670424061 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fifteenM_61, prime_fifteenM_290721364943316951027384001]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fifteenM_17734003261542334012670424062 : Nat.totient 17734003261542334012670424062 = 8580969320101129360969560000 := by
  rw [← show ((([(2, 1), (31, 1), (286032310670037645365652001, 1)] : List FactorBlock).map factorBlockValue).prod) = 17734003261542334012670424062 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fifteenM_2, prime_fifteenM_31, prime_fifteenM_286032310670037645365652001]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fifteenM_17734003261542334012670424063 : Nat.totient 17734003261542334012670424063 = 9941801852202141359370240000 := by
  rw [← show ((([(3, 2), (7, 1), (97, 1), (139, 1), (659, 1), (55001, 1), (576001613200633, 1)] : List FactorBlock).map factorBlockValue).prod) = 17734003261542334012670424063 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fifteenM_3, prime_fifteenM_7, prime_fifteenM_97, prime_fifteenM_139, prime_fifteenM_659, prime_fifteenM_55001, prime_fifteenM_576001613200633]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fifteenM_17734003261542334012670424064 : Nat.totient 17734003261542334012670424064 = 8867001630771167006335211520 := by
  rw [← show ((([(2, 10), (17318362560099935559248461, 1)] : List FactorBlock).map factorBlockValue).prod) = 17734003261542334012670424064 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fifteenM_2, prime_fifteenM_17318362560099935559248461]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fifteenM_17734003261542334012670424065 : Nat.totient 17734003261542334012670424065 = 13095879331600492809356620800 := by
  rw [← show ((([(5, 1), (13, 1), (272830819408343600194929601, 1)] : List FactorBlock).map factorBlockValue).prod) = 17734003261542334012670424065 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fifteenM_5, prime_fifteenM_13, prime_fifteenM_272830819408343600194929601]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fifteenM_17734003261542334012670424066 : Nat.totient 17734003261542334012670424066 = 5370176130405898412111884800 := by
  rw [← show ((([(2, 1), (3, 1), (11, 1), (1471, 1), (48383, 1), (3775351412811012257, 1)] : List FactorBlock).map factorBlockValue).prod) = 17734003261542334012670424066 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fifteenM_2, prime_fifteenM_3, prime_fifteenM_11, prime_fifteenM_1471, prime_fifteenM_48383, prime_fifteenM_3775351412811012257]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fifteenM_17734003261542334012670424067 : Nat.totient 17734003261542334012670424067 = 17677585217963995907829523200 := by
  rw [← show ((([(359, 1), (2531, 1), (543841, 1), (35887916391298903, 1)] : List FactorBlock).map factorBlockValue).prod) = 17734003261542334012670424067 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fifteenM_359, prime_fifteenM_2531, prime_fifteenM_543841, prime_fifteenM_35887916391298903]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fifteenM_17734003261542334012670424068 : Nat.totient 17734003261542334012670424068 = 8229314642961719800075821056 := by
  rw [← show ((([(2, 2), (17, 1), (149, 1), (173, 1), (677, 1), (14944343145089993069, 1)] : List FactorBlock).map factorBlockValue).prod) = 17734003261542334012670424068 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fifteenM_2, prime_fifteenM_17, prime_fifteenM_149, prime_fifteenM_173, prime_fifteenM_677, prime_fifteenM_14944343145089993069]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fifteenM_17734003261542334012670424069 : Nat.totient 17734003261542334012670424069 = 11308639383650464384465962432 := by
  rw [← show ((([(3, 1), (23, 1), (56297287, 1), (64144099, 1), (71172712477, 1)] : List FactorBlock).map factorBlockValue).prod) = 17734003261542334012670424069 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fifteenM_3, prime_fifteenM_23, prime_fifteenM_56297287, prime_fifteenM_64144099, prime_fifteenM_71172712477]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fifteenM_17734003261542334012670424070 : Nat.totient 17734003261542334012670424070 = 6080198556103818538901644800 := by
  rw [← show ((([(2, 1), (5, 1), (7, 1), (339389, 1), (545911, 1), (2940799, 1), (464968781, 1)] : List FactorBlock).map factorBlockValue).prod) = 17734003261542334012670424070 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fifteenM_2, prime_fifteenM_5, prime_fifteenM_7, prime_fifteenM_339389, prime_fifteenM_545911, prime_fifteenM_2940799, prime_fifteenM_464968781]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fifteenM_17734003261542334012670424071 : Nat.totient 17734003261542334012670424071 = 17734003247276254625895357552 := by
  rw [← show ((([(1243088783, 1), (14266079385531977737, 1)] : List FactorBlock).map factorBlockValue).prod) = 17734003261542334012670424071 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fifteenM_1243088783, prime_fifteenM_14266079385531977737]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fifteenM_17734003261542334012670424072 : Nat.totient 17734003261542334012670424072 = 5911334420514111337556808000 := by
  rw [← show ((([(2, 3), (3, 2), (246305600854754639064867001, 1)] : List FactorBlock).map factorBlockValue).prod) = 17734003261542334012670424072 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fifteenM_2, prime_fifteenM_3, prime_fifteenM_246305600854754639064867001]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fifteenM_17734003261542334012670424073 : Nat.totient 17734003261542334012670424073 = 17734003261542334012670424072 := by
  rw [← show ((([(17734003261542334012670424073, 1)] : List FactorBlock).map factorBlockValue).prod) = 17734003261542334012670424073 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fifteenM_17734003261542334012670424073]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fifteenM_17734003261542334012670424074 : Nat.totient 17734003261542334012670424074 = 8623695128209477903772519040 := by
  rw [← show ((([(2, 1), (37, 1), (2473, 1), (50971, 1), (1901199948306317947, 1)] : List FactorBlock).map factorBlockValue).prod) = 17734003261542334012670424074 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fifteenM_2, prime_fifteenM_37, prime_fifteenM_2473, prime_fifteenM_50971, prime_fifteenM_1901199948306317947]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fifteenM_17734003261542334012670424075 : Nat.totient 17734003261542334012670424075 = 9458135057715683318239186080 := by
  rw [← show ((([(3, 1), (5, 2), (626080687, 1), (377672369920211983, 1)] : List FactorBlock).map factorBlockValue).prod) = 17734003261542334012670424075 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fifteenM_3, prime_fifteenM_5, prime_fifteenM_626080687, prime_fifteenM_377672369920211983]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fifteenM_17734003261542334012670424076 : Nat.totient 17734003261542334012670424076 = 8393987027455924091032706832 := by
  rw [← show ((([(2, 2), (19, 1), (1327, 1), (175841859968491790075263, 1)] : List FactorBlock).map factorBlockValue).prod) = 17734003261542334012670424076 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fifteenM_2, prime_fifteenM_19, prime_fifteenM_1327, prime_fifteenM_175841859968491790075263]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fifteenM_17734003261542334012670424077 : Nat.totient 17734003261542334012670424077 = 13806037750483514997900654000 := by
  rw [← show ((([(7, 1), (11, 1), (1091, 1), (211101494655711238500011, 1)] : List FactorBlock).map factorBlockValue).prod) = 17734003261542334012670424077 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fifteenM_7, prime_fifteenM_11, prime_fifteenM_1091, prime_fifteenM_211101494655711238500011]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fifteenM_17734003261542334012670424078 : Nat.totient 17734003261542334012670424078 = 5456616387944359692662572128 := by
  rw [← show ((([(2, 1), (3, 1), (13, 1), (24522826583, 1), (9271321778674247, 1)] : List FactorBlock).map factorBlockValue).prod) = 17734003261542334012670424078 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fifteenM_2, prime_fifteenM_3, prime_fifteenM_13, prime_fifteenM_24522826583, prime_fifteenM_9271321778674247]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fifteenM_17734003261542334012670424079 : Nat.totient 17734003261542334012670424079 = 17723770137906129549881806984 := by
  rw [← show ((([(1733, 1), (10233123636204462788615363, 1)] : List FactorBlock).map factorBlockValue).prod) = 17734003261542334012670424079 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fifteenM_1733, prime_fifteenM_10233123636204462788615363]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fifteenM_17734003261542334012670424080 : Nat.totient 17734003261542334012670424080 = 7031504270546446115051827200 := by
  rw [← show ((([(2, 4), (5, 1), (197, 1), (271, 1), (152441, 1), (27238268144131903, 1)] : List FactorBlock).map factorBlockValue).prod) = 17734003261542334012670424080 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fifteenM_2, prime_fifteenM_5, prime_fifteenM_197, prime_fifteenM_271, prime_fifteenM_152441, prime_fifteenM_27238268144131903]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fifteenM_17734003261542334012670424081 : Nat.totient 17734003261542334012670424081 = 11822668841028222675113615892 := by
  rw [← show ((([(3, 5), (72979437290297670834034667, 1)] : List FactorBlock).map factorBlockValue).prod) = 17734003261542334012670424081 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fifteenM_3, prime_fifteenM_72979437290297670834034667]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fifteenM_17734003261542334012670424082 : Nat.totient 17734003261542334012670424082 = 8532119018699252177598673920 := by
  rw [← show ((([(2, 1), (41, 1), (73, 1), (148667, 1), (158909, 1), (125402732291479, 1)] : List FactorBlock).map factorBlockValue).prod) = 17734003261542334012670424082 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fifteenM_2, prime_fifteenM_41, prime_fifteenM_73, prime_fifteenM_148667, prime_fifteenM_158909, prime_fifteenM_125402732291479]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fifteenM_17734003261542334012670424083 : Nat.totient 17734003261542334012670424083 = 17734003200033086306302785240 := by
  rw [← show ((([(288314423, 1), (61509247706079324421, 1)] : List FactorBlock).map factorBlockValue).prod) = 17734003261542334012670424083 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fifteenM_288314423, prime_fifteenM_61509247706079324421]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fifteenM_17734003261542334012670424084 : Nat.totient 17734003261542334012670424084 = 5059630031823775752545040000 := by
  rw [← show ((([(2, 2), (3, 1), (7, 1), (701, 1), (301168454275224747175301, 1)] : List FactorBlock).map factorBlockValue).prod) = 17734003261542334012670424084 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fifteenM_2, prime_fifteenM_3, prime_fifteenM_7, prime_fifteenM_701, prime_fifteenM_301168454275224747175301]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fifteenM_17734003261542334012670424085 : Nat.totient 17734003261542334012670424085 = 13352661279278933844834201600 := by
  rw [← show ((([(5, 1), (17, 1), (208635332488733341325534401, 1)] : List FactorBlock).map factorBlockValue).prod) = 17734003261542334012670424085 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fifteenM_5, prime_fifteenM_17, prime_fifteenM_208635332488733341325534401]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fifteenM_17734003261542334012670424086 : Nat.totient 17734003261542334012670424086 = 8660792290520674750373928000 := by
  rw [← show ((([(2, 1), (43, 1), (206209340250492255961284001, 1)] : List FactorBlock).map factorBlockValue).prod) = 17734003261542334012670424086 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fifteenM_2, prime_fifteenM_43, prime_fifteenM_206209340250492255961284001]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fifteenM_17734003261542334012670424087 : Nat.totient 17734003261542334012670424087 = 11284967892114778887097712640 := by
  rw [← show ((([(3, 1), (29, 1), (89, 1), (6397, 1), (894938237, 1), (400062744481, 1)] : List FactorBlock).map factorBlockValue).prod) = 17734003261542334012670424087 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fifteenM_3, prime_fifteenM_29, prime_fifteenM_89, prime_fifteenM_6397, prime_fifteenM_894938237, prime_fifteenM_400062744481]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fifteenM_17734003261542334012670424088 : Nat.totient 17734003261542334012670424088 = 8025409728118008654546216960 := by
  rw [← show ((([(2, 3), (11, 1), (263, 1), (1657, 1), (1696543, 1), (272571838399577, 1)] : List FactorBlock).map factorBlockValue).prod) = 17734003261542334012670424088 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fifteenM_2, prime_fifteenM_11, prime_fifteenM_263, prime_fifteenM_1657, prime_fifteenM_1696543, prime_fifteenM_272571838399577]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fifteenM_17734003261542334012670424089 : Nat.totient 17734003261542334012670424089 = 17733095268912327470225764320 := by
  rw [← show ((([(19531, 1), (619997541913, 1), (1464509982563, 1)] : List FactorBlock).map factorBlockValue).prod) = 17734003261542334012670424089 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fifteenM_19531, prime_fifteenM_619997541913, prime_fifteenM_1464509982563]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fifteenM_17734003261542334012670424090 : Nat.totient 17734003261542334012670424090 = 4717400485682981134329322752 := by
  rw [← show ((([(2, 1), (3, 2), (5, 1), (409, 1), (45127, 1), (10675900157669865007, 1)] : List FactorBlock).map factorBlockValue).prod) = 17734003261542334012670424090 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fifteenM_2, prime_fifteenM_3, prime_fifteenM_5, prime_fifteenM_409, prime_fifteenM_45127, prime_fifteenM_10675900157669865007]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fifteenM_17734003261542334012670424091 : Nat.totient 17734003261542334012670424091 = 13925624367180838344544512000 := by
  rw [← show ((([(7, 1), (13, 1), (151, 1), (1093, 1), (9380931121, 1), (125870029867, 1)] : List FactorBlock).map factorBlockValue).prod) = 17734003261542334012670424091 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fifteenM_7, prime_fifteenM_13, prime_fifteenM_151, prime_fifteenM_1093, prime_fifteenM_9380931121, prime_fifteenM_125870029867]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fifteenM_17734003261542334012670424092 : Nat.totient 17734003261542334012670424092 = 8481479820737638006059768000 := by
  rw [← show ((([(2, 2), (23, 1), (192760905016764500137722001, 1)] : List FactorBlock).map factorBlockValue).prod) = 17734003261542334012670424092 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fifteenM_2, prime_fifteenM_23, prime_fifteenM_192760905016764500137722001]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

theorem freeKill_64FifteenM : certifiedKill 1 17734003261542334012670423993 98 := by
  norm_num [certifiedKill, windowDiscrepancy, Finset.sum_range_succ,
    phi_fifteenM_17734003261542334012670423994, phi_fifteenM_17734003261542334012670423995, phi_fifteenM_17734003261542334012670423996,
    phi_fifteenM_17734003261542334012670423997, phi_fifteenM_17734003261542334012670423998, phi_fifteenM_17734003261542334012670423999,
    phi_fifteenM_17734003261542334012670424000, phi_fifteenM_17734003261542334012670424001, phi_fifteenM_17734003261542334012670424002,
    phi_fifteenM_17734003261542334012670424003, phi_fifteenM_17734003261542334012670424004, phi_fifteenM_17734003261542334012670424005,
    phi_fifteenM_17734003261542334012670424006, phi_fifteenM_17734003261542334012670424007, phi_fifteenM_17734003261542334012670424008,
    phi_fifteenM_17734003261542334012670424009, phi_fifteenM_17734003261542334012670424010, phi_fifteenM_17734003261542334012670424011,
    phi_fifteenM_17734003261542334012670424012, phi_fifteenM_17734003261542334012670424013, phi_fifteenM_17734003261542334012670424014,
    phi_fifteenM_17734003261542334012670424015, phi_fifteenM_17734003261542334012670424016, phi_fifteenM_17734003261542334012670424017,
    phi_fifteenM_17734003261542334012670424018, phi_fifteenM_17734003261542334012670424019, phi_fifteenM_17734003261542334012670424020,
    phi_fifteenM_17734003261542334012670424021, phi_fifteenM_17734003261542334012670424022, phi_fifteenM_17734003261542334012670424023,
    phi_fifteenM_17734003261542334012670424024, phi_fifteenM_17734003261542334012670424025, phi_fifteenM_17734003261542334012670424026,
    phi_fifteenM_17734003261542334012670424027, phi_fifteenM_17734003261542334012670424028, phi_fifteenM_17734003261542334012670424029,
    phi_fifteenM_17734003261542334012670424030, phi_fifteenM_17734003261542334012670424031, phi_fifteenM_17734003261542334012670424032,
    phi_fifteenM_17734003261542334012670424033, phi_fifteenM_17734003261542334012670424034, phi_fifteenM_17734003261542334012670424035,
    phi_fifteenM_17734003261542334012670424036, phi_fifteenM_17734003261542334012670424037, phi_fifteenM_17734003261542334012670424038,
    phi_fifteenM_17734003261542334012670424039, phi_fifteenM_17734003261542334012670424040, phi_fifteenM_17734003261542334012670424041,
    phi_fifteenM_17734003261542334012670424042, phi_fifteenM_17734003261542334012670424043, phi_fifteenM_17734003261542334012670424044,
    phi_fifteenM_17734003261542334012670424045, phi_fifteenM_17734003261542334012670424046, phi_fifteenM_17734003261542334012670424047,
    phi_fifteenM_17734003261542334012670424048, phi_fifteenM_17734003261542334012670424049, phi_fifteenM_17734003261542334012670424050,
    phi_fifteenM_17734003261542334012670424051, phi_fifteenM_17734003261542334012670424052, phi_fifteenM_17734003261542334012670424053,
    phi_fifteenM_17734003261542334012670424054, phi_fifteenM_17734003261542334012670424055, phi_fifteenM_17734003261542334012670424056,
    phi_fifteenM_17734003261542334012670424057, phi_fifteenM_17734003261542334012670424058, phi_fifteenM_17734003261542334012670424059,
    phi_fifteenM_17734003261542334012670424060, phi_fifteenM_17734003261542334012670424061, phi_fifteenM_17734003261542334012670424062,
    phi_fifteenM_17734003261542334012670424063, phi_fifteenM_17734003261542334012670424064, phi_fifteenM_17734003261542334012670424065,
    phi_fifteenM_17734003261542334012670424066, phi_fifteenM_17734003261542334012670424067, phi_fifteenM_17734003261542334012670424068,
    phi_fifteenM_17734003261542334012670424069, phi_fifteenM_17734003261542334012670424070, phi_fifteenM_17734003261542334012670424071,
    phi_fifteenM_17734003261542334012670424072, phi_fifteenM_17734003261542334012670424073, phi_fifteenM_17734003261542334012670424074,
    phi_fifteenM_17734003261542334012670424075, phi_fifteenM_17734003261542334012670424076, phi_fifteenM_17734003261542334012670424077,
    phi_fifteenM_17734003261542334012670424078, phi_fifteenM_17734003261542334012670424079, phi_fifteenM_17734003261542334012670424080,
    phi_fifteenM_17734003261542334012670424081, phi_fifteenM_17734003261542334012670424082, phi_fifteenM_17734003261542334012670424083,
    phi_fifteenM_17734003261542334012670424084, phi_fifteenM_17734003261542334012670424085, phi_fifteenM_17734003261542334012670424086,
    phi_fifteenM_17734003261542334012670424087, phi_fifteenM_17734003261542334012670424088, phi_fifteenM_17734003261542334012670424089,
    phi_fifteenM_17734003261542334012670424090, phi_fifteenM_17734003261542334012670424091, phi_fifteenM_17734003261542334012670424092]

end TotientTailPeriodKiller
end Erdos249257
