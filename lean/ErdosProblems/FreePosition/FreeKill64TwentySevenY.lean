import Erdos249257.DiagonalPincerCertificatesT64

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

private def twentySevenYFastPow {M : Type*} [Monoid M] (a : M) (n : ℕ) : M :=
  Nat.binaryRec 1 (fun b _ r => if b then r * r * a else r * r) n

private theorem twentySevenYFastPow_eq_pow {M : Type*} [Monoid M] (a : M) (n : ℕ) :
    twentySevenYFastPow a n = a ^ n := by
  induction n using Nat.binaryRec with
  | zero => simp [twentySevenYFastPow, Nat.binaryRec_zero]
  | bit b n ih =>
      rw [twentySevenYFastPow, Nat.binaryRec_eq b n (by left; simp)]
      change (if b then twentySevenYFastPow a n * twentySevenYFastPow a n * a
        else twentySevenYFastPow a n * twentySevenYFastPow a n) = _
      rw [ih]
      cases b <;> simp [Nat.bit, two_mul, pow_add]

private theorem prime_twentySevenY_3 : Nat.Prime 3 := by norm_num
private theorem prime_twentySevenY_3923 : Nat.Prime 3923 := by norm_num
private theorem prime_twentySevenY_8197093 : Nat.Prime 8197093 := by norm_num
private theorem prime_twentySevenY_2 : Nat.Prime 2 := by norm_num
private theorem prime_twentySevenY_5 : Nat.Prime 5 := by norm_num
private theorem prime_twentySevenY_7 : Nat.Prime 7 := by norm_num
private theorem prime_twentySevenY_11 : Nat.Prime 11 := by norm_num
private theorem prime_twentySevenY_149 : Nat.Prime 149 := by norm_num
private theorem prime_twentySevenY_929 : Nat.Prime 929 := by norm_num
private theorem prime_twentySevenY_1796567 : Nat.Prime 1796567 := by norm_num
private theorem prime_twentySevenY_110295707065568641 : Nat.Prime 110295707065568641 := by
  apply lucas_primality 110295707065568641 (26 : ZMod 110295707065568641)
  · rw [← twentySevenYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 7), (3, 2), (5, 1), (7, 1), (11, 1), (149, 1), (929, 1), (1796567, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 7), (3, 2), (5, 1), (7, 1), (11, 1), (149, 1), (929, 1), (1796567, 1)] : List FactorBlock).map factorBlockValue).prod = 110295707065568641 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_twentySevenY_2
      · exact prime_twentySevenY_3
      · exact prime_twentySevenY_5
      · exact prime_twentySevenY_7
      · exact prime_twentySevenY_11
      · exact prime_twentySevenY_149
      · exact prime_twentySevenY_929
      · exact prime_twentySevenY_1796567
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (26 : ZMod 110295707065568641) ^ 55147853532784320 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (26 : ZMod 110295707065568641) ^ 36765235688522880 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (26 : ZMod 110295707065568641) ^ 22059141413113728 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (26 : ZMod 110295707065568641) ^ 15756529580795520 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (26 : ZMod 110295707065568641) ^ 10026882460506240 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (26 : ZMod 110295707065568641) ^ 740239644735360 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (26 : ZMod 110295707065568641) ^ 118725195980160 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (26 : ZMod 110295707065568641) ^ 61392481920 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide

private theorem prime_twentySevenY_137 : Nat.Prime 137 := by norm_num
private theorem prime_twentySevenY_457 : Nat.Prime 457 := by norm_num
private theorem prime_twentySevenY_7243 : Nat.Prime 7243 := by norm_num
private theorem prime_twentySevenY_17881 : Nat.Prime 17881 := by norm_num
private theorem prime_twentySevenY_12439517 : Nat.Prime 12439517 := by norm_num
private theorem prime_twentySevenY_883 : Nat.Prime 883 := by norm_num
private theorem prime_twentySevenY_39558401 : Nat.Prime 39558401 := by
  apply lucas_primality 39558401 (3 : ZMod 39558401)
  · rw [← twentySevenYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 8), (5, 2), (7, 1), (883, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 8), (5, 2), (7, 1), (883, 1)] : List FactorBlock).map factorBlockValue).prod = 39558401 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentySevenY_2
      · exact prime_twentySevenY_5
      · exact prime_twentySevenY_7
      · exact prime_twentySevenY_883
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 39558401) ^ 19779200 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (3 : ZMod 39558401) ^ 7911680 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (3 : ZMod 39558401) ^ 5651200 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (3 : ZMod 39558401) ^ 44800 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide

private theorem prime_twentySevenY_199 : Nat.Prime 199 := by norm_num
private theorem prime_twentySevenY_15739 : Nat.Prime 15739 := by norm_num
private theorem prime_twentySevenY_74093 : Nat.Prime 74093 := by norm_num
private theorem prime_twentySevenY_167 : Nat.Prime 167 := by norm_num
private theorem prime_twentySevenY_223 : Nat.Prime 223 := by norm_num
private theorem prime_twentySevenY_1801 : Nat.Prime 1801 := by norm_num
private theorem prime_twentySevenY_904261 : Nat.Prime 904261 := by norm_num
private theorem prime_twentySevenY_29314333099 : Nat.Prime 29314333099 := by
  apply lucas_primality 29314333099 (2 : ZMod 29314333099)
  · rw [← twentySevenYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 2), (1801, 1), (904261, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 2), (1801, 1), (904261, 1)] : List FactorBlock).map factorBlockValue).prod = 29314333099 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentySevenY_2
      · exact prime_twentySevenY_3
      · exact prime_twentySevenY_1801
      · exact prime_twentySevenY_904261
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 29314333099) ^ 14657166549 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (2 : ZMod 29314333099) ^ 9771444366 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (2 : ZMod 29314333099) ^ 16276698 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (2 : ZMod 29314333099) ^ 32418 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide

private theorem prime_twentySevenY_19650511420917463 : Nat.Prime 19650511420917463 := by
  apply lucas_primality 19650511420917463 (3 : ZMod 19650511420917463)
  · rw [← twentySevenYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 2), (167, 1), (223, 1), (29314333099, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 2), (167, 1), (223, 1), (29314333099, 1)] : List FactorBlock).map factorBlockValue).prod = 19650511420917463 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentySevenY_2
      · exact prime_twentySevenY_3
      · exact prime_twentySevenY_167
      · exact prime_twentySevenY_223
      · exact prime_twentySevenY_29314333099
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 19650511420917463) ^ 9825255710458731 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (3 : ZMod 19650511420917463) ^ 6550170473639154 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (3 : ZMod 19650511420917463) ^ 117667733059386 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (3 : ZMod 19650511420917463) ^ 88118885295594 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (3 : ZMod 19650511420917463) ^ 670338 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide

private theorem prime_twentySevenY_79 : Nat.Prime 79 := by norm_num
private theorem prime_twentySevenY_189067 : Nat.Prime 189067 := by norm_num
private theorem prime_twentySevenY_2202311 : Nat.Prime 2202311 := by norm_num
private theorem prime_twentySevenY_43 : Nat.Prime 43 := by norm_num
private theorem prime_twentySevenY_47 : Nat.Prime 47 := by norm_num
private theorem prime_twentySevenY_877 : Nat.Prime 877 := by norm_num
private theorem prime_twentySevenY_13751 : Nat.Prime 13751 := by norm_num
private theorem prime_twentySevenY_161735950924213 : Nat.Prime 161735950924213 := by
  apply lucas_primality 161735950924213 (2 : ZMod 161735950924213)
  · rw [← twentySevenYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (7, 1), (43, 1), (47, 1), (79, 1), (877, 1), (13751, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (7, 1), (43, 1), (47, 1), (79, 1), (877, 1), (13751, 1)] : List FactorBlock).map factorBlockValue).prod = 161735950924213 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_twentySevenY_2
      · exact prime_twentySevenY_3
      · exact prime_twentySevenY_7
      · exact prime_twentySevenY_43
      · exact prime_twentySevenY_47
      · exact prime_twentySevenY_79
      · exact prime_twentySevenY_877
      · exact prime_twentySevenY_13751
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 161735950924213) ^ 80867975462106 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (2 : ZMod 161735950924213) ^ 53911983641404 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (2 : ZMod 161735950924213) ^ 23105135846316 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (2 : ZMod 161735950924213) ^ 3761301184284 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (2 : ZMod 161735950924213) ^ 3441190445196 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (2 : ZMod 161735950924213) ^ 2047290518028 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (2 : ZMod 161735950924213) ^ 184419556356 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (2 : ZMod 161735950924213) ^ 11761759212 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide

private theorem prime_twentySevenY_521 : Nat.Prime 521 := by norm_num
private theorem prime_twentySevenY_2689 : Nat.Prime 2689 := by norm_num
private theorem prime_twentySevenY_17 : Nat.Prime 17 := by norm_num
private theorem prime_twentySevenY_41 : Nat.Prime 41 := by norm_num
private theorem prime_twentySevenY_13 : Nat.Prime 13 := by norm_num
private theorem prime_twentySevenY_3163 : Nat.Prime 3163 := by norm_num
private theorem prime_twentySevenY_55889 : Nat.Prime 55889 := by norm_num
private theorem prime_twentySevenY_197176393 : Nat.Prime 197176393 := by
  apply lucas_primality 197176393 (5 : ZMod 197176393)
  · rw [← twentySevenYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (3, 2), (7, 2), (55889, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (3, 2), (7, 2), (55889, 1)] : List FactorBlock).map factorBlockValue).prod = 197176393 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentySevenY_2
      · exact prime_twentySevenY_3
      · exact prime_twentySevenY_7
      · exact prime_twentySevenY_55889
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 197176393) ^ 98588196 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (5 : ZMod 197176393) ^ 65725464 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (5 : ZMod 197176393) ^ 28168056 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (5 : ZMod 197176393) ^ 3528 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide

private theorem prime_twentySevenY_3154822289 : Nat.Prime 3154822289 := by
  apply lucas_primality 3154822289 (3 : ZMod 3154822289)
  · rw [← twentySevenYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 4), (197176393, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 4), (197176393, 1)] : List FactorBlock).map factorBlockValue).prod = 3154822289 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_twentySevenY_2
      · exact prime_twentySevenY_197176393
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 3154822289) ^ 1577411144 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (3 : ZMod 3154822289) ^ 16 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide

private theorem prime_twentySevenY_199574058002141 : Nat.Prime 199574058002141 := by
  apply lucas_primality 199574058002141 (3 : ZMod 199574058002141)
  · rw [← twentySevenYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (5, 1), (3163, 1), (3154822289, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (5, 1), (3163, 1), (3154822289, 1)] : List FactorBlock).map factorBlockValue).prod = 199574058002141 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentySevenY_2
      · exact prime_twentySevenY_5
      · exact prime_twentySevenY_3163
      · exact prime_twentySevenY_3154822289
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 199574058002141) ^ 99787029001070 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (3 : ZMod 199574058002141) ^ 39914811600428 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (3 : ZMod 199574058002141) ^ 63096445780 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (3 : ZMod 199574058002141) ^ 63260 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide

private theorem prime_twentySevenY_217934871338337973 : Nat.Prime 217934871338337973 := by
  apply lucas_primality 217934871338337973 (5 : ZMod 217934871338337973)
  · rw [← twentySevenYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (7, 1), (13, 1), (199574058002141, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (7, 1), (13, 1), (199574058002141, 1)] : List FactorBlock).map factorBlockValue).prod = 217934871338337973 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentySevenY_2
      · exact prime_twentySevenY_3
      · exact prime_twentySevenY_7
      · exact prime_twentySevenY_13
      · exact prime_twentySevenY_199574058002141
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 217934871338337973) ^ 108967435669168986 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (5 : ZMod 217934871338337973) ^ 72644957112779324 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (5 : ZMod 217934871338337973) ^ 31133553048333996 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (5 : ZMod 217934871338337973) ^ 16764220872179844 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (5 : ZMod 217934871338337973) ^ 1092 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide

private theorem prime_twentySevenY_4557018159684647015431 : Nat.Prime 4557018159684647015431 := by
  apply lucas_primality 4557018159684647015431 (3 : ZMod 4557018159684647015431)
  · rw [← twentySevenYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (5, 1), (17, 1), (41, 1), (217934871338337973, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (5, 1), (17, 1), (41, 1), (217934871338337973, 1)] : List FactorBlock).map factorBlockValue).prod = 4557018159684647015431 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_twentySevenY_2
      · exact prime_twentySevenY_3
      · exact prime_twentySevenY_5
      · exact prime_twentySevenY_17
      · exact prime_twentySevenY_41
      · exact prime_twentySevenY_217934871338337973
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 4557018159684647015431) ^ 2278509079842323507715 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (3 : ZMod 4557018159684647015431) ^ 1519006053228215671810 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (3 : ZMod 4557018159684647015431) ^ 911403631936929403086 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (3 : ZMod 4557018159684647015431) ^ 268059891746155706790 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (3 : ZMod 4557018159684647015431) ^ 111146784382552366230 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (3 : ZMod 4557018159684647015431) ^ 20910 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide

private theorem prime_twentySevenY_5981 : Nat.Prime 5981 := by norm_num
private theorem prime_twentySevenY_9001 : Nat.Prime 9001 := by norm_num
private theorem prime_twentySevenY_9187 : Nat.Prime 9187 := by norm_num
private theorem prime_twentySevenY_61 : Nat.Prime 61 := by norm_num
private theorem prime_twentySevenY_197 : Nat.Prime 197 := by norm_num
private theorem prime_twentySevenY_31724881 : Nat.Prime 31724881 := by
  apply lucas_primality 31724881 (7 : ZMod 31724881)
  · rw [← twentySevenYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 4), (3, 1), (5, 1), (11, 1), (61, 1), (197, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 4), (3, 1), (5, 1), (11, 1), (61, 1), (197, 1)] : List FactorBlock).map factorBlockValue).prod = 31724881 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_twentySevenY_2
      · exact prime_twentySevenY_3
      · exact prime_twentySevenY_5
      · exact prime_twentySevenY_11
      · exact prime_twentySevenY_61
      · exact prime_twentySevenY_197
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 31724881) ^ 15862440 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (7 : ZMod 31724881) ^ 10574960 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (7 : ZMod 31724881) ^ 6344976 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (7 : ZMod 31724881) ^ 2884080 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (7 : ZMod 31724881) ^ 520080 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (7 : ZMod 31724881) ^ 161040 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide

private theorem prime_twentySevenY_623291 : Nat.Prime 623291 := by norm_num
private theorem prime_twentySevenY_508605457 : Nat.Prime 508605457 := by
  apply lucas_primality 508605457 (5 : ZMod 508605457)
  · rw [← twentySevenYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 4), (3, 1), (17, 1), (623291, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 4), (3, 1), (17, 1), (623291, 1)] : List FactorBlock).map factorBlockValue).prod = 508605457 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentySevenY_2
      · exact prime_twentySevenY_3
      · exact prime_twentySevenY_17
      · exact prime_twentySevenY_623291
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 508605457) ^ 254302728 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (5 : ZMod 508605457) ^ 169535152 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (5 : ZMod 508605457) ^ 29917968 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (5 : ZMod 508605457) ^ 816 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide

private theorem prime_twentySevenY_97 : Nat.Prime 97 := by norm_num
private theorem prime_twentySevenY_36749 : Nat.Prime 36749 := by norm_num
private theorem prime_twentySevenY_8917369 : Nat.Prime 8917369 := by norm_num
private theorem prime_twentySevenY_160512643 : Nat.Prime 160512643 := by
  apply lucas_primality 160512643 (2 : ZMod 160512643)
  · rw [← twentySevenYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 2), (8917369, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 2), (8917369, 1)] : List FactorBlock).map factorBlockValue).prod = 160512643 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twentySevenY_2
      · exact prime_twentySevenY_3
      · exact prime_twentySevenY_8917369
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 160512643) ^ 80256321 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (2 : ZMod 160512643) ^ 53504214 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (2 : ZMod 160512643) ^ 18 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide

private theorem prime_twentySevenY_73 : Nat.Prime 73 := by norm_num
private theorem prime_twentySevenY_2939 : Nat.Prime 2939 := by norm_num
private theorem prime_twentySevenY_722317 : Nat.Prime 722317 := by norm_num
private theorem prime_twentySevenY_18596513447881 : Nat.Prime 18596513447881 := by
  apply lucas_primality 18596513447881 (13 : ZMod 18596513447881)
  · rw [← twentySevenYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (3, 1), (5, 1), (73, 1), (2939, 1), (722317, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (3, 1), (5, 1), (73, 1), (2939, 1), (722317, 1)] : List FactorBlock).map factorBlockValue).prod = 18596513447881 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_twentySevenY_2
      · exact prime_twentySevenY_3
      · exact prime_twentySevenY_5
      · exact prime_twentySevenY_73
      · exact prime_twentySevenY_2939
      · exact prime_twentySevenY_722317
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 18596513447881) ^ 9298256723940 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (13 : ZMod 18596513447881) ^ 6198837815960 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (13 : ZMod 18596513447881) ^ 3719302689576 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (13 : ZMod 18596513447881) ^ 254746759560 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (13 : ZMod 18596513447881) ^ 6327496920 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (13 : ZMod 18596513447881) ^ 25745640 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide

private theorem prime_twentySevenY_15960602935388100611403381599 : Nat.Prime 15960602935388100611403381599 := by
  apply lucas_primality 15960602935388100611403381599 (67 : ZMod 15960602935388100611403381599)
  · rw [← twentySevenYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5981, 1), (9001, 1), (9187, 1), (31724881, 1), (508605457, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5981, 1), (9001, 1), (9187, 1), (31724881, 1), (508605457, 1)] : List FactorBlock).map factorBlockValue).prod = 15960602935388100611403381599 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_twentySevenY_2
      · exact prime_twentySevenY_5981
      · exact prime_twentySevenY_9001
      · exact prime_twentySevenY_9187
      · exact prime_twentySevenY_31724881
      · exact prime_twentySevenY_508605457
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (67 : ZMod 15960602935388100611403381599) ^ 7980301467694050305701690799 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (67 : ZMod 15960602935388100611403381599) ^ 2668550900416000771008758 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (67 : ZMod 15960602935388100611403381599) ^ 1773203303564948406999598 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (67 : ZMod 15960602935388100611403381599) ^ 1737303029866996909916554 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (67 : ZMod 15960602935388100611403381599) ^ 503094178206313858558 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (67 : ZMod 15960602935388100611403381599) ^ 31381108314353183614 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide

private theorem prime_twentySevenY_435161 : Nat.Prime 435161 := by norm_num
private theorem prime_twentySevenY_107 : Nat.Prime 107 := by norm_num
private theorem prime_twentySevenY_14532697 : Nat.Prime 14532697 := by norm_num
private theorem prime_twentySevenY_2557 : Nat.Prime 2557 := by norm_num
private theorem prime_twentySevenY_1407877 : Nat.Prime 1407877 := by norm_num
private theorem prime_twentySevenY_86398595737 : Nat.Prime 86398595737 := by
  apply lucas_primality 86398595737 (7 : ZMod 86398595737)
  · rw [← twentySevenYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (3, 1), (2557, 1), (1407877, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (3, 1), (2557, 1), (1407877, 1)] : List FactorBlock).map factorBlockValue).prod = 86398595737 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentySevenY_2
      · exact prime_twentySevenY_3
      · exact prime_twentySevenY_2557
      · exact prime_twentySevenY_1407877
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 86398595737) ^ 43199297868 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (7 : ZMod 86398595737) ^ 28799531912 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (7 : ZMod 86398595737) ^ 33789048 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (7 : ZMod 86398595737) ^ 61368 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide

private theorem prime_twentySevenY_73354932704852229916759 : Nat.Prime 73354932704852229916759 := by
  apply lucas_primality 73354932704852229916759 (7 : ZMod 73354932704852229916759)
  · rw [← twentySevenYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (7, 1), (13, 1), (107, 1), (14532697, 1), (86398595737, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (7, 1), (13, 1), (107, 1), (14532697, 1), (86398595737, 1)] : List FactorBlock).map factorBlockValue).prod = 73354932704852229916759 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_twentySevenY_2
      · exact prime_twentySevenY_3
      · exact prime_twentySevenY_7
      · exact prime_twentySevenY_13
      · exact prime_twentySevenY_107
      · exact prime_twentySevenY_14532697
      · exact prime_twentySevenY_86398595737
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 73354932704852229916759) ^ 36677466352426114958379 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (7 : ZMod 73354932704852229916759) ^ 24451644234950743305586 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (7 : ZMod 73354932704852229916759) ^ 10479276100693175702394 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (7 : ZMod 73354932704852229916759) ^ 5642687131142479224366 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (7 : ZMod 73354932704852229916759) ^ 685560118736936728194 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (7 : ZMod 73354932704852229916759) ^ 5047578760147014 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (7 : ZMod 73354932704852229916759) ^ 849029224134 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide

private theorem prime_twentySevenY_19 : Nat.Prime 19 := by norm_num
private theorem prime_twentySevenY_23 : Nat.Prime 23 := by norm_num
private theorem prime_twentySevenY_29 : Nat.Prime 29 := by norm_num
private theorem prime_twentySevenY_31 : Nat.Prime 31 := by norm_num
private theorem prime_twentySevenY_37 : Nat.Prime 37 := by norm_num
private theorem prime_twentySevenY_53 : Nat.Prime 53 := by norm_num
private theorem prime_twentySevenY_59 : Nat.Prime 59 := by norm_num
private theorem prime_twentySevenY_227893 : Nat.Prime 227893 := by norm_num
private theorem prime_twentySevenY_4231 : Nat.Prime 4231 := by norm_num
private theorem prime_twentySevenY_183451 : Nat.Prime 183451 := by norm_num
private theorem prime_twentySevenY_64574753 : Nat.Prime 64574753 := by
  apply lucas_primality 64574753 (3 : ZMod 64574753)
  · rw [← twentySevenYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 5), (11, 1), (183451, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 5), (11, 1), (183451, 1)] : List FactorBlock).map factorBlockValue).prod = 64574753 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twentySevenY_2
      · exact prime_twentySevenY_11
      · exact prime_twentySevenY_183451
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 64574753) ^ 32287376 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (3 : ZMod 64574753) ^ 5870432 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (3 : ZMod 64574753) ^ 352 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide

private theorem prime_twentySevenY_311 : Nat.Prime 311 := by norm_num
private theorem prime_twentySevenY_1049 : Nat.Prime 1049 := by norm_num
private theorem prime_twentySevenY_1559 : Nat.Prime 1559 := by norm_num
private theorem prime_twentySevenY_6103279213 : Nat.Prime 6103279213 := by
  apply lucas_primality 6103279213 (5 : ZMod 6103279213)
  · rw [← twentySevenYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (311, 1), (1049, 1), (1559, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (311, 1), (1049, 1), (1559, 1)] : List FactorBlock).map factorBlockValue).prod = 6103279213 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentySevenY_2
      · exact prime_twentySevenY_3
      · exact prime_twentySevenY_311
      · exact prime_twentySevenY_1049
      · exact prime_twentySevenY_1559
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 6103279213) ^ 3051639606 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (5 : ZMod 6103279213) ^ 2034426404 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (5 : ZMod 6103279213) ^ 19624692 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (5 : ZMod 6103279213) ^ 5818188 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (5 : ZMod 6103279213) ^ 3914868 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide

private theorem prime_twentySevenY_140071023992734314888157 : Nat.Prime 140071023992734314888157 := by
  apply lucas_primality 140071023992734314888157 (2 : ZMod 140071023992734314888157)
  · rw [← twentySevenYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (7, 1), (4231, 1), (64574753, 1), (6103279213, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (7, 1), (4231, 1), (64574753, 1), (6103279213, 1)] : List FactorBlock).map factorBlockValue).prod = 140071023992734314888157 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_twentySevenY_2
      · exact prime_twentySevenY_3
      · exact prime_twentySevenY_7
      · exact prime_twentySevenY_4231
      · exact prime_twentySevenY_64574753
      · exact prime_twentySevenY_6103279213
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 140071023992734314888157) ^ 70035511996367157444078 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (2 : ZMod 140071023992734314888157) ^ 46690341330911438296052 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (2 : ZMod 140071023992734314888157) ^ 20010146284676330698308 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (2 : ZMod 140071023992734314888157) ^ 33105890804238788676 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (2 : ZMod 140071023992734314888157) ^ 2169129845417052 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (2 : ZMod 140071023992734314888157) ^ 22950125515212 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide

private theorem prime_twentySevenY_227 : Nat.Prime 227 := by norm_num
private theorem prime_twentySevenY_6894983 : Nat.Prime 6894983 := by norm_num
private theorem prime_twentySevenY_579178573 : Nat.Prime 579178573 := by
  apply lucas_primality 579178573 (14 : ZMod 579178573)
  · rw [← twentySevenYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (7, 1), (6894983, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (7, 1), (6894983, 1)] : List FactorBlock).map factorBlockValue).prod = 579178573 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentySevenY_2
      · exact prime_twentySevenY_3
      · exact prime_twentySevenY_7
      · exact prime_twentySevenY_6894983
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (14 : ZMod 579178573) ^ 289589286 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (14 : ZMod 579178573) ^ 193059524 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (14 : ZMod 579178573) ^ 82739796 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (14 : ZMod 579178573) ^ 84 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide

private theorem prime_twentySevenY_1032763 : Nat.Prime 1032763 := by norm_num
private theorem prime_twentySevenY_2288681 : Nat.Prime 2288681 := by norm_num
private theorem prime_twentySevenY_70909951668091 : Nat.Prime 70909951668091 := by
  apply lucas_primality 70909951668091 (10 : ZMod 70909951668091)
  · rw [← twentySevenYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (5, 1), (1032763, 1), (2288681, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (5, 1), (1032763, 1), (2288681, 1)] : List FactorBlock).map factorBlockValue).prod = 70909951668091 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentySevenY_2
      · exact prime_twentySevenY_3
      · exact prime_twentySevenY_5
      · exact prime_twentySevenY_1032763
      · exact prime_twentySevenY_2288681
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 70909951668091) ^ 35454975834045 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (10 : ZMod 70909951668091) ^ 23636650556030 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (10 : ZMod 70909951668091) ^ 14181990333618 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (10 : ZMod 70909951668091) ^ 68660430 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (10 : ZMod 70909951668091) ^ 30982890 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide

private theorem prime_twentySevenY_60698918627885897 : Nat.Prime 60698918627885897 := by
  apply lucas_primality 60698918627885897 (3 : ZMod 60698918627885897)
  · rw [← twentySevenYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (107, 1), (70909951668091, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (107, 1), (70909951668091, 1)] : List FactorBlock).map factorBlockValue).prod = 60698918627885897 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twentySevenY_2
      · exact prime_twentySevenY_107
      · exact prime_twentySevenY_70909951668091
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 60698918627885897) ^ 30349459313942948 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (3 : ZMod 60698918627885897) ^ 567279613344728 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (3 : ZMod 60698918627885897) ^ 856 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide

private theorem prime_twentySevenY_70311026147084143662569963 : Nat.Prime 70311026147084143662569963 := by
  apply lucas_primality 70311026147084143662569963 (2 : ZMod 70311026147084143662569963)
  · rw [← twentySevenYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (579178573, 1), (60698918627885897, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (579178573, 1), (60698918627885897, 1)] : List FactorBlock).map factorBlockValue).prod = 70311026147084143662569963 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twentySevenY_2
      · exact prime_twentySevenY_579178573
      · exact prime_twentySevenY_60698918627885897
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 70311026147084143662569963) ^ 35155513073542071831284981 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (2 : ZMod 70311026147084143662569963) ^ 121397837255771794 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (2 : ZMod 70311026147084143662569963) ^ 1158357146 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide

private theorem prime_twentySevenY_293 : Nat.Prime 293 := by norm_num
private theorem prime_twentySevenY_3616901 : Nat.Prime 3616901 := by norm_num
private theorem prime_twentySevenY_5004841 : Nat.Prime 5004841 := by norm_num
private theorem prime_twentySevenY_11968729 : Nat.Prime 11968729 := by norm_num
private theorem prime_twentySevenY_287249497 : Nat.Prime 287249497 := by
  apply lucas_primality 287249497 (5 : ZMod 287249497)
  · rw [← twentySevenYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (3, 1), (11968729, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (3, 1), (11968729, 1)] : List FactorBlock).map factorBlockValue).prod = 287249497 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twentySevenY_2
      · exact prime_twentySevenY_3
      · exact prime_twentySevenY_11968729
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 287249497) ^ 143624748 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (5 : ZMod 287249497) ^ 95749832 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (5 : ZMod 287249497) ^ 24 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide

private theorem prime_twentySevenY_93596301651291302272987 : Nat.Prime 93596301651291302272987 := by
  apply lucas_primality 93596301651291302272987 (2 : ZMod 93596301651291302272987)
  · rw [← twentySevenYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 2), (3616901, 1), (5004841, 1), (287249497, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 2), (3616901, 1), (5004841, 1), (287249497, 1)] : List FactorBlock).map factorBlockValue).prod = 93596301651291302272987 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentySevenY_2
      · exact prime_twentySevenY_3
      · exact prime_twentySevenY_3616901
      · exact prime_twentySevenY_5004841
      · exact prime_twentySevenY_287249497
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 93596301651291302272987) ^ 46798150825645651136493 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (2 : ZMod 93596301651291302272987) ^ 31198767217097100757662 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (2 : ZMod 93596301651291302272987) ^ 25877485076669586 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (2 : ZMod 93596301651291302272987) ^ 18701153873078346 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (2 : ZMod 93596301651291302272987) ^ 325836259519338 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide

private theorem prime_twentySevenY_36315365040701025281918957 : Nat.Prime 36315365040701025281918957 := by
  apply lucas_primality 36315365040701025281918957 (2 : ZMod 36315365040701025281918957)
  · rw [← twentySevenYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (97, 1), (93596301651291302272987, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (97, 1), (93596301651291302272987, 1)] : List FactorBlock).map factorBlockValue).prod = 36315365040701025281918957 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twentySevenY_2
      · exact prime_twentySevenY_97
      · exact prime_twentySevenY_93596301651291302272987
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 36315365040701025281918957) ^ 18157682520350512640959478 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (2 : ZMod 36315365040701025281918957) ^ 374385206605165209091948 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (2 : ZMod 36315365040701025281918957) ^ 388 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide

private theorem prime_twentySevenY_43457 : Nat.Prime 43457 := by norm_num
private theorem prime_twentySevenY_113 : Nat.Prime 113 := by norm_num
private theorem prime_twentySevenY_110261 : Nat.Prime 110261 := by norm_num
private theorem prime_twentySevenY_83 : Nat.Prime 83 := by norm_num
private theorem prime_twentySevenY_1548389 : Nat.Prime 1548389 := by norm_num
private theorem prime_twentySevenY_356129471 : Nat.Prime 356129471 := by
  apply lucas_primality 356129471 (11 : ZMod 356129471)
  · rw [← twentySevenYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 1), (23, 1), (1548389, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 1), (23, 1), (1548389, 1)] : List FactorBlock).map factorBlockValue).prod = 356129471 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentySevenY_2
      · exact prime_twentySevenY_5
      · exact prime_twentySevenY_23
      · exact prime_twentySevenY_1548389
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 356129471) ^ 178064735 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (11 : ZMod 356129471) ^ 71225894 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (11 : ZMod 356129471) ^ 15483890 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (11 : ZMod 356129471) ^ 230 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide

private theorem prime_twentySevenY_131595537606037 : Nat.Prime 131595537606037 := by
  apply lucas_primality 131595537606037 (2 : ZMod 131595537606037)
  · rw [← twentySevenYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (7, 1), (53, 1), (83, 1), (356129471, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (7, 1), (53, 1), (83, 1), (356129471, 1)] : List FactorBlock).map factorBlockValue).prod = 131595537606037 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_twentySevenY_2
      · exact prime_twentySevenY_3
      · exact prime_twentySevenY_7
      · exact prime_twentySevenY_53
      · exact prime_twentySevenY_83
      · exact prime_twentySevenY_356129471
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 131595537606037) ^ 65797768803018 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (2 : ZMod 131595537606037) ^ 43865179202012 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (2 : ZMod 131595537606037) ^ 18799362515148 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (2 : ZMod 131595537606037) ^ 2482934671812 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (2 : ZMod 131595537606037) ^ 1585488404892 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (2 : ZMod 131595537606037) ^ 369516 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide

private theorem prime_twentySevenY_183636732118969333034993 : Nat.Prime 183636732118969333034993 := by
  apply lucas_primality 183636732118969333034993 (5 : ZMod 183636732118969333034993)
  · rw [← twentySevenYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 4), (7, 1), (113, 1), (110261, 1), (131595537606037, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 4), (7, 1), (113, 1), (110261, 1), (131595537606037, 1)] : List FactorBlock).map factorBlockValue).prod = 183636732118969333034993 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentySevenY_2
      · exact prime_twentySevenY_7
      · exact prime_twentySevenY_113
      · exact prime_twentySevenY_110261
      · exact prime_twentySevenY_131595537606037
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 183636732118969333034993) ^ 91818366059484666517496 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (5 : ZMod 183636732118969333034993) ^ 26233818874138476147856 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (5 : ZMod 183636732118969333034993) ^ 1625103824061675513584 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (5 : ZMod 183636732118969333034993) ^ 1665473123942004272 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (5 : ZMod 183636732118969333034993) ^ 1395463216 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide

private theorem prime_twentySevenY_23537 : Nat.Prime 23537 := by norm_num
private theorem prime_twentySevenY_69198781 : Nat.Prime 69198781 := by
  apply lucas_primality 69198781 (13 : ZMod 69198781)
  · rw [← twentySevenYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (5, 1), (7, 2), (23537, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (5, 1), (7, 2), (23537, 1)] : List FactorBlock).map factorBlockValue).prod = 69198781 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentySevenY_2
      · exact prime_twentySevenY_3
      · exact prime_twentySevenY_5
      · exact prime_twentySevenY_7
      · exact prime_twentySevenY_23537
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 69198781) ^ 34599390 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (13 : ZMod 69198781) ^ 23066260 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (13 : ZMod 69198781) ^ 13839756 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (13 : ZMod 69198781) ^ 9885540 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (13 : ZMod 69198781) ^ 2940 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide

private theorem prime_twentySevenY_14821679 : Nat.Prime 14821679 := by norm_num
private theorem prime_twentySevenY_1613 : Nat.Prime 1613 := by norm_num
private theorem prime_twentySevenY_302460083 : Nat.Prime 302460083 := by
  apply lucas_primality 302460083 (2 : ZMod 302460083)
  · rw [← twentySevenYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (29, 1), (53, 1), (61, 1), (1613, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (29, 1), (53, 1), (61, 1), (1613, 1)] : List FactorBlock).map factorBlockValue).prod = 302460083 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentySevenY_2
      · exact prime_twentySevenY_29
      · exact prime_twentySevenY_53
      · exact prime_twentySevenY_61
      · exact prime_twentySevenY_1613
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 302460083) ^ 151230041 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (2 : ZMod 302460083) ^ 10429658 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (2 : ZMod 302460083) ^ 5706794 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (2 : ZMod 302460083) ^ 4958362 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (2 : ZMod 302460083) ^ 187514 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide

private theorem prime_twentySevenY_92259445641899967061 : Nat.Prime 92259445641899967061 := by
  apply lucas_primality 92259445641899967061 (2 : ZMod 92259445641899967061)
  · rw [← twentySevenYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (5, 1), (7, 3), (14821679, 1), (302460083, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (5, 1), (7, 3), (14821679, 1), (302460083, 1)] : List FactorBlock).map factorBlockValue).prod = 92259445641899967061 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_twentySevenY_2
      · exact prime_twentySevenY_3
      · exact prime_twentySevenY_5
      · exact prime_twentySevenY_7
      · exact prime_twentySevenY_14821679
      · exact prime_twentySevenY_302460083
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 92259445641899967061) ^ 46129722820949983530 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (2 : ZMod 92259445641899967061) ^ 30753148547299989020 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (2 : ZMod 92259445641899967061) ^ 18451889128379993412 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (2 : ZMod 92259445641899967061) ^ 13179920805985709580 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (2 : ZMod 92259445641899967061) ^ 6224628508140 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (2 : ZMod 92259445641899967061) ^ 305030153820 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide

private theorem prime_twentySevenY_2663 : Nat.Prime 2663 := by norm_num
private theorem prime_twentySevenY_9063547 : Nat.Prime 9063547 := by norm_num
private theorem prime_twentySevenY_151 : Nat.Prime 151 := by norm_num
private theorem prime_twentySevenY_211 : Nat.Prime 211 := by norm_num
private theorem prime_twentySevenY_26126021 : Nat.Prime 26126021 := by
  apply lucas_primality 26126021 (3 : ZMod 26126021)
  · rw [← twentySevenYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (5, 1), (41, 1), (151, 1), (211, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (5, 1), (41, 1), (151, 1), (211, 1)] : List FactorBlock).map factorBlockValue).prod = 26126021 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentySevenY_2
      · exact prime_twentySevenY_5
      · exact prime_twentySevenY_41
      · exact prime_twentySevenY_151
      · exact prime_twentySevenY_211
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 26126021) ^ 13063010 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (3 : ZMod 26126021) ^ 5225204 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (3 : ZMod 26126021) ^ 637220 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (3 : ZMod 26126021) ^ 173020 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (3 : ZMod 26126021) ^ 123820 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide

private theorem prime_twentySevenY_397 : Nat.Prime 397 := by norm_num
private theorem prime_twentySevenY_1213 : Nat.Prime 1213 := by norm_num
private theorem prime_twentySevenY_8436948721 : Nat.Prime 8436948721 := by
  apply lucas_primality 8436948721 (7 : ZMod 8436948721)
  · rw [← twentySevenYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 4), (3, 1), (5, 1), (73, 1), (397, 1), (1213, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 4), (3, 1), (5, 1), (73, 1), (397, 1), (1213, 1)] : List FactorBlock).map factorBlockValue).prod = 8436948721 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_twentySevenY_2
      · exact prime_twentySevenY_3
      · exact prime_twentySevenY_5
      · exact prime_twentySevenY_73
      · exact prime_twentySevenY_397
      · exact prime_twentySevenY_1213
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 8436948721) ^ 4218474360 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (7 : ZMod 8436948721) ^ 2812316240 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (7 : ZMod 8436948721) ^ 1687389744 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (7 : ZMod 8436948721) ^ 115574640 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (7 : ZMod 8436948721) ^ 21251760 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (7 : ZMod 8436948721) ^ 6955440 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide

private theorem prime_twentySevenY_1217 : Nat.Prime 1217 := by norm_num
private theorem prime_twentySevenY_14797631 : Nat.Prime 14797631 := by norm_num
private theorem prime_twentySevenY_29595263 : Nat.Prime 29595263 := by
  apply lucas_primality 29595263 (5 : ZMod 29595263)
  · rw [← twentySevenYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (14797631, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (14797631, 1)] : List FactorBlock).map factorBlockValue).prod = 29595263 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_twentySevenY_2
      · exact prime_twentySevenY_14797631
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 29595263) ^ 14797631 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (5 : ZMod 29595263) ^ 2 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide

private theorem prime_twentySevenY_216104610427 : Nat.Prime 216104610427 := by
  apply lucas_primality 216104610427 (5 : ZMod 216104610427)
  · rw [← twentySevenYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (1217, 1), (29595263, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (1217, 1), (29595263, 1)] : List FactorBlock).map factorBlockValue).prod = 216104610427 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentySevenY_2
      · exact prime_twentySevenY_3
      · exact prime_twentySevenY_1217
      · exact prime_twentySevenY_29595263
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 216104610427) ^ 108052305213 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (5 : ZMod 216104610427) ^ 72034870142 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (5 : ZMod 216104610427) ^ 177571578 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (5 : ZMod 216104610427) ^ 7302 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide

private theorem prime_twentySevenY_7481 : Nat.Prime 7481 := by norm_num
private theorem prime_twentySevenY_500000117 : Nat.Prime 500000117 := by
  apply lucas_primality 500000117 (2 : ZMod 500000117)
  · rw [← twentySevenYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (7, 2), (11, 1), (31, 1), (7481, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (7, 2), (11, 1), (31, 1), (7481, 1)] : List FactorBlock).map factorBlockValue).prod = 500000117 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentySevenY_2
      · exact prime_twentySevenY_7
      · exact prime_twentySevenY_11
      · exact prime_twentySevenY_31
      · exact prime_twentySevenY_7481
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 500000117) ^ 250000058 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (2 : ZMod 500000117) ^ 71428588 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (2 : ZMod 500000117) ^ 45454556 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (2 : ZMod 500000117) ^ 16129036 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (2 : ZMod 500000117) ^ 66836 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide

private theorem prime_twentySevenY_197212046147609 : Nat.Prime 197212046147609 := by
  apply lucas_primality 197212046147609 (3 : ZMod 197212046147609)
  · rw [← twentySevenYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (47, 1), (1049, 1), (500000117, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (47, 1), (1049, 1), (500000117, 1)] : List FactorBlock).map factorBlockValue).prod = 197212046147609 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentySevenY_2
      · exact prime_twentySevenY_47
      · exact prime_twentySevenY_1049
      · exact prime_twentySevenY_500000117
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 197212046147609) ^ 98606023073804 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (3 : ZMod 197212046147609) ^ 4196000981864 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (3 : ZMod 197212046147609) ^ 188000043992 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (3 : ZMod 197212046147609) ^ 394424 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide

private theorem prime_twentySevenY_3990150733847025152850845401 : Nat.Prime 3990150733847025152850845401 := by
  apply lucas_primality 3990150733847025152850845401 (67 : ZMod 3990150733847025152850845401)
  · rw [← twentySevenYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (3, 6), (5, 2), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (3, 6), (5, 2), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod = 3990150733847025152850845401 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_twentySevenY_2
      · exact prime_twentySevenY_3
      · exact prime_twentySevenY_5
      · exact prime_twentySevenY_7
      · exact prime_twentySevenY_11
      · exact prime_twentySevenY_13
      · exact prime_twentySevenY_17
      · exact prime_twentySevenY_19
      · exact prime_twentySevenY_23
      · exact prime_twentySevenY_29
      · exact prime_twentySevenY_31
      · exact prime_twentySevenY_37
      · exact prime_twentySevenY_41
      · exact prime_twentySevenY_43
      · exact prime_twentySevenY_47
      · exact prime_twentySevenY_53
      · exact prime_twentySevenY_59
      · exact prime_twentySevenY_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (67 : ZMod 3990150733847025152850845401) ^ 1995075366923512576425422700 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (67 : ZMod 3990150733847025152850845401) ^ 1330050244615675050950281800 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (67 : ZMod 3990150733847025152850845401) ^ 798030146769405030570169080 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (67 : ZMod 3990150733847025152850845401) ^ 570021533406717878978692200 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (67 : ZMod 3990150733847025152850845401) ^ 362740975804275013895531400 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (67 : ZMod 3990150733847025152850845401) ^ 306934671834386550219295800 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (67 : ZMod 3990150733847025152850845401) ^ 234714749049825008991226200 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (67 : ZMod 3990150733847025152850845401) ^ 210007933360369744886886600 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (67 : ZMod 3990150733847025152850845401) ^ 173484814515088050123949800 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (67 : ZMod 3990150733847025152850845401) ^ 137591404615414660443132600 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (67 : ZMod 3990150733847025152850845401) ^ 128714539801516940414543400 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (67 : ZMod 3990150733847025152850845401) ^ 107841911725595274401374200 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (67 : ZMod 3990150733847025152850845401) ^ 97320749606025003728069400 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (67 : ZMod 3990150733847025152850845401) ^ 92794203112721515182577800 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (67 : ZMod 3990150733847025152850845401) ^ 84896824124404790486188200 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (67 : ZMod 3990150733847025152850845401) ^ 75285862902774059487751800 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (67 : ZMod 3990150733847025152850845401) ^ 67629673455034324624590600 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (67 : ZMod 3990150733847025152850845401) ^ 65412307112246313981161400 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide

private theorem prime_twentySevenY_71 : Nat.Prime 71 := by norm_num
private theorem prime_twentySevenY_114593 : Nat.Prime 114593 := by norm_num
private theorem prime_twentySevenY_42857783 : Nat.Prime 42857783 := by
  apply lucas_primality 42857783 (5 : ZMod 42857783)
  · rw [← twentySevenYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (11, 1), (17, 1), (114593, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (11, 1), (17, 1), (114593, 1)] : List FactorBlock).map factorBlockValue).prod = 42857783 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentySevenY_2
      · exact prime_twentySevenY_11
      · exact prime_twentySevenY_17
      · exact prime_twentySevenY_114593
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 42857783) ^ 21428891 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (5 : ZMod 42857783) ^ 3896162 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (5 : ZMod 42857783) ^ 2521046 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (5 : ZMod 42857783) ^ 374 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide

private theorem prime_twentySevenY_30429025931 : Nat.Prime 30429025931 := by
  apply lucas_primality 30429025931 (2 : ZMod 30429025931)
  · rw [← twentySevenYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 1), (71, 1), (42857783, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 1), (71, 1), (42857783, 1)] : List FactorBlock).map factorBlockValue).prod = 30429025931 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentySevenY_2
      · exact prime_twentySevenY_5
      · exact prime_twentySevenY_71
      · exact prime_twentySevenY_42857783
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 30429025931) ^ 15214512965 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (2 : ZMod 30429025931) ^ 6085805186 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (2 : ZMod 30429025931) ^ 428577830 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (2 : ZMod 30429025931) ^ 710 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide

private theorem prime_twentySevenY_81047 : Nat.Prime 81047 := by norm_num
private theorem prime_twentySevenY_14999741 : Nat.Prime 14999741 := by norm_num
private theorem prime_twentySevenY_11655978276633277 : Nat.Prime 11655978276633277 := by
  apply lucas_primality 11655978276633277 (2 : ZMod 11655978276633277)
  · rw [← twentySevenYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (17, 1), (47, 1), (81047, 1), (14999741, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (17, 1), (47, 1), (81047, 1), (14999741, 1)] : List FactorBlock).map factorBlockValue).prod = 11655978276633277 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_twentySevenY_2
      · exact prime_twentySevenY_3
      · exact prime_twentySevenY_17
      · exact prime_twentySevenY_47
      · exact prime_twentySevenY_81047
      · exact prime_twentySevenY_14999741
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 11655978276633277) ^ 5827989138316638 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (2 : ZMod 11655978276633277) ^ 3885326092211092 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (2 : ZMod 11655978276633277) ^ 685645780978428 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (2 : ZMod 11655978276633277) ^ 247999537800708 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (2 : ZMod 11655978276633277) ^ 143817516708 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (2 : ZMod 11655978276633277) ^ 777078636 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide

private theorem prime_twentySevenY_116559782766332771 : Nat.Prime 116559782766332771 := by
  apply lucas_primality 116559782766332771 (2 : ZMod 116559782766332771)
  · rw [← twentySevenYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 1), (11655978276633277, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 1), (11655978276633277, 1)] : List FactorBlock).map factorBlockValue).prod = 116559782766332771 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twentySevenY_2
      · exact prime_twentySevenY_5
      · exact prime_twentySevenY_11655978276633277
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 116559782766332771) ^ 58279891383166385 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (2 : ZMod 116559782766332771) ^ 23311956553266554 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (2 : ZMod 116559782766332771) ^ 10 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide

private theorem prime_twentySevenY_34781 : Nat.Prime 34781 := by norm_num
private theorem prime_twentySevenY_121733501 : Nat.Prime 121733501 := by
  apply lucas_primality 121733501 (3 : ZMod 121733501)
  · rw [← twentySevenYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (5, 3), (7, 1), (34781, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (5, 3), (7, 1), (34781, 1)] : List FactorBlock).map factorBlockValue).prod = 121733501 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentySevenY_2
      · exact prime_twentySevenY_5
      · exact prime_twentySevenY_7
      · exact prime_twentySevenY_34781
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 121733501) ^ 60866750 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (3 : ZMod 121733501) ^ 24346700 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (3 : ZMod 121733501) ^ 17390500 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (3 : ZMod 121733501) ^ 3500 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide

private theorem prime_twentySevenY_4382406037 : Nat.Prime 4382406037 := by
  apply lucas_primality 4382406037 (6 : ZMod 4382406037)
  · rw [← twentySevenYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 2), (121733501, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 2), (121733501, 1)] : List FactorBlock).map factorBlockValue).prod = 4382406037 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twentySevenY_2
      · exact prime_twentySevenY_3
      · exact prime_twentySevenY_121733501
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (6 : ZMod 4382406037) ^ 2191203018 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (6 : ZMod 4382406037) ^ 1460802012 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (6 : ZMod 4382406037) ^ 36 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide

private theorem prime_twentySevenY_8171 : Nat.Prime 8171 := by norm_num
private theorem prime_twentySevenY_263899 : Nat.Prime 263899 := by norm_num
private theorem prime_twentySevenY_107022411157729 : Nat.Prime 107022411157729 := by
  apply lucas_primality 107022411157729 (19 : ZMod 107022411157729)
  · rw [← twentySevenYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 5), (3, 1), (11, 1), (47, 1), (8171, 1), (263899, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 5), (3, 1), (11, 1), (47, 1), (8171, 1), (263899, 1)] : List FactorBlock).map factorBlockValue).prod = 107022411157729 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_twentySevenY_2
      · exact prime_twentySevenY_3
      · exact prime_twentySevenY_11
      · exact prime_twentySevenY_47
      · exact prime_twentySevenY_8171
      · exact prime_twentySevenY_263899
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (19 : ZMod 107022411157729) ^ 53511205578864 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (19 : ZMod 107022411157729) ^ 35674137052576 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (19 : ZMod 107022411157729) ^ 9729310105248 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (19 : ZMod 107022411157729) ^ 2277072577824 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (19 : ZMod 107022411157729) ^ 13097835168 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (19 : ZMod 107022411157729) ^ 405543072 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide

private theorem prime_twentySevenY_38459284181658073762417787 : Nat.Prime 38459284181658073762417787 := by
  apply lucas_primality 38459284181658073762417787 (2 : ZMod 38459284181658073762417787)
  · rw [← twentySevenYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (41, 1), (4382406037, 1), (107022411157729, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (41, 1), (4382406037, 1), (107022411157729, 1)] : List FactorBlock).map factorBlockValue).prod = 38459284181658073762417787 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentySevenY_2
      · exact prime_twentySevenY_41
      · exact prime_twentySevenY_4382406037
      · exact prime_twentySevenY_107022411157729
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 38459284181658073762417787) ^ 19229642090829036881208893 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (2 : ZMod 38459284181658073762417787) ^ 938031321503855457619946 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (2 : ZMod 38459284181658073762417787) ^ 8775837714933778 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (2 : ZMod 38459284181658073762417787) ^ 359357295034 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide

private theorem prime_twentySevenY_701 : Nat.Prime 701 := by norm_num
private theorem prime_twentySevenY_1686677 : Nat.Prime 1686677 := by norm_num
private theorem prime_twentySevenY_13313779 : Nat.Prime 13313779 := by norm_num
private theorem prime_twentySevenY_3947 : Nat.Prime 3947 := by norm_num
private theorem prime_twentySevenY_864917 : Nat.Prime 864917 := by norm_num
private theorem prime_twentySevenY_184346679547 : Nat.Prime 184346679547 := by
  apply lucas_primality 184346679547 (2 : ZMod 184346679547)
  · rw [← twentySevenYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 3), (3947, 1), (864917, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 3), (3947, 1), (864917, 1)] : List FactorBlock).map factorBlockValue).prod = 184346679547 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentySevenY_2
      · exact prime_twentySevenY_3
      · exact prime_twentySevenY_3947
      · exact prime_twentySevenY_864917
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 184346679547) ^ 92173339773 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (2 : ZMod 184346679547) ^ 61448893182 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (2 : ZMod 184346679547) ^ 46705518 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (2 : ZMod 184346679547) ^ 213138 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide

private theorem prime_twentySevenY_3137 : Nat.Prime 3137 := by norm_num
private theorem prime_twentySevenY_19309 : Nat.Prime 19309 := by norm_num
private theorem prime_twentySevenY_821 : Nat.Prime 821 := by norm_num
private theorem prime_twentySevenY_5437 : Nat.Prime 5437 := by norm_num
private theorem prime_twentySevenY_14347 : Nat.Prime 14347 := by norm_num
private theorem prime_twentySevenY_312018557 : Nat.Prime 312018557 := by
  apply lucas_primality 312018557 (2 : ZMod 312018557)
  · rw [← twentySevenYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (5437, 1), (14347, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (5437, 1), (14347, 1)] : List FactorBlock).map factorBlockValue).prod = 312018557 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twentySevenY_2
      · exact prime_twentySevenY_5437
      · exact prime_twentySevenY_14347
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 312018557) ^ 156009278 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (2 : ZMod 312018557) ^ 57388 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (2 : ZMod 312018557) ^ 21748 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide

private theorem prime_twentySevenY_4368259799 : Nat.Prime 4368259799 := by
  apply lucas_primality 4368259799 (7 : ZMod 4368259799)
  · rw [← twentySevenYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (7, 1), (312018557, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (7, 1), (312018557, 1)] : List FactorBlock).map factorBlockValue).prod = 4368259799 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twentySevenY_2
      · exact prime_twentySevenY_7
      · exact prime_twentySevenY_312018557
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 4368259799) ^ 2184129899 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (7 : ZMod 4368259799) ^ 624037114 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (7 : ZMod 4368259799) ^ 14 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide

private theorem prime_twentySevenY_52419117589 : Nat.Prime 52419117589 := by
  apply lucas_primality 52419117589 (2 : ZMod 52419117589)
  · rw [← twentySevenYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (4368259799, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (4368259799, 1)] : List FactorBlock).map factorBlockValue).prod = 52419117589 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twentySevenY_2
      · exact prime_twentySevenY_3
      · exact prime_twentySevenY_4368259799
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 52419117589) ^ 26209558794 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (2 : ZMod 52419117589) ^ 17473039196 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (2 : ZMod 52419117589) ^ 12 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide

private theorem prime_twentySevenY_13372745926364969 : Nat.Prime 13372745926364969 := by
  apply lucas_primality 13372745926364969 (3 : ZMod 13372745926364969)
  · rw [← twentySevenYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (11, 1), (13, 1), (223, 1), (52419117589, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (11, 1), (13, 1), (223, 1), (52419117589, 1)] : List FactorBlock).map factorBlockValue).prod = 13372745926364969 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentySevenY_2
      · exact prime_twentySevenY_11
      · exact prime_twentySevenY_13
      · exact prime_twentySevenY_223
      · exact prime_twentySevenY_52419117589
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 13372745926364969) ^ 6686372963182484 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (3 : ZMod 13372745926364969) ^ 1215704175124088 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (3 : ZMod 13372745926364969) ^ 1028672763566536 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (3 : ZMod 13372745926364969) ^ 59967470521816 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (3 : ZMod 13372745926364969) ^ 255112 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide

private theorem prime_twentySevenY_43916097622182558197 : Nat.Prime 43916097622182558197 := by
  apply lucas_primality 43916097622182558197 (2 : ZMod 43916097622182558197)
  · rw [← twentySevenYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (821, 1), (13372745926364969, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (821, 1), (13372745926364969, 1)] : List FactorBlock).map factorBlockValue).prod = 43916097622182558197 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twentySevenY_2
      · exact prime_twentySevenY_821
      · exact prime_twentySevenY_13372745926364969
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 43916097622182558197) ^ 21958048811091279098 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (2 : ZMod 43916097622182558197) ^ 53490983705459876 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (2 : ZMod 43916097622182558197) ^ 3284 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide

private theorem prime_twentySevenY_233 : Nat.Prime 233 := by norm_num
private theorem prime_twentySevenY_25903 : Nat.Prime 25903 := by norm_num
private theorem prime_twentySevenY_181 : Nat.Prime 181 := by norm_num
private theorem prime_twentySevenY_6983 : Nat.Prime 6983 := by norm_num
private theorem prime_twentySevenY_614266579 : Nat.Prime 614266579 := by
  apply lucas_primality 614266579 (3 : ZMod 614266579)
  · rw [← twentySevenYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 5), (181, 1), (6983, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 5), (181, 1), (6983, 1)] : List FactorBlock).map factorBlockValue).prod = 614266579 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentySevenY_2
      · exact prime_twentySevenY_3
      · exact prime_twentySevenY_181
      · exact prime_twentySevenY_6983
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 614266579) ^ 307133289 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (3 : ZMod 614266579) ^ 204755526 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (3 : ZMod 614266579) ^ 3393738 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (3 : ZMod 614266579) ^ 87966 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide

private theorem prime_twentySevenY_4175827 : Nat.Prime 4175827 := by norm_num
private theorem prime_twentySevenY_2129671771 : Nat.Prime 2129671771 := by
  apply lucas_primality 2129671771 (22 : ZMod 2129671771)
  · rw [← twentySevenYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (5, 1), (17, 1), (4175827, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (5, 1), (17, 1), (4175827, 1)] : List FactorBlock).map factorBlockValue).prod = 2129671771 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentySevenY_2
      · exact prime_twentySevenY_3
      · exact prime_twentySevenY_5
      · exact prime_twentySevenY_17
      · exact prime_twentySevenY_4175827
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (22 : ZMod 2129671771) ^ 1064835885 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (22 : ZMod 2129671771) ^ 709890590 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (22 : ZMod 2129671771) ^ 425934354 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (22 : ZMod 2129671771) ^ 125274810 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (22 : ZMod 2129671771) ^ 510 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide

private theorem prime_twentySevenY_127 : Nat.Prime 127 := by norm_num
private theorem prime_twentySevenY_186481 : Nat.Prime 186481 := by norm_num
private theorem prime_twentySevenY_16767625597 : Nat.Prime 16767625597 := by
  apply lucas_primality 16767625597 (6 : ZMod 16767625597)
  · rw [← twentySevenYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (59, 1), (127, 1), (186481, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (59, 1), (127, 1), (186481, 1)] : List FactorBlock).map factorBlockValue).prod = 16767625597 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentySevenY_2
      · exact prime_twentySevenY_3
      · exact prime_twentySevenY_59
      · exact prime_twentySevenY_127
      · exact prime_twentySevenY_186481
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 16767625597) ^ 8383812798 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (6 : ZMod 16767625597) ^ 5589208532 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (6 : ZMod 16767625597) ^ 284197044 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (6 : ZMod 16767625597) ^ 132028548 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (6 : ZMod 16767625597) ^ 89916 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide

private theorem prime_twentySevenY_471217 : Nat.Prime 471217 := by norm_num
private theorem prime_twentySevenY_1922603 : Nat.Prime 1922603 := by norm_num
private theorem prime_twentySevenY_407591837 : Nat.Prime 407591837 := by
  apply lucas_primality 407591837 (2 : ZMod 407591837)
  · rw [← twentySevenYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (53, 1), (1922603, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (53, 1), (1922603, 1)] : List FactorBlock).map factorBlockValue).prod = 407591837 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twentySevenY_2
      · exact prime_twentySevenY_53
      · exact prime_twentySevenY_1922603
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 407591837) ^ 203795918 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (2 : ZMod 407591837) ^ 7690412 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (2 : ZMod 407591837) ^ 212 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide

private theorem prime_twentySevenY_135981455480185333 : Nat.Prime 135981455480185333 := by
  apply lucas_primality 135981455480185333 (6 : ZMod 135981455480185333)
  · rw [← twentySevenYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (59, 1), (471217, 1), (407591837, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (59, 1), (471217, 1), (407591837, 1)] : List FactorBlock).map factorBlockValue).prod = 135981455480185333 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentySevenY_2
      · exact prime_twentySevenY_3
      · exact prime_twentySevenY_59
      · exact prime_twentySevenY_471217
      · exact prime_twentySevenY_407591837
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 135981455480185333) ^ 67990727740092666 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (6 : ZMod 135981455480185333) ^ 45327151826728444 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (6 : ZMod 135981455480185333) ^ 2304770431867548 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (6 : ZMod 135981455480185333) ^ 288575020596 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (6 : ZMod 135981455480185333) ^ 333621636 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide

private theorem prime_twentySevenY_3181 : Nat.Prime 3181 := by norm_num
private theorem prime_twentySevenY_73571 : Nat.Prime 73571 := by norm_num
private theorem prime_twentySevenY_455881 : Nat.Prime 455881 := by norm_num
private theorem prime_twentySevenY_7524701 : Nat.Prime 7524701 := by norm_num
private theorem prime_twentySevenY_8487862729 : Nat.Prime 8487862729 := by
  apply lucas_primality 8487862729 (7 : ZMod 8487862729)
  · rw [← twentySevenYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (3, 1), (47, 1), (7524701, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (3, 1), (47, 1), (7524701, 1)] : List FactorBlock).map factorBlockValue).prod = 8487862729 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentySevenY_2
      · exact prime_twentySevenY_3
      · exact prime_twentySevenY_47
      · exact prime_twentySevenY_7524701
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 8487862729) ^ 4243931364 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (7 : ZMod 8487862729) ^ 2829287576 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (7 : ZMod 8487862729) ^ 180592824 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (7 : ZMod 8487862729) ^ 1128 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide

private theorem prime_twentySevenY_19946477413151 : Nat.Prime 19946477413151 := by
  apply lucas_primality 19946477413151 (11 : ZMod 19946477413151)
  · rw [← twentySevenYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 2), (47, 1), (8487862729, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 2), (47, 1), (8487862729, 1)] : List FactorBlock).map factorBlockValue).prod = 19946477413151 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentySevenY_2
      · exact prime_twentySevenY_5
      · exact prime_twentySevenY_47
      · exact prime_twentySevenY_8487862729
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 19946477413151) ^ 9973238706575 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (11 : ZMod 19946477413151) ^ 3989295482630 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (11 : ZMod 19946477413151) ^ 424393136450 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (11 : ZMod 19946477413151) ^ 2350 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide

private theorem prime_twentySevenY_2521 : Nat.Prime 2521 := by norm_num
private theorem prime_twentySevenY_2591 : Nat.Prime 2591 := by norm_num
private theorem prime_twentySevenY_342553 : Nat.Prime 342553 := by norm_num
private theorem prime_twentySevenY_1255693 : Nat.Prime 1255693 := by norm_num
private theorem prime_twentySevenY_15887027837 : Nat.Prime 15887027837 := by
  apply lucas_primality 15887027837 (2 : ZMod 15887027837)
  · rw [← twentySevenYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3163, 1), (1255693, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3163, 1), (1255693, 1)] : List FactorBlock).map factorBlockValue).prod = 15887027837 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twentySevenY_2
      · exact prime_twentySevenY_3163
      · exact prime_twentySevenY_1255693
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 15887027837) ^ 7943513918 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (2 : ZMod 15887027837) ^ 5022772 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (2 : ZMod 15887027837) ^ 12652 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide

private theorem prime_twentySevenY_571933002133 : Nat.Prime 571933002133 := by
  apply lucas_primality 571933002133 (2 : ZMod 571933002133)
  · rw [← twentySevenYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 2), (15887027837, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 2), (15887027837, 1)] : List FactorBlock).map factorBlockValue).prod = 571933002133 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twentySevenY_2
      · exact prime_twentySevenY_3
      · exact prime_twentySevenY_15887027837
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 571933002133) ^ 285966501066 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (2 : ZMod 571933002133) ^ 190644334044 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (2 : ZMod 571933002133) ^ 36 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide

private theorem prime_twentySevenY_6257 : Nat.Prime 6257 := by norm_num
private theorem prime_twentySevenY_4091 : Nat.Prime 4091 := by norm_num
private theorem prime_twentySevenY_12289 : Nat.Prime 12289 := by norm_num
private theorem prime_twentySevenY_127997 : Nat.Prime 127997 := by norm_num
private theorem prime_twentySevenY_254818731547 : Nat.Prime 254818731547 := by
  apply lucas_primality 254818731547 (2 : ZMod 254818731547)
  · rw [← twentySevenYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 4), (12289, 1), (127997, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 4), (12289, 1), (127997, 1)] : List FactorBlock).map factorBlockValue).prod = 254818731547 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentySevenY_2
      · exact prime_twentySevenY_3
      · exact prime_twentySevenY_12289
      · exact prime_twentySevenY_127997
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 254818731547) ^ 127409365773 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (2 : ZMod 254818731547) ^ 84939577182 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (2 : ZMod 254818731547) ^ 20735514 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (2 : ZMod 254818731547) ^ 1990818 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide

private theorem prime_twentySevenY_99668269744904299 : Nat.Prime 99668269744904299 := by
  apply lucas_primality 99668269744904299 (2 : ZMod 99668269744904299)
  · rw [← twentySevenYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (19, 1), (47, 1), (73, 1), (254818731547, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (19, 1), (47, 1), (73, 1), (254818731547, 1)] : List FactorBlock).map factorBlockValue).prod = 99668269744904299 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_twentySevenY_2
      · exact prime_twentySevenY_3
      · exact prime_twentySevenY_19
      · exact prime_twentySevenY_47
      · exact prime_twentySevenY_73
      · exact prime_twentySevenY_254818731547
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 99668269744904299) ^ 49834134872452149 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (2 : ZMod 99668269744904299) ^ 33222756581634766 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (2 : ZMod 99668269744904299) ^ 5245698407626542 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (2 : ZMod 99668269744904299) ^ 2120601483934134 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (2 : ZMod 99668269744904299) ^ 1365318763628826 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (2 : ZMod 99668269744904299) ^ 391134 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide

private theorem prime_twentySevenY_815485783052806974419 : Nat.Prime 815485783052806974419 := by
  apply lucas_primality 815485783052806974419 (2 : ZMod 815485783052806974419)
  · rw [← twentySevenYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (4091, 1), (99668269744904299, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (4091, 1), (99668269744904299, 1)] : List FactorBlock).map factorBlockValue).prod = 815485783052806974419 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twentySevenY_2
      · exact prime_twentySevenY_4091
      · exact prime_twentySevenY_99668269744904299
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 815485783052806974419) ^ 407742891526403487209 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (2 : ZMod 815485783052806974419) ^ 199336539489808598 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (2 : ZMod 815485783052806974419) ^ 8182 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide

private theorem prime_twentySevenY_300098768163432966586193 : Nat.Prime 300098768163432966586193 := by
  apply lucas_primality 300098768163432966586193 (3 : ZMod 300098768163432966586193)
  · rw [← twentySevenYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 4), (23, 1), (815485783052806974419, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 4), (23, 1), (815485783052806974419, 1)] : List FactorBlock).map factorBlockValue).prod = 300098768163432966586193 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twentySevenY_2
      · exact prime_twentySevenY_23
      · exact prime_twentySevenY_815485783052806974419
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 300098768163432966586193) ^ 150049384081716483293096 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (3 : ZMod 300098768163432966586193) ^ 13047772528844911590704 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (3 : ZMod 300098768163432966586193) ^ 368 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide

private theorem prime_twentySevenY_8233 : Nat.Prime 8233 := by norm_num
private theorem prime_twentySevenY_93811 : Nat.Prime 93811 := by norm_num
private theorem prime_twentySevenY_8274073 : Nat.Prime 8274073 := by norm_num
private theorem prime_twentySevenY_1429 : Nat.Prime 1429 := by norm_num
private theorem prime_twentySevenY_217223 : Nat.Prime 217223 := by norm_num
private theorem prime_twentySevenY_277508030299 : Nat.Prime 277508030299 := by
  apply lucas_primality 277508030299 (3 : ZMod 277508030299)
  · rw [← twentySevenYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (149, 1), (1429, 1), (217223, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (149, 1), (1429, 1), (217223, 1)] : List FactorBlock).map factorBlockValue).prod = 277508030299 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentySevenY_2
      · exact prime_twentySevenY_3
      · exact prime_twentySevenY_149
      · exact prime_twentySevenY_1429
      · exact prime_twentySevenY_217223
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 277508030299) ^ 138754015149 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (3 : ZMod 277508030299) ^ 92502676766 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (3 : ZMod 277508030299) ^ 1862470002 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (3 : ZMod 277508030299) ^ 194197362 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (3 : ZMod 277508030299) ^ 1277526 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide

private theorem prime_twentySevenY_16996403 : Nat.Prime 16996403 := by norm_num
private theorem prime_twentySevenY_33992807 : Nat.Prime 33992807 := by
  apply lucas_primality 33992807 (5 : ZMod 33992807)
  · rw [← twentySevenYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (16996403, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (16996403, 1)] : List FactorBlock).map factorBlockValue).prod = 33992807 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_twentySevenY_2
      · exact prime_twentySevenY_16996403
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 33992807) ^ 16996403 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (5 : ZMod 33992807) ^ 2 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide

private theorem prime_twentySevenY_2651438947 : Nat.Prime 2651438947 := by
  apply lucas_primality 2651438947 (3 : ZMod 2651438947)
  · rw [← twentySevenYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (13, 1), (33992807, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (13, 1), (33992807, 1)] : List FactorBlock).map factorBlockValue).prod = 2651438947 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentySevenY_2
      · exact prime_twentySevenY_3
      · exact prime_twentySevenY_13
      · exact prime_twentySevenY_33992807
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 2651438947) ^ 1325719473 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (3 : ZMod 2651438947) ^ 883812982 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (3 : ZMod 2651438947) ^ 203956842 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (3 : ZMod 2651438947) ^ 78 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide

private theorem prime_twentySevenY_127269069457 : Nat.Prime 127269069457 := by
  apply lucas_primality 127269069457 (5 : ZMod 127269069457)
  · rw [← twentySevenYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 4), (3, 1), (2651438947, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 4), (3, 1), (2651438947, 1)] : List FactorBlock).map factorBlockValue).prod = 127269069457 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twentySevenY_2
      · exact prime_twentySevenY_3
      · exact prime_twentySevenY_2651438947
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 127269069457) ^ 63634534728 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (5 : ZMod 127269069457) ^ 42423023152 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (5 : ZMod 127269069457) ^ 48 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide

private theorem prime_twentySevenY_4933 : Nat.Prime 4933 := by norm_num
private theorem prime_twentySevenY_16603 : Nat.Prime 16603 := by norm_num
private theorem prime_twentySevenY_21417871 : Nat.Prime 21417871 := by
  apply lucas_primality 21417871 (6 : ZMod 21417871)
  · rw [← twentySevenYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (5, 1), (43, 1), (16603, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (5, 1), (43, 1), (16603, 1)] : List FactorBlock).map factorBlockValue).prod = 21417871 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentySevenY_2
      · exact prime_twentySevenY_3
      · exact prime_twentySevenY_5
      · exact prime_twentySevenY_43
      · exact prime_twentySevenY_16603
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 21417871) ^ 10708935 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (6 : ZMod 21417871) ^ 7139290 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (6 : ZMod 21417871) ^ 4283574 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (6 : ZMod 21417871) ^ 498090 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (6 : ZMod 21417871) ^ 1290 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide

private theorem prime_twentySevenY_13200878061346993 : Nat.Prime 13200878061346993 := by
  apply lucas_primality 13200878061346993 (5 : ZMod 13200878061346993)
  · rw [← twentySevenYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 4), (3, 1), (19, 1), (137, 1), (4933, 1), (21417871, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 4), (3, 1), (19, 1), (137, 1), (4933, 1), (21417871, 1)] : List FactorBlock).map factorBlockValue).prod = 13200878061346993 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_twentySevenY_2
      · exact prime_twentySevenY_3
      · exact prime_twentySevenY_19
      · exact prime_twentySevenY_137
      · exact prime_twentySevenY_4933
      · exact prime_twentySevenY_21417871
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 13200878061346993) ^ 6600439030673496 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (5 : ZMod 13200878061346993) ^ 4400292687115664 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (5 : ZMod 13200878061346993) ^ 694783055860368 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (5 : ZMod 13200878061346993) ^ 96356774170416 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (5 : ZMod 13200878061346993) ^ 2676034474224 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (5 : ZMod 13200878061346993) ^ 616348752 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide

private theorem prime_twentySevenY_359 : Nat.Prime 359 := by norm_num
private theorem prime_twentySevenY_24949783 : Nat.Prime 24949783 := by
  apply lucas_primality 24949783 (6 : ZMod 24949783)
  · rw [← twentySevenYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 5), (11, 1), (13, 1), (359, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 5), (11, 1), (13, 1), (359, 1)] : List FactorBlock).map factorBlockValue).prod = 24949783 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentySevenY_2
      · exact prime_twentySevenY_3
      · exact prime_twentySevenY_11
      · exact prime_twentySevenY_13
      · exact prime_twentySevenY_359
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 24949783) ^ 12474891 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (6 : ZMod 24949783) ^ 8316594 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (6 : ZMod 24949783) ^ 2268162 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (6 : ZMod 24949783) ^ 1919214 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (6 : ZMod 24949783) ^ 69498 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide

private theorem prime_twentySevenY_5659 : Nat.Prime 5659 := by norm_num
private theorem prime_twentySevenY_14303 : Nat.Prime 14303 := by norm_num
private theorem prime_twentySevenY_11372171 : Nat.Prime 11372171 := by norm_num
private theorem prime_twentySevenY_63970908826694406967 : Nat.Prime 63970908826694406967 := by
  apply lucas_primality 63970908826694406967 (3 : ZMod 63970908826694406967)
  · rw [← twentySevenYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 5), (11, 1), (13, 1), (5659, 1), (14303, 1), (11372171, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 5), (11, 1), (13, 1), (5659, 1), (14303, 1), (11372171, 1)] : List FactorBlock).map factorBlockValue).prod = 63970908826694406967 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_twentySevenY_2
      · exact prime_twentySevenY_3
      · exact prime_twentySevenY_11
      · exact prime_twentySevenY_13
      · exact prime_twentySevenY_5659
      · exact prime_twentySevenY_14303
      · exact prime_twentySevenY_11372171
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 63970908826694406967) ^ 31985454413347203483 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (3 : ZMod 63970908826694406967) ^ 21323636275564802322 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (3 : ZMod 63970908826694406967) ^ 5815537166063127906 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (3 : ZMod 63970908826694406967) ^ 4920839140514954382 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (3 : ZMod 63970908826694406967) ^ 11304277933679874 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (3 : ZMod 63970908826694406967) ^ 4472551830154122 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (3 : ZMod 63970908826694406967) ^ 5625215170146 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide

private theorem prime_twentySevenY_67 : Nat.Prime 67 := by norm_num
private theorem prime_twentySevenY_12583 : Nat.Prime 12583 := by norm_num
private theorem prime_twentySevenY_277259 : Nat.Prime 277259 := by norm_num
private theorem prime_twentySevenY_2674733 : Nat.Prime 2674733 := by norm_num
private theorem prime_twentySevenY_239 : Nat.Prime 239 := by norm_num
private theorem prime_twentySevenY_283 : Nat.Prime 283 := by norm_num
private theorem prime_twentySevenY_1997 : Nat.Prime 1997 := by norm_num
private theorem prime_twentySevenY_2431279603 : Nat.Prime 2431279603 := by
  apply lucas_primality 2431279603 (2 : ZMod 2431279603)
  · rw [← twentySevenYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 2), (239, 1), (283, 1), (1997, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 2), (239, 1), (283, 1), (1997, 1)] : List FactorBlock).map factorBlockValue).prod = 2431279603 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentySevenY_2
      · exact prime_twentySevenY_3
      · exact prime_twentySevenY_239
      · exact prime_twentySevenY_283
      · exact prime_twentySevenY_1997
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 2431279603) ^ 1215639801 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (2 : ZMod 2431279603) ^ 810426534 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (2 : ZMod 2431279603) ^ 10172718 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (2 : ZMod 2431279603) ^ 8591094 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (2 : ZMod 2431279603) ^ 1217466 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide

private theorem prime_twentySevenY_947 : Nat.Prime 947 := by norm_num
private theorem prime_twentySevenY_2281 : Nat.Prime 2281 := by norm_num
private theorem prime_twentySevenY_103 : Nat.Prime 103 := by norm_num
private theorem prime_twentySevenY_263 : Nat.Prime 263 := by norm_num
private theorem prime_twentySevenY_463 : Nat.Prime 463 := by norm_num
private theorem prime_twentySevenY_109 : Nat.Prime 109 := by norm_num
private theorem prime_twentySevenY_863 : Nat.Prime 863 := by norm_num
private theorem prime_twentySevenY_2731329413 : Nat.Prime 2731329413 := by
  apply lucas_primality 2731329413 (2 : ZMod 2731329413)
  · rw [← twentySevenYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (7, 1), (17, 1), (61, 1), (109, 1), (863, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (7, 1), (17, 1), (61, 1), (109, 1), (863, 1)] : List FactorBlock).map factorBlockValue).prod = 2731329413 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_twentySevenY_2
      · exact prime_twentySevenY_7
      · exact prime_twentySevenY_17
      · exact prime_twentySevenY_61
      · exact prime_twentySevenY_109
      · exact prime_twentySevenY_863
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 2731329413) ^ 1365664706 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (2 : ZMod 2731329413) ^ 390189916 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (2 : ZMod 2731329413) ^ 160666436 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (2 : ZMod 2731329413) ^ 44775892 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (2 : ZMod 2731329413) ^ 25058068 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (2 : ZMod 2731329413) ^ 3164924 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide

private theorem prime_twentySevenY_144165029076967 : Nat.Prime 144165029076967 := by
  apply lucas_primality 144165029076967 (47 : ZMod 144165029076967)
  · rw [← twentySevenYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (19, 1), (463, 1), (2731329413, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (19, 1), (463, 1), (2731329413, 1)] : List FactorBlock).map factorBlockValue).prod = 144165029076967 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentySevenY_2
      · exact prime_twentySevenY_3
      · exact prime_twentySevenY_19
      · exact prime_twentySevenY_463
      · exact prime_twentySevenY_2731329413
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (47 : ZMod 144165029076967) ^ 72082514538483 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (47 : ZMod 144165029076967) ^ 48055009692322 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (47 : ZMod 144165029076967) ^ 7587633109314 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (47 : ZMod 144165029076967) ^ 311371553082 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (47 : ZMod 144165029076967) ^ 52782 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide

private theorem prime_twentySevenY_7810572945331918127 : Nat.Prime 7810572945331918127 := by
  apply lucas_primality 7810572945331918127 (5 : ZMod 7810572945331918127)
  · rw [← twentySevenYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (103, 1), (263, 1), (144165029076967, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (103, 1), (263, 1), (144165029076967, 1)] : List FactorBlock).map factorBlockValue).prod = 7810572945331918127 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentySevenY_2
      · exact prime_twentySevenY_103
      · exact prime_twentySevenY_263
      · exact prime_twentySevenY_144165029076967
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 7810572945331918127) ^ 3905286472665959063 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (5 : ZMod 7810572945331918127) ^ 75830805294484642 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (5 : ZMod 7810572945331918127) ^ 29697995989855202 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (5 : ZMod 7810572945331918127) ^ 54178 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide

private theorem prime_twentySevenY_1532168852393981051301083 : Nat.Prime 1532168852393981051301083 := by
  apply lucas_primality 1532168852393981051301083 (2 : ZMod 1532168852393981051301083)
  · rw [← twentySevenYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (43, 1), (2281, 1), (7810572945331918127, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (43, 1), (2281, 1), (7810572945331918127, 1)] : List FactorBlock).map factorBlockValue).prod = 1532168852393981051301083 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentySevenY_2
      · exact prime_twentySevenY_43
      · exact prime_twentySevenY_2281
      · exact prime_twentySevenY_7810572945331918127
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1532168852393981051301083) ^ 766084426196990525650541 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (2 : ZMod 1532168852393981051301083) ^ 35631833776604210495374 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (2 : ZMod 1532168852393981051301083) ^ 671709273298544958922 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (2 : ZMod 1532168852393981051301083) ^ 196166 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide

private theorem prime_twentySevenY_157 : Nat.Prime 157 := by norm_num
private theorem prime_twentySevenY_337 : Nat.Prime 337 := by norm_num
private theorem prime_twentySevenY_3656251 : Nat.Prime 3656251 := by norm_num
private theorem prime_twentySevenY_179 : Nat.Prime 179 := by norm_num
private theorem prime_twentySevenY_271 : Nat.Prime 271 := by norm_num
private theorem prime_twentySevenY_2857 : Nat.Prime 2857 := by norm_num
private theorem prime_twentySevenY_188916269 : Nat.Prime 188916269 := by
  apply lucas_primality 188916269 (2 : ZMod 188916269)
  · rw [← twentySevenYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (61, 1), (271, 1), (2857, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (61, 1), (271, 1), (2857, 1)] : List FactorBlock).map factorBlockValue).prod = 188916269 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentySevenY_2
      · exact prime_twentySevenY_61
      · exact prime_twentySevenY_271
      · exact prime_twentySevenY_2857
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 188916269) ^ 94458134 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (2 : ZMod 188916269) ^ 3096988 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (2 : ZMod 188916269) ^ 697108 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (2 : ZMod 188916269) ^ 66124 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide

private theorem prime_twentySevenY_45989776525361 : Nat.Prime 45989776525361 := by
  apply lucas_primality 45989776525361 (6 : ZMod 45989776525361)
  · rw [← twentySevenYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 4), (5, 1), (17, 1), (179, 1), (188916269, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 4), (5, 1), (17, 1), (179, 1), (188916269, 1)] : List FactorBlock).map factorBlockValue).prod = 45989776525361 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentySevenY_2
      · exact prime_twentySevenY_5
      · exact prime_twentySevenY_17
      · exact prime_twentySevenY_179
      · exact prime_twentySevenY_188916269
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 45989776525361) ^ 22994888262680 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (6 : ZMod 45989776525361) ^ 9197955305072 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (6 : ZMod 45989776525361) ^ 2705280972080 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (6 : ZMod 45989776525361) ^ 256926125840 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (6 : ZMod 45989776525361) ^ 243440 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide

private theorem prime_twentySevenY_8839990548539518477653493 : Nat.Prime 8839990548539518477653493 := by
  apply lucas_primality 8839990548539518477653493 (5 : ZMod 8839990548539518477653493)
  · rw [← twentySevenYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (13, 1), (337, 1), (3656251, 1), (45989776525361, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (13, 1), (337, 1), (3656251, 1), (45989776525361, 1)] : List FactorBlock).map factorBlockValue).prod = 8839990548539518477653493 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_twentySevenY_2
      · exact prime_twentySevenY_3
      · exact prime_twentySevenY_13
      · exact prime_twentySevenY_337
      · exact prime_twentySevenY_3656251
      · exact prime_twentySevenY_45989776525361
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 8839990548539518477653493) ^ 4419995274269759238826746 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (5 : ZMod 8839990548539518477653493) ^ 2946663516179839492551164 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (5 : ZMod 8839990548539518477653493) ^ 679999272964578344434884 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (5 : ZMod 8839990548539518477653493) ^ 26231425960057918331316 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (5 : ZMod 8839990548539518477653493) ^ 2417774531491278492 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (5 : ZMod 8839990548539518477653493) ^ 192216427572 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide

private theorem prime_twentySevenY_919 : Nat.Prime 919 := by norm_num
private theorem prime_twentySevenY_11257 : Nat.Prime 11257 := by norm_num
private theorem prime_twentySevenY_425291 : Nat.Prime 425291 := by norm_num
private theorem prime_twentySevenY_443 : Nat.Prime 443 := by norm_num
private theorem prime_twentySevenY_292231 : Nat.Prime 292231 := by norm_num
private theorem prime_twentySevenY_4610820719 : Nat.Prime 4610820719 := by
  apply lucas_primality 4610820719 (13 : ZMod 4610820719)
  · rw [← twentySevenYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (7, 3), (23, 1), (292231, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (7, 3), (23, 1), (292231, 1)] : List FactorBlock).map factorBlockValue).prod = 4610820719 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentySevenY_2
      · exact prime_twentySevenY_7
      · exact prime_twentySevenY_23
      · exact prime_twentySevenY_292231
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (13 : ZMod 4610820719) ^ 2305410359 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (13 : ZMod 4610820719) ^ 658688674 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (13 : ZMod 4610820719) ^ 200470466 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (13 : ZMod 4610820719) ^ 15778 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide

private theorem prime_twentySevenY_302303849620517 : Nat.Prime 302303849620517 := by
  apply lucas_primality 302303849620517 (2 : ZMod 302303849620517)
  · rw [← twentySevenYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (37, 1), (443, 1), (4610820719, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (37, 1), (443, 1), (4610820719, 1)] : List FactorBlock).map factorBlockValue).prod = 302303849620517 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentySevenY_2
      · exact prime_twentySevenY_37
      · exact prime_twentySevenY_443
      · exact prime_twentySevenY_4610820719
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 302303849620517) ^ 151151924810258 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (2 : ZMod 302303849620517) ^ 8170374314068 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (2 : ZMod 302303849620517) ^ 682401466412 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (2 : ZMod 302303849620517) ^ 65564 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide

private theorem prime_twentySevenY_191 : Nat.Prime 191 := by norm_num
private theorem prime_twentySevenY_251 : Nat.Prime 251 := by norm_num
private theorem prime_twentySevenY_6271 : Nat.Prime 6271 := by norm_num
private theorem prime_twentySevenY_13217 : Nat.Prime 13217 := by norm_num
private theorem prime_twentySevenY_481513 : Nat.Prime 481513 := by norm_num
private theorem prime_twentySevenY_4289 : Nat.Prime 4289 := by norm_num
private theorem prime_twentySevenY_5557 : Nat.Prime 5557 := by norm_num
private theorem prime_twentySevenY_47667947 : Nat.Prime 47667947 := by
  apply lucas_primality 47667947 (2 : ZMod 47667947)
  · rw [← twentySevenYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (4289, 1), (5557, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (4289, 1), (5557, 1)] : List FactorBlock).map factorBlockValue).prod = 47667947 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twentySevenY_2
      · exact prime_twentySevenY_4289
      · exact prime_twentySevenY_5557
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 47667947) ^ 23833973 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (2 : ZMod 47667947) ^ 11114 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (2 : ZMod 47667947) ^ 8578 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide

private theorem prime_twentySevenY_667351259 : Nat.Prime 667351259 := by
  apply lucas_primality 667351259 (2 : ZMod 667351259)
  · rw [← twentySevenYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (7, 1), (47667947, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (7, 1), (47667947, 1)] : List FactorBlock).map factorBlockValue).prod = 667351259 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twentySevenY_2
      · exact prime_twentySevenY_7
      · exact prime_twentySevenY_47667947
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 667351259) ^ 333675629 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (2 : ZMod 667351259) ^ 95335894 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (2 : ZMod 667351259) ^ 14 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide

private theorem prime_twentySevenY_9281 : Nat.Prime 9281 := by norm_num
private theorem prime_twentySevenY_14626967 : Nat.Prime 14626967 := by norm_num
private theorem prime_twentySevenY_7907 : Nat.Prime 7907 := by norm_num
private theorem prime_twentySevenY_20509 : Nat.Prime 20509 := by norm_num
private theorem prime_twentySevenY_23462297 : Nat.Prime 23462297 := by
  apply lucas_primality 23462297 (3 : ZMod 23462297)
  · rw [← twentySevenYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (11, 1), (13, 1), (20509, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (11, 1), (13, 1), (20509, 1)] : List FactorBlock).map factorBlockValue).prod = 23462297 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentySevenY_2
      · exact prime_twentySevenY_11
      · exact prime_twentySevenY_13
      · exact prime_twentySevenY_20509
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 23462297) ^ 11731148 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (3 : ZMod 23462297) ^ 2132936 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (3 : ZMod 23462297) ^ 1804792 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (3 : ZMod 23462297) ^ 1144 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide

private theorem prime_twentySevenY_695686433921251 : Nat.Prime 695686433921251 := by
  apply lucas_primality 695686433921251 (13 : ZMod 695686433921251)
  · rw [← twentySevenYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (5, 4), (7907, 1), (23462297, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (5, 4), (7907, 1), (23462297, 1)] : List FactorBlock).map factorBlockValue).prod = 695686433921251 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentySevenY_2
      · exact prime_twentySevenY_3
      · exact prime_twentySevenY_5
      · exact prime_twentySevenY_7907
      · exact prime_twentySevenY_23462297
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 695686433921251) ^ 347843216960625 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (13 : ZMod 695686433921251) ^ 231895477973750 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (13 : ZMod 695686433921251) ^ 139137286784250 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (13 : ZMod 695686433921251) ^ 87983613750 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (13 : ZMod 695686433921251) ^ 29651250 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide

private theorem prime_twentySevenY_5009 : Nat.Prime 5009 := by norm_num
private theorem prime_twentySevenY_61717 : Nat.Prime 61717 := by norm_num
private theorem prime_twentySevenY_35279 : Nat.Prime 35279 := by norm_num
private theorem prime_twentySevenY_7190123 : Nat.Prime 7190123 := by norm_num
private theorem prime_twentySevenY_1521962095903 : Nat.Prime 1521962095903 := by
  apply lucas_primality 1521962095903 (3 : ZMod 1521962095903)
  · rw [← twentySevenYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (35279, 1), (7190123, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (35279, 1), (7190123, 1)] : List FactorBlock).map factorBlockValue).prod = 1521962095903 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentySevenY_2
      · exact prime_twentySevenY_3
      · exact prime_twentySevenY_35279
      · exact prime_twentySevenY_7190123
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1521962095903) ^ 760981047951 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (3 : ZMod 1521962095903) ^ 507320698634 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (3 : ZMod 1521962095903) ^ 43140738 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (3 : ZMod 1521962095903) ^ 211674 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide

private theorem prime_twentySevenY_563585608037072707 : Nat.Prime 563585608037072707 := by
  apply lucas_primality 563585608037072707 (3 : ZMod 563585608037072707)
  · rw [← twentySevenYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (61717, 1), (1521962095903, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (61717, 1), (1521962095903, 1)] : List FactorBlock).map factorBlockValue).prod = 563585608037072707 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentySevenY_2
      · exact prime_twentySevenY_3
      · exact prime_twentySevenY_61717
      · exact prime_twentySevenY_1521962095903
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 563585608037072707) ^ 281792804018536353 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (3 : ZMod 563585608037072707) ^ 187861869345690902 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (3 : ZMod 563585608037072707) ^ 9131772575418 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (3 : ZMod 563585608037072707) ^ 370302 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide

private theorem prime_twentySevenY_2291539082278737626663 : Nat.Prime 2291539082278737626663 := by
  apply lucas_primality 2291539082278737626663 (10 : ZMod 2291539082278737626663)
  · rw [← twentySevenYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (19, 1), (107, 1), (563585608037072707, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (19, 1), (107, 1), (563585608037072707, 1)] : List FactorBlock).map factorBlockValue).prod = 2291539082278737626663 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentySevenY_2
      · exact prime_twentySevenY_19
      · exact prime_twentySevenY_107
      · exact prime_twentySevenY_563585608037072707
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (10 : ZMod 2291539082278737626663) ^ 1145769541139368813331 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (10 : ZMod 2291539082278737626663) ^ 120607320119933559298 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (10 : ZMod 2291539082278737626663) ^ 21416253105408762866 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (10 : ZMod 2291539082278737626663) ^ 4066 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide

private theorem prime_twentySevenY_32051 : Nat.Prime 32051 := by norm_num
private theorem prime_twentySevenY_80149 : Nat.Prime 80149 := by norm_num
private theorem prime_twentySevenY_173 : Nat.Prime 173 := by norm_num
private theorem prime_twentySevenY_557 : Nat.Prime 557 := by norm_num
private theorem prime_twentySevenY_977323 : Nat.Prime 977323 := by norm_num
private theorem prime_twentySevenY_1088737823 : Nat.Prime 1088737823 := by
  apply lucas_primality 1088737823 (5 : ZMod 1088737823)
  · rw [← twentySevenYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (557, 1), (977323, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (557, 1), (977323, 1)] : List FactorBlock).map factorBlockValue).prod = 1088737823 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twentySevenY_2
      · exact prime_twentySevenY_557
      · exact prime_twentySevenY_977323
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 1088737823) ^ 544368911 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (5 : ZMod 1088737823) ^ 1954646 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (5 : ZMod 1088737823) ^ 1114 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide

private theorem prime_twentySevenY_2776281448651 : Nat.Prime 2776281448651 := by
  apply lucas_primality 2776281448651 (22 : ZMod 2776281448651)
  · rw [← twentySevenYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (5, 2), (17, 1), (1088737823, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (5, 2), (17, 1), (1088737823, 1)] : List FactorBlock).map factorBlockValue).prod = 2776281448651 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentySevenY_2
      · exact prime_twentySevenY_3
      · exact prime_twentySevenY_5
      · exact prime_twentySevenY_17
      · exact prime_twentySevenY_1088737823
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (22 : ZMod 2776281448651) ^ 1388140724325 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (22 : ZMod 2776281448651) ^ 925427149550 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (22 : ZMod 2776281448651) ^ 555256289730 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (22 : ZMod 2776281448651) ^ 163310673450 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (22 : ZMod 2776281448651) ^ 2550 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide

private theorem prime_twentySevenY_1282642029276763 : Nat.Prime 1282642029276763 := by
  apply lucas_primality 1282642029276763 (3 : ZMod 1282642029276763)
  · rw [← twentySevenYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (7, 1), (11, 1), (2776281448651, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (7, 1), (11, 1), (2776281448651, 1)] : List FactorBlock).map factorBlockValue).prod = 1282642029276763 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentySevenY_2
      · exact prime_twentySevenY_3
      · exact prime_twentySevenY_7
      · exact prime_twentySevenY_11
      · exact prime_twentySevenY_2776281448651
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1282642029276763) ^ 641321014638381 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (3 : ZMod 1282642029276763) ^ 427547343092254 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (3 : ZMod 1282642029276763) ^ 183234575610966 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (3 : ZMod 1282642029276763) ^ 116603820843342 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (3 : ZMod 1282642029276763) ^ 462 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide

private theorem prime_twentySevenY_443794142129759999 : Nat.Prime 443794142129759999 := by
  apply lucas_primality 443794142129759999 (7 : ZMod 443794142129759999)
  · rw [← twentySevenYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (173, 1), (1282642029276763, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (173, 1), (1282642029276763, 1)] : List FactorBlock).map factorBlockValue).prod = 443794142129759999 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twentySevenY_2
      · exact prime_twentySevenY_173
      · exact prime_twentySevenY_1282642029276763
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 443794142129759999) ^ 221897071064879999 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (7 : ZMod 443794142129759999) ^ 2565284058553526 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (7 : ZMod 443794142129759999) ^ 346 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide

private theorem prime_twentySevenY_1100731236923317283545060801 : Nat.Prime 1100731236923317283545060801 := by
  apply lucas_primality 1100731236923317283545060801 (71 : ZMod 1100731236923317283545060801)
  · rw [← twentySevenYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 6), (3, 6), (5, 2), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 6), (3, 6), (5, 2), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod = 1100731236923317283545060801 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_twentySevenY_2
      · exact prime_twentySevenY_3
      · exact prime_twentySevenY_5
      · exact prime_twentySevenY_7
      · exact prime_twentySevenY_11
      · exact prime_twentySevenY_13
      · exact prime_twentySevenY_17
      · exact prime_twentySevenY_19
      · exact prime_twentySevenY_23
      · exact prime_twentySevenY_31
      · exact prime_twentySevenY_37
      · exact prime_twentySevenY_41
      · exact prime_twentySevenY_43
      · exact prime_twentySevenY_47
      · exact prime_twentySevenY_53
      · exact prime_twentySevenY_59
      · exact prime_twentySevenY_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (71 : ZMod 1100731236923317283545060801) ^ 550365618461658641772530400 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (71 : ZMod 1100731236923317283545060801) ^ 366910412307772427848353600 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (71 : ZMod 1100731236923317283545060801) ^ 220146247384663456709012160 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (71 : ZMod 1100731236923317283545060801) ^ 157247319560473897649294400 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (71 : ZMod 1100731236923317283545060801) ^ 100066476083937934867732800 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (71 : ZMod 1100731236923317283545060801) ^ 84671633609485944888081600 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (71 : ZMod 1100731236923317283545060801) ^ 64748896289606899032062400 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (71 : ZMod 1100731236923317283545060801) ^ 57933222995964067555003200 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (71 : ZMod 1100731236923317283545060801) ^ 47857879866231186241089600 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (71 : ZMod 1100731236923317283545060801) ^ 35507459255590880114356800 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (71 : ZMod 1100731236923317283545060801) ^ 29749492889819386041758400 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (71 : ZMod 1100731236923317283545060801) ^ 26847103339593104476708800 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (71 : ZMod 1100731236923317283545060801) ^ 25598400858681797291745600 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (71 : ZMod 1100731236923317283545060801) ^ 23419813551559942203086400 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (71 : ZMod 1100731236923317283545060801) ^ 20768513904213533651793600 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (71 : ZMod 1100731236923317283545060801) ^ 18656461642768089551611200 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (71 : ZMod 1100731236923317283545060801) ^ 18044774375792086615492800 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide

private theorem prime_twentySevenY_139 : Nat.Prime 139 := by norm_num
private theorem prime_twentySevenY_577 : Nat.Prime 577 := by norm_num
private theorem prime_twentySevenY_2303321 : Nat.Prime 2303321 := by norm_num
private theorem prime_twentySevenY_34057 : Nat.Prime 34057 := by norm_num
private theorem prime_twentySevenY_20025517 : Nat.Prime 20025517 := by
  apply lucas_primality 20025517 (2 : ZMod 20025517)
  · rw [← twentySevenYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (7, 2), (34057, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (7, 2), (34057, 1)] : List FactorBlock).map factorBlockValue).prod = 20025517 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentySevenY_2
      · exact prime_twentySevenY_3
      · exact prime_twentySevenY_7
      · exact prime_twentySevenY_34057
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 20025517) ^ 10012758 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (2 : ZMod 20025517) ^ 6675172 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (2 : ZMod 20025517) ^ 2860788 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (2 : ZMod 20025517) ^ 588 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide

private theorem prime_twentySevenY_2879936805405053 : Nat.Prime 2879936805405053 := by
  apply lucas_primality 2879936805405053 (2 : ZMod 2879936805405053)
  · rw [← twentySevenYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (19, 1), (61, 1), (67, 1), (463, 1), (20025517, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (19, 1), (61, 1), (67, 1), (463, 1), (20025517, 1)] : List FactorBlock).map factorBlockValue).prod = 2879936805405053 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_twentySevenY_2
      · exact prime_twentySevenY_19
      · exact prime_twentySevenY_61
      · exact prime_twentySevenY_67
      · exact prime_twentySevenY_463
      · exact prime_twentySevenY_20025517
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 2879936805405053) ^ 1439968402702526 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (2 : ZMod 2879936805405053) ^ 151575621337108 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (2 : ZMod 2879936805405053) ^ 47212078777132 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (2 : ZMod 2879936805405053) ^ 42984131423956 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (2 : ZMod 2879936805405053) ^ 6220165886404 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (2 : ZMod 2879936805405053) ^ 143813356 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide

private theorem prime_twentySevenY_5759873610810107 : Nat.Prime 5759873610810107 := by
  apply lucas_primality 5759873610810107 (2 : ZMod 5759873610810107)
  · rw [← twentySevenYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (2879936805405053, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (2879936805405053, 1)] : List FactorBlock).map factorBlockValue).prod = 5759873610810107 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_twentySevenY_2
      · exact prime_twentySevenY_2879936805405053
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 5759873610810107) ^ 2879936805405053 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (2 : ZMod 5759873610810107) ^ 2 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide

private theorem prime_twentySevenY_361727 : Nat.Prime 361727 := by norm_num
private theorem prime_twentySevenY_404191789 : Nat.Prime 404191789 := by
  apply lucas_primality 404191789 (6 : ZMod 404191789)
  · rw [← twentySevenYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (7, 2), (11, 2), (13, 1), (19, 1), (23, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (7, 2), (11, 2), (13, 1), (19, 1), (23, 1)] : List FactorBlock).map factorBlockValue).prod = 404191789 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_twentySevenY_2
      · exact prime_twentySevenY_3
      · exact prime_twentySevenY_7
      · exact prime_twentySevenY_11
      · exact prime_twentySevenY_13
      · exact prime_twentySevenY_19
      · exact prime_twentySevenY_23
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 404191789) ^ 202095894 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (6 : ZMod 404191789) ^ 134730596 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (6 : ZMod 404191789) ^ 57741684 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (6 : ZMod 404191789) ^ 36744708 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (6 : ZMod 404191789) ^ 31091676 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (6 : ZMod 404191789) ^ 21273252 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (6 : ZMod 404191789) ^ 17573556 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide

private theorem prime_twentySevenY_8504393 : Nat.Prime 8504393 := by norm_num
private theorem prime_twentySevenY_459237223 : Nat.Prime 459237223 := by
  apply lucas_primality 459237223 (5 : ZMod 459237223)
  · rw [← twentySevenYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 3), (8504393, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 3), (8504393, 1)] : List FactorBlock).map factorBlockValue).prod = 459237223 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twentySevenY_2
      · exact prime_twentySevenY_3
      · exact prime_twentySevenY_8504393
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 459237223) ^ 229618611 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (5 : ZMod 459237223) ^ 153079074 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (5 : ZMod 459237223) ^ 54 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide

private theorem prime_twentySevenY_40093901583788580553 : Nat.Prime 40093901583788580553 := by
  apply lucas_primality 40093901583788580553 (5 : ZMod 40093901583788580553)
  · rw [← twentySevenYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (3, 3), (404191789, 1), (459237223, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (3, 3), (404191789, 1), (459237223, 1)] : List FactorBlock).map factorBlockValue).prod = 40093901583788580553 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentySevenY_2
      · exact prime_twentySevenY_3
      · exact prime_twentySevenY_404191789
      · exact prime_twentySevenY_459237223
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 40093901583788580553) ^ 20046950791894290276 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (5 : ZMod 40093901583788580553) ^ 13364633861262860184 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (5 : ZMod 40093901583788580553) ^ 99195240168 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (5 : ZMod 40093901583788580553) ^ 87305426424 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide

private theorem prime_twentySevenY_89 : Nat.Prime 89 := by norm_num
private theorem prime_twentySevenY_1009 : Nat.Prime 1009 := by norm_num
private theorem prime_twentySevenY_142723051 : Nat.Prime 142723051 := by
  apply lucas_primality 142723051 (10 : ZMod 142723051)
  · rw [← twentySevenYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (5, 2), (23, 1), (41, 1), (1009, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (5, 2), (23, 1), (41, 1), (1009, 1)] : List FactorBlock).map factorBlockValue).prod = 142723051 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_twentySevenY_2
      · exact prime_twentySevenY_3
      · exact prime_twentySevenY_5
      · exact prime_twentySevenY_23
      · exact prime_twentySevenY_41
      · exact prime_twentySevenY_1009
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 142723051) ^ 71361525 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (10 : ZMod 142723051) ^ 47574350 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (10 : ZMod 142723051) ^ 28544610 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (10 : ZMod 142723051) ^ 6205350 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (10 : ZMod 142723051) ^ 3481050 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (10 : ZMod 142723051) ^ 141450 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide

private theorem prime_twentySevenY_541 : Nat.Prime 541 := by norm_num
private theorem prime_twentySevenY_1123 : Nat.Prime 1123 := by norm_num
private theorem prime_twentySevenY_17191 : Nat.Prime 17191 := by norm_num
private theorem prime_twentySevenY_79594331 : Nat.Prime 79594331 := by
  apply lucas_primality 79594331 (2 : ZMod 79594331)
  · rw [← twentySevenYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 1), (463, 1), (17191, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 1), (463, 1), (17191, 1)] : List FactorBlock).map factorBlockValue).prod = 79594331 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentySevenY_2
      · exact prime_twentySevenY_5
      · exact prime_twentySevenY_463
      · exact prime_twentySevenY_17191
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 79594331) ^ 39797165 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (2 : ZMod 79594331) ^ 15918866 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (2 : ZMod 79594331) ^ 171910 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (2 : ZMod 79594331) ^ 4630 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide

private theorem prime_twentySevenY_676997700942263 : Nat.Prime 676997700942263 := by
  apply lucas_primality 676997700942263 (5 : ZMod 676997700942263)
  · rw [← twentySevenYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (7, 1), (541, 1), (1123, 1), (79594331, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (7, 1), (541, 1), (1123, 1), (79594331, 1)] : List FactorBlock).map factorBlockValue).prod = 676997700942263 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentySevenY_2
      · exact prime_twentySevenY_7
      · exact prime_twentySevenY_541
      · exact prime_twentySevenY_1123
      · exact prime_twentySevenY_79594331
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 676997700942263) ^ 338498850471131 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (5 : ZMod 676997700942263) ^ 96713957277466 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (5 : ZMod 676997700942263) ^ 1251382071982 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (5 : ZMod 676997700942263) ^ 602847462994 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (5 : ZMod 676997700942263) ^ 8505602 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide

private theorem prime_twentySevenY_78531733309302509 : Nat.Prime 78531733309302509 := by
  apply lucas_primality 78531733309302509 (2 : ZMod 78531733309302509)
  · rw [← twentySevenYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (29, 1), (676997700942263, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (29, 1), (676997700942263, 1)] : List FactorBlock).map factorBlockValue).prod = 78531733309302509 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twentySevenY_2
      · exact prime_twentySevenY_29
      · exact prime_twentySevenY_676997700942263
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 78531733309302509) ^ 39265866654651254 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (2 : ZMod 78531733309302509) ^ 2707990803769052 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (2 : ZMod 78531733309302509) ^ 116 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide

private theorem prime_twentySevenY_60793 : Nat.Prime 60793 := by norm_num
private theorem prime_twentySevenY_33749 : Nat.Prime 33749 := by norm_num
private theorem prime_twentySevenY_347 : Nat.Prime 347 := by norm_num
private theorem prime_twentySevenY_109481 : Nat.Prime 109481 := by norm_num
private theorem prime_twentySevenY_5205667 : Nat.Prime 5205667 := by norm_num
private theorem prime_twentySevenY_791051220811877 : Nat.Prime 791051220811877 := by
  apply lucas_primality 791051220811877 (2 : ZMod 791051220811877)
  · rw [← twentySevenYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (347, 1), (109481, 1), (5205667, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (347, 1), (109481, 1), (5205667, 1)] : List FactorBlock).map factorBlockValue).prod = 791051220811877 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentySevenY_2
      · exact prime_twentySevenY_347
      · exact prime_twentySevenY_109481
      · exact prime_twentySevenY_5205667
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 791051220811877) ^ 395525610405938 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (2 : ZMod 791051220811877) ^ 2279686515308 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (2 : ZMod 791051220811877) ^ 7225465796 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (2 : ZMod 791051220811877) ^ 151959628 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide

private theorem prime_twentySevenY_106788750604720147493 : Nat.Prime 106788750604720147493 := by
  apply lucas_primality 106788750604720147493 (2 : ZMod 106788750604720147493)
  · rw [← twentySevenYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (33749, 1), (791051220811877, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (33749, 1), (791051220811877, 1)] : List FactorBlock).map factorBlockValue).prod = 106788750604720147493 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twentySevenY_2
      · exact prime_twentySevenY_33749
      · exact prime_twentySevenY_791051220811877
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 106788750604720147493) ^ 53394375302360073746 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (2 : ZMod 106788750604720147493) ^ 3164204883247508 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (2 : ZMod 106788750604720147493) ^ 134996 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide

private theorem prime_twentySevenY_130787 : Nat.Prime 130787 := by norm_num
private theorem prime_twentySevenY_246391 : Nat.Prime 246391 := by norm_num
private theorem prime_twentySevenY_14702459 : Nat.Prime 14702459 := by norm_num
private theorem prime_twentySevenY_154621 : Nat.Prime 154621 := by norm_num
private theorem prime_twentySevenY_990811369 : Nat.Prime 990811369 := by
  apply lucas_primality 990811369 (17 : ZMod 990811369)
  · rw [← twentySevenYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (3, 2), (89, 1), (154621, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (3, 2), (89, 1), (154621, 1)] : List FactorBlock).map factorBlockValue).prod = 990811369 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentySevenY_2
      · exact prime_twentySevenY_3
      · exact prime_twentySevenY_89
      · exact prime_twentySevenY_154621
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (17 : ZMod 990811369) ^ 495405684 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (17 : ZMod 990811369) ^ 330270456 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (17 : ZMod 990811369) ^ 11132712 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (17 : ZMod 990811369) ^ 6408 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide

private theorem prime_twentySevenY_7178534534772569414123 : Nat.Prime 7178534534772569414123 := by
  apply lucas_primality 7178534534772569414123 (2 : ZMod 7178534534772569414123)
  · rw [← twentySevenYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (246391, 1), (14702459, 1), (990811369, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (246391, 1), (14702459, 1), (990811369, 1)] : List FactorBlock).map factorBlockValue).prod = 7178534534772569414123 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentySevenY_2
      · exact prime_twentySevenY_246391
      · exact prime_twentySevenY_14702459
      · exact prime_twentySevenY_990811369
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 7178534534772569414123) ^ 3589267267386284707061 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (2 : ZMod 7178534534772569414123) ^ 29134727058912742 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (2 : ZMod 7178534534772569414123) ^ 488254008038558 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (2 : ZMod 7178534534772569414123) ^ 7245107150938 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide

private theorem prime_twentySevenY_5188849 : Nat.Prime 5188849 := by norm_num
private theorem prime_twentySevenY_13926949 : Nat.Prime 13926949 := by norm_num
private theorem prime_twentySevenY_167123389 : Nat.Prime 167123389 := by
  apply lucas_primality 167123389 (2 : ZMod 167123389)
  · rw [← twentySevenYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (13926949, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (13926949, 1)] : List FactorBlock).map factorBlockValue).prod = 167123389 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twentySevenY_2
      · exact prime_twentySevenY_3
      · exact prime_twentySevenY_13926949
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 167123389) ^ 83561694 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (2 : ZMod 167123389) ^ 55707796 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (2 : ZMod 167123389) ^ 12 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide

private theorem prime_twentySevenY_569 : Nat.Prime 569 := by norm_num
private theorem prime_twentySevenY_152809 : Nat.Prime 152809 := by norm_num
private theorem prime_twentySevenY_3130139557 : Nat.Prime 3130139557 := by
  apply lucas_primality 3130139557 (2 : ZMod 3130139557)
  · rw [← twentySevenYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 2), (569, 1), (152809, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 2), (569, 1), (152809, 1)] : List FactorBlock).map factorBlockValue).prod = 3130139557 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentySevenY_2
      · exact prime_twentySevenY_3
      · exact prime_twentySevenY_569
      · exact prime_twentySevenY_152809
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 3130139557) ^ 1565069778 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (2 : ZMod 3130139557) ^ 1043379852 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (2 : ZMod 3130139557) ^ 5501124 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (2 : ZMod 3130139557) ^ 20484 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide

private theorem prime_twentySevenY_175768162351756354129 : Nat.Prime 175768162351756354129 := by
  apply lucas_primality 175768162351756354129 (11 : ZMod 175768162351756354129)
  · rw [← twentySevenYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 4), (3, 1), (7, 1), (167123389, 1), (3130139557, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 4), (3, 1), (7, 1), (167123389, 1), (3130139557, 1)] : List FactorBlock).map factorBlockValue).prod = 175768162351756354129 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentySevenY_2
      · exact prime_twentySevenY_3
      · exact prime_twentySevenY_7
      · exact prime_twentySevenY_167123389
      · exact prime_twentySevenY_3130139557
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 175768162351756354129) ^ 87884081175878177064 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (11 : ZMod 175768162351756354129) ^ 58589387450585451376 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (11 : ZMod 175768162351756354129) ^ 25109737478822336304 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (11 : ZMod 175768162351756354129) ^ 1051726891152 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (11 : ZMod 175768162351756354129) ^ 56153458704 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide

private theorem prime_twentySevenY_769 : Nat.Prime 769 := by norm_num
private theorem prime_twentySevenY_2143 : Nat.Prime 2143 := by norm_num
private theorem prime_twentySevenY_8597 : Nat.Prime 8597 := by norm_num
private theorem prime_twentySevenY_9792301 : Nat.Prime 9792301 := by norm_num
private theorem prime_twentySevenY_161017 : Nat.Prime 161017 := by norm_num
private theorem prime_twentySevenY_6391408799 : Nat.Prime 6391408799 := by
  apply lucas_primality 6391408799 (23 : ZMod 6391408799)
  · rw [← twentySevenYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (89, 1), (223, 1), (161017, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (89, 1), (223, 1), (161017, 1)] : List FactorBlock).map factorBlockValue).prod = 6391408799 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentySevenY_2
      · exact prime_twentySevenY_89
      · exact prime_twentySevenY_223
      · exact prime_twentySevenY_161017
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (23 : ZMod 6391408799) ^ 3195704399 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (23 : ZMod 6391408799) ^ 71813582 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (23 : ZMod 6391408799) ^ 28661026 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (23 : ZMod 6391408799) ^ 39694 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide

private theorem prime_twentySevenY_475637 : Nat.Prime 475637 := by norm_num
private theorem prime_twentySevenY_327337 : Nat.Prime 327337 := by norm_num
private theorem prime_twentySevenY_2131 : Nat.Prime 2131 := by norm_num
private theorem prime_twentySevenY_209281249 : Nat.Prime 209281249 := by
  apply lucas_primality 209281249 (13 : ZMod 209281249)
  · rw [← twentySevenYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 5), (3, 2), (11, 1), (31, 1), (2131, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 5), (3, 2), (11, 1), (31, 1), (2131, 1)] : List FactorBlock).map factorBlockValue).prod = 209281249 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentySevenY_2
      · exact prime_twentySevenY_3
      · exact prime_twentySevenY_11
      · exact prime_twentySevenY_31
      · exact prime_twentySevenY_2131
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 209281249) ^ 104640624 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (13 : ZMod 209281249) ^ 69760416 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (13 : ZMod 209281249) ^ 19025568 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (13 : ZMod 209281249) ^ 6751008 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (13 : ZMod 209281249) ^ 98208 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide

private theorem prime_twentySevenY_197901371804377 : Nat.Prime 197901371804377 := by
  apply lucas_primality 197901371804377 (5 : ZMod 197901371804377)
  · rw [← twentySevenYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (3, 1), (31, 2), (41, 1), (209281249, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (3, 1), (31, 2), (41, 1), (209281249, 1)] : List FactorBlock).map factorBlockValue).prod = 197901371804377 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentySevenY_2
      · exact prime_twentySevenY_3
      · exact prime_twentySevenY_31
      · exact prime_twentySevenY_41
      · exact prime_twentySevenY_209281249
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 197901371804377) ^ 98950685902188 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (5 : ZMod 197901371804377) ^ 65967123934792 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (5 : ZMod 197901371804377) ^ 6383915219496 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (5 : ZMod 197901371804377) ^ 4826862726936 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (5 : ZMod 197901371804377) ^ 945624 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide

private theorem prime_twentySevenY_1813852357585221913373 : Nat.Prime 1813852357585221913373 := by
  apply lucas_primality 1813852357585221913373 (2 : ZMod 1813852357585221913373)
  · rw [← twentySevenYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (7, 1), (327337, 1), (197901371804377, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (7, 1), (327337, 1), (197901371804377, 1)] : List FactorBlock).map factorBlockValue).prod = 1813852357585221913373 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentySevenY_2
      · exact prime_twentySevenY_7
      · exact prime_twentySevenY_327337
      · exact prime_twentySevenY_197901371804377
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1813852357585221913373) ^ 906926178792610956686 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (2 : ZMod 1813852357585221913373) ^ 259121765369317416196 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (2 : ZMod 1813852357585221913373) ^ 5541238410522556 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (2 : ZMod 1813852357585221913373) ^ 9165436 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide

private theorem prime_twentySevenY_472883 : Nat.Prime 472883 := by norm_num
private theorem prime_twentySevenY_42559471 : Nat.Prime 42559471 := by
  apply lucas_primality 42559471 (6 : ZMod 42559471)
  · rw [← twentySevenYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 2), (5, 1), (472883, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 2), (5, 1), (472883, 1)] : List FactorBlock).map factorBlockValue).prod = 42559471 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentySevenY_2
      · exact prime_twentySevenY_3
      · exact prime_twentySevenY_5
      · exact prime_twentySevenY_472883
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 42559471) ^ 21279735 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (6 : ZMod 42559471) ^ 14186490 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (6 : ZMod 42559471) ^ 8511894 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (6 : ZMod 42559471) ^ 90 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide

private theorem prime_twentySevenY_3109 : Nat.Prime 3109 := by norm_num
private theorem prime_twentySevenY_151632149 : Nat.Prime 151632149 := by
  apply lucas_primality 151632149 (2 : ZMod 151632149)
  · rw [← twentySevenYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (89, 1), (137, 1), (3109, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (89, 1), (137, 1), (3109, 1)] : List FactorBlock).map factorBlockValue).prod = 151632149 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentySevenY_2
      · exact prime_twentySevenY_89
      · exact prime_twentySevenY_137
      · exact prime_twentySevenY_3109
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 151632149) ^ 75816074 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (2 : ZMod 151632149) ^ 1703732 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (2 : ZMod 151632149) ^ 1106804 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (2 : ZMod 151632149) ^ 48772 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide

private theorem prime_twentySevenY_953 : Nat.Prime 953 := by norm_num
private theorem prime_twentySevenY_758827 : Nat.Prime 758827 := by norm_num
private theorem prime_twentySevenY_1446324263 : Nat.Prime 1446324263 := by
  apply lucas_primality 1446324263 (5 : ZMod 1446324263)
  · rw [← twentySevenYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (953, 1), (758827, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (953, 1), (758827, 1)] : List FactorBlock).map factorBlockValue).prod = 1446324263 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twentySevenY_2
      · exact prime_twentySevenY_953
      · exact prime_twentySevenY_758827
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 1446324263) ^ 723162131 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (5 : ZMod 1446324263) ^ 1517654 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (5 : ZMod 1446324263) ^ 1906 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide

private theorem prime_twentySevenY_19737833053457806831 : Nat.Prime 19737833053457806831 := by
  apply lucas_primality 19737833053457806831 (15 : ZMod 19737833053457806831)
  · rw [← twentySevenYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 2), (5, 1), (151632149, 1), (1446324263, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 2), (5, 1), (151632149, 1), (1446324263, 1)] : List FactorBlock).map factorBlockValue).prod = 19737833053457806831 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentySevenY_2
      · exact prime_twentySevenY_3
      · exact prime_twentySevenY_5
      · exact prime_twentySevenY_151632149
      · exact prime_twentySevenY_1446324263
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (15 : ZMod 19737833053457806831) ^ 9868916526728903415 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (15 : ZMod 19737833053457806831) ^ 6579277684485935610 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (15 : ZMod 19737833053457806831) ^ 3947566610691561366 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (15 : ZMod 19737833053457806831) ^ 130169183670 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (15 : ZMod 19737833053457806831) ^ 13646893410 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide

private theorem prime_twentySevenY_11489 : Nat.Prime 11489 := by norm_num
private theorem prime_twentySevenY_193 : Nat.Prime 193 := by norm_num
private theorem prime_twentySevenY_7723 : Nat.Prime 7723 := by norm_num
private theorem prime_twentySevenY_21580023643 : Nat.Prime 21580023643 := by
  apply lucas_primality 21580023643 (2 : ZMod 21580023643)
  · rw [← twentySevenYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (19, 1), (127, 1), (193, 1), (7723, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (19, 1), (127, 1), (193, 1), (7723, 1)] : List FactorBlock).map factorBlockValue).prod = 21580023643 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_twentySevenY_2
      · exact prime_twentySevenY_3
      · exact prime_twentySevenY_19
      · exact prime_twentySevenY_127
      · exact prime_twentySevenY_193
      · exact prime_twentySevenY_7723
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 21580023643) ^ 10790011821 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (2 : ZMod 21580023643) ^ 7193341214 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (2 : ZMod 21580023643) ^ 1135790718 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (2 : ZMod 21580023643) ^ 169921446 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (2 : ZMod 21580023643) ^ 111813594 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (2 : ZMod 21580023643) ^ 2794254 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide

private theorem prime_twentySevenY_18679 : Nat.Prime 18679 := by norm_num
private theorem prime_twentySevenY_77218987 : Nat.Prime 77218987 := by
  apply lucas_primality 77218987 (5 : ZMod 77218987)
  · rw [← twentySevenYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (13, 1), (53, 1), (18679, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (13, 1), (53, 1), (18679, 1)] : List FactorBlock).map factorBlockValue).prod = 77218987 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentySevenY_2
      · exact prime_twentySevenY_3
      · exact prime_twentySevenY_13
      · exact prime_twentySevenY_53
      · exact prime_twentySevenY_18679
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 77218987) ^ 38609493 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (5 : ZMod 77218987) ^ 25739662 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (5 : ZMod 77218987) ^ 5939922 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (5 : ZMod 77218987) ^ 1456962 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (5 : ZMod 77218987) ^ 4134 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide

private theorem prime_twentySevenY_103164566633 : Nat.Prime 103164566633 := by
  apply lucas_primality 103164566633 (3 : ZMod 103164566633)
  · rw [← twentySevenYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (167, 1), (77218987, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (167, 1), (77218987, 1)] : List FactorBlock).map factorBlockValue).prod = 103164566633 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twentySevenY_2
      · exact prime_twentySevenY_167
      · exact prime_twentySevenY_77218987
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 103164566633) ^ 51582283316 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (3 : ZMod 103164566633) ^ 617751896 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (3 : ZMod 103164566633) ^ 1336 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide

private theorem prime_twentySevenY_71241401185919644928609 : Nat.Prime 71241401185919644928609 := by
  apply lucas_primality 71241401185919644928609 (3 : ZMod 71241401185919644928609)
  · rw [← twentySevenYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 5), (21580023643, 1), (103164566633, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 5), (21580023643, 1), (103164566633, 1)] : List FactorBlock).map factorBlockValue).prod = 71241401185919644928609 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twentySevenY_2
      · exact prime_twentySevenY_21580023643
      · exact prime_twentySevenY_103164566633
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 71241401185919644928609) ^ 35620700592959822464304 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (3 : ZMod 71241401185919644928609) ^ 3301266132256 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (3 : ZMod 71241401185919644928609) ^ 690560756576 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide

private theorem prime_twentySevenY_2377 : Nat.Prime 2377 := by norm_num
private theorem prime_twentySevenY_3089 : Nat.Prime 3089 := by norm_num
private theorem prime_twentySevenY_4157 : Nat.Prime 4157 := by norm_num
private theorem prime_twentySevenY_6528503 : Nat.Prime 6528503 := by norm_num
private theorem prime_twentySevenY_2551 : Nat.Prime 2551 := by norm_num
private theorem prime_twentySevenY_27067 : Nat.Prime 27067 := by norm_num
private theorem prime_twentySevenY_4004779187 : Nat.Prime 4004779187 := by
  apply lucas_primality 4004779187 (2 : ZMod 4004779187)
  · rw [← twentySevenYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (29, 1), (2551, 1), (27067, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (29, 1), (2551, 1), (27067, 1)] : List FactorBlock).map factorBlockValue).prod = 4004779187 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentySevenY_2
      · exact prime_twentySevenY_29
      · exact prime_twentySevenY_2551
      · exact prime_twentySevenY_27067
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 4004779187) ^ 2002389593 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (2 : ZMod 4004779187) ^ 138095834 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (2 : ZMod 4004779187) ^ 1569886 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (2 : ZMod 4004779187) ^ 147958 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide

private theorem prime_twentySevenY_9587 : Nat.Prime 9587 := by norm_num
private theorem prime_twentySevenY_1173541 : Nat.Prime 1173541 := by norm_num
private theorem prime_twentySevenY_881 : Nat.Prime 881 := by norm_num
private theorem prime_twentySevenY_8741 : Nat.Prime 8741 := by norm_num
private theorem prime_twentySevenY_15427 : Nat.Prime 15427 := by norm_num
private theorem prime_twentySevenY_34600664721388751 : Nat.Prime 34600664721388751 := by
  apply lucas_primality 34600664721388751 (13 : ZMod 34600664721388751)
  · rw [← twentySevenYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 4), (233, 1), (881, 1), (8741, 1), (15427, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 4), (233, 1), (881, 1), (8741, 1), (15427, 1)] : List FactorBlock).map factorBlockValue).prod = 34600664721388751 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_twentySevenY_2
      · exact prime_twentySevenY_5
      · exact prime_twentySevenY_233
      · exact prime_twentySevenY_881
      · exact prime_twentySevenY_8741
      · exact prime_twentySevenY_15427
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 34600664721388751) ^ 17300332360694375 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (13 : ZMod 34600664721388751) ^ 6920132944277750 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (13 : ZMod 34600664721388751) ^ 148500706958750 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (13 : ZMod 34600664721388751) ^ 39274307288750 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (13 : ZMod 34600664721388751) ^ 3958433213750 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (13 : ZMod 34600664721388751) ^ 2242864116250 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide

private theorem prime_twentySevenY_69201329442777503 : Nat.Prime 69201329442777503 := by
  apply lucas_primality 69201329442777503 (5 : ZMod 69201329442777503)
  · rw [← twentySevenYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (34600664721388751, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (34600664721388751, 1)] : List FactorBlock).map factorBlockValue).prod = 69201329442777503 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_twentySevenY_2
      · exact prime_twentySevenY_34600664721388751
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 69201329442777503) ^ 34600664721388751 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (5 : ZMod 69201329442777503) ^ 2 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide

private theorem prime_twentySevenY_277 : Nat.Prime 277 := by norm_num
private theorem prime_twentySevenY_1483 : Nat.Prime 1483 := by norm_num
private theorem prime_twentySevenY_76543 : Nat.Prime 76543 := by norm_num
private theorem prime_twentySevenY_6810796141 : Nat.Prime 6810796141 := by
  apply lucas_primality 6810796141 (2 : ZMod 6810796141)
  · rw [← twentySevenYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (5, 1), (1483, 1), (76543, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (5, 1), (1483, 1), (76543, 1)] : List FactorBlock).map factorBlockValue).prod = 6810796141 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentySevenY_2
      · exact prime_twentySevenY_3
      · exact prime_twentySevenY_5
      · exact prime_twentySevenY_1483
      · exact prime_twentySevenY_76543
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 6810796141) ^ 3405398070 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (2 : ZMod 6810796141) ^ 2270265380 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (2 : ZMod 6810796141) ^ 1362159228 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (2 : ZMod 6810796141) ^ 4592580 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (2 : ZMod 6810796141) ^ 88980 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide

private theorem prime_twentySevenY_55291 : Nat.Prime 55291 := by norm_num
private theorem prime_twentySevenY_756933791 : Nat.Prime 756933791 := by
  apply lucas_primality 756933791 (11 : ZMod 756933791)
  · rw [← twentySevenYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 1), (37, 2), (55291, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 1), (37, 2), (55291, 1)] : List FactorBlock).map factorBlockValue).prod = 756933791 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentySevenY_2
      · exact prime_twentySevenY_5
      · exact prime_twentySevenY_37
      · exact prime_twentySevenY_55291
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 756933791) ^ 378466895 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (11 : ZMod 756933791) ^ 151386758 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (11 : ZMod 756933791) ^ 20457670 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (11 : ZMod 756933791) ^ 13690 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide

private theorem prime_twentySevenY_1513867583 : Nat.Prime 1513867583 := by
  apply lucas_primality 1513867583 (5 : ZMod 1513867583)
  · rw [← twentySevenYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (756933791, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (756933791, 1)] : List FactorBlock).map factorBlockValue).prod = 1513867583 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_twentySevenY_2
      · exact prime_twentySevenY_756933791
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 1513867583) ^ 756933791 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (5 : ZMod 1513867583) ^ 2 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide

private theorem prime_twentySevenY_108998465977 : Nat.Prime 108998465977 := by
  apply lucas_primality 108998465977 (5 : ZMod 108998465977)
  · rw [← twentySevenYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (3, 2), (1513867583, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (3, 2), (1513867583, 1)] : List FactorBlock).map factorBlockValue).prod = 108998465977 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twentySevenY_2
      · exact prime_twentySevenY_3
      · exact prime_twentySevenY_1513867583
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 108998465977) ^ 54499232988 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (5 : ZMod 108998465977) ^ 36332821992 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (5 : ZMod 108998465977) ^ 72 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide

private theorem prime_twentySevenY_402858330250993 : Nat.Prime 402858330250993 := by
  apply lucas_primality 402858330250993 (5 : ZMod 402858330250993)
  · rw [← twentySevenYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 4), (3, 1), (7, 1), (11, 1), (108998465977, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 4), (3, 1), (7, 1), (11, 1), (108998465977, 1)] : List FactorBlock).map factorBlockValue).prod = 402858330250993 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentySevenY_2
      · exact prime_twentySevenY_3
      · exact prime_twentySevenY_7
      · exact prime_twentySevenY_11
      · exact prime_twentySevenY_108998465977
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 402858330250993) ^ 201429165125496 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (5 : ZMod 402858330250993) ^ 134286110083664 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (5 : ZMod 402858330250993) ^ 57551190035856 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (5 : ZMod 402858330250993) ^ 36623484568272 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (5 : ZMod 402858330250993) ^ 3696 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide

private theorem prime_twentySevenY_4993 : Nat.Prime 4993 := by norm_num
private theorem prime_twentySevenY_5443 : Nat.Prime 5443 := by norm_num
private theorem prime_twentySevenY_229 : Nat.Prime 229 := by norm_num
private theorem prime_twentySevenY_761 : Nat.Prime 761 := by norm_num
private theorem prime_twentySevenY_16091 : Nat.Prime 16091 := by norm_num
private theorem prime_twentySevenY_1659615521571361 : Nat.Prime 1659615521571361 := by
  apply lucas_primality 1659615521571361 (19 : ZMod 1659615521571361)
  · rw [← twentySevenYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 5), (3, 3), (5, 1), (137, 1), (229, 1), (761, 1), (16091, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 5), (3, 3), (5, 1), (137, 1), (229, 1), (761, 1), (16091, 1)] : List FactorBlock).map factorBlockValue).prod = 1659615521571361 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_twentySevenY_2
      · exact prime_twentySevenY_3
      · exact prime_twentySevenY_5
      · exact prime_twentySevenY_137
      · exact prime_twentySevenY_229
      · exact prime_twentySevenY_761
      · exact prime_twentySevenY_16091
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (19 : ZMod 1659615521571361) ^ 829807760785680 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (19 : ZMod 1659615521571361) ^ 553205173857120 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (19 : ZMod 1659615521571361) ^ 331923104314272 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (19 : ZMod 1659615521571361) ^ 12113981909280 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (19 : ZMod 1659615521571361) ^ 7247229351840 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (19 : ZMod 1659615521571361) ^ 2180835113760 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (19 : ZMod 1659615521571361) ^ 103139364960 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide

private theorem prime_twentySevenY_269 : Nat.Prime 269 := by norm_num
private theorem prime_twentySevenY_1153 : Nat.Prime 1153 := by norm_num
private theorem prime_twentySevenY_1579 : Nat.Prime 1579 := by norm_num
private theorem prime_twentySevenY_1966233961 : Nat.Prime 1966233961 := by
  apply lucas_primality 1966233961 (7 : ZMod 1966233961)
  · rw [← twentySevenYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (3, 3), (5, 1), (1153, 1), (1579, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (3, 3), (5, 1), (1153, 1), (1579, 1)] : List FactorBlock).map factorBlockValue).prod = 1966233961 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentySevenY_2
      · exact prime_twentySevenY_3
      · exact prime_twentySevenY_5
      · exact prime_twentySevenY_1153
      · exact prime_twentySevenY_1579
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 1966233961) ^ 983116980 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (7 : ZMod 1966233961) ^ 655411320 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (7 : ZMod 1966233961) ^ 393246792 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (7 : ZMod 1966233961) ^ 1705320 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (7 : ZMod 1966233961) ^ 1245240 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide

private theorem prime_twentySevenY_163 : Nat.Prime 163 := by norm_num
private theorem prime_twentySevenY_303377 : Nat.Prime 303377 := by norm_num
private theorem prime_twentySevenY_239061077 : Nat.Prime 239061077 := by
  apply lucas_primality 239061077 (2 : ZMod 239061077)
  · rw [← twentySevenYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (197, 1), (303377, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (197, 1), (303377, 1)] : List FactorBlock).map factorBlockValue).prod = 239061077 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twentySevenY_2
      · exact prime_twentySevenY_197
      · exact prime_twentySevenY_303377
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 239061077) ^ 119530538 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (2 : ZMod 239061077) ^ 1213508 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (2 : ZMod 239061077) ^ 788 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide

private theorem prime_twentySevenY_12469425776321 : Nat.Prime 12469425776321 := by
  apply lucas_primality 12469425776321 (3 : ZMod 12469425776321)
  · rw [← twentySevenYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 6), (5, 1), (163, 1), (239061077, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 6), (5, 1), (163, 1), (239061077, 1)] : List FactorBlock).map factorBlockValue).prod = 12469425776321 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentySevenY_2
      · exact prime_twentySevenY_5
      · exact prime_twentySevenY_163
      · exact prime_twentySevenY_239061077
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 12469425776321) ^ 6234712888160 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (3 : ZMod 12469425776321) ^ 2493885155264 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (3 : ZMod 12469425776321) ^ 76499544640 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (3 : ZMod 12469425776321) ^ 52160 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide

private theorem prime_twentySevenY_65952904691686366162823891 : Nat.Prime 65952904691686366162823891 := by
  apply lucas_primality 65952904691686366162823891 (2 : ZMod 65952904691686366162823891)
  · rw [← twentySevenYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 1), (269, 1), (1966233961, 1), (12469425776321, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 1), (269, 1), (1966233961, 1), (12469425776321, 1)] : List FactorBlock).map factorBlockValue).prod = 65952904691686366162823891 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentySevenY_2
      · exact prime_twentySevenY_5
      · exact prime_twentySevenY_269
      · exact prime_twentySevenY_1966233961
      · exact prime_twentySevenY_12469425776321
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 65952904691686366162823891) ^ 32976452345843183081411945 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (2 : ZMod 65952904691686366162823891) ^ 13190580938337273232564778 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (2 : ZMod 65952904691686366162823891) ^ 245178084355711398374810 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (2 : ZMod 65952904691686366162823891) ^ 33542755338303490 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (2 : ZMod 65952904691686366162823891) ^ 5289169355090 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide

private theorem prime_twentySevenY_281 : Nat.Prime 281 := by norm_num
private theorem prime_twentySevenY_739 : Nat.Prime 739 := by norm_num
private theorem prime_twentySevenY_8443 : Nat.Prime 8443 := by norm_num
private theorem prime_twentySevenY_84294913 : Nat.Prime 84294913 := by
  apply lucas_primality 84294913 (14 : ZMod 84294913)
  · rw [← twentySevenYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 8), (3, 1), (13, 1), (8443, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 8), (3, 1), (13, 1), (8443, 1)] : List FactorBlock).map factorBlockValue).prod = 84294913 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentySevenY_2
      · exact prime_twentySevenY_3
      · exact prime_twentySevenY_13
      · exact prime_twentySevenY_8443
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (14 : ZMod 84294913) ^ 42147456 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (14 : ZMod 84294913) ^ 28098304 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (14 : ZMod 84294913) ^ 6484224 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (14 : ZMod 84294913) ^ 9984 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide

private theorem prime_twentySevenY_3540386347 : Nat.Prime 3540386347 := by
  apply lucas_primality 3540386347 (11 : ZMod 3540386347)
  · rw [← twentySevenYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (7, 1), (84294913, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (7, 1), (84294913, 1)] : List FactorBlock).map factorBlockValue).prod = 3540386347 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentySevenY_2
      · exact prime_twentySevenY_3
      · exact prime_twentySevenY_7
      · exact prime_twentySevenY_84294913
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 3540386347) ^ 1770193173 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (11 : ZMod 3540386347) ^ 1180128782 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (11 : ZMod 3540386347) ^ 505769478 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (11 : ZMod 3540386347) ^ 42 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide

private theorem prime_twentySevenY_1509031 : Nat.Prime 1509031 := by norm_num
private theorem prime_twentySevenY_9277522589 : Nat.Prime 9277522589 := by
  apply lucas_primality 9277522589 (2 : ZMod 9277522589)
  · rw [← twentySevenYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (29, 1), (53, 1), (1509031, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (29, 1), (53, 1), (1509031, 1)] : List FactorBlock).map factorBlockValue).prod = 9277522589 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentySevenY_2
      · exact prime_twentySevenY_29
      · exact prime_twentySevenY_53
      · exact prime_twentySevenY_1509031
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 9277522589) ^ 4638761294 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (2 : ZMod 9277522589) ^ 319914572 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (2 : ZMod 9277522589) ^ 175047596 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (2 : ZMod 9277522589) ^ 6148 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide

private theorem prime_twentySevenY_964862349257 : Nat.Prime 964862349257 := by
  apply lucas_primality 964862349257 (5 : ZMod 964862349257)
  · rw [← twentySevenYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (13, 1), (9277522589, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (13, 1), (9277522589, 1)] : List FactorBlock).map factorBlockValue).prod = 964862349257 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twentySevenY_2
      · exact prime_twentySevenY_13
      · exact prime_twentySevenY_9277522589
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 964862349257) ^ 482431174628 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (5 : ZMod 964862349257) ^ 74220180712 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (5 : ZMod 964862349257) ^ 104 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide

private theorem prime_twentySevenY_461 : Nat.Prime 461 := by norm_num
private theorem prime_twentySevenY_24289169 : Nat.Prime 24289169 := by
  apply lucas_primality 24289169 (6 : ZMod 24289169)
  · rw [← twentySevenYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 4), (37, 1), (89, 1), (461, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 4), (37, 1), (89, 1), (461, 1)] : List FactorBlock).map factorBlockValue).prod = 24289169 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentySevenY_2
      · exact prime_twentySevenY_37
      · exact prime_twentySevenY_89
      · exact prime_twentySevenY_461
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 24289169) ^ 12144584 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (6 : ZMod 24289169) ^ 656464 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (6 : ZMod 24289169) ^ 272912 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (6 : ZMod 24289169) ^ 52688 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide

private theorem prime_twentySevenY_18046411 : Nat.Prime 18046411 := by norm_num
private theorem prime_twentySevenY_180464111 : Nat.Prime 180464111 := by
  apply lucas_primality 180464111 (7 : ZMod 180464111)
  · rw [← twentySevenYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 1), (18046411, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 1), (18046411, 1)] : List FactorBlock).map factorBlockValue).prod = 180464111 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twentySevenY_2
      · exact prime_twentySevenY_5
      · exact prime_twentySevenY_18046411
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 180464111) ^ 90232055 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (7 : ZMod 180464111) ^ 36092822 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (7 : ZMod 180464111) ^ 10 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide

private theorem prime_twentySevenY_11208829 : Nat.Prime 11208829 := by norm_num
private theorem prime_twentySevenY_246594239 : Nat.Prime 246594239 := by
  apply lucas_primality 246594239 (11 : ZMod 246594239)
  · rw [← twentySevenYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (11, 1), (11208829, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (11, 1), (11208829, 1)] : List FactorBlock).map factorBlockValue).prod = 246594239 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twentySevenY_2
      · exact prime_twentySevenY_11
      · exact prime_twentySevenY_11208829
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (11 : ZMod 246594239) ^ 123297119 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (11 : ZMod 246594239) ^ 22417658 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (11 : ZMod 246594239) ^ 22 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide

private theorem prime_twentySevenY_158313501439 : Nat.Prime 158313501439 := by
  apply lucas_primality 158313501439 (3 : ZMod 158313501439)
  · rw [← twentySevenYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (107, 1), (246594239, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (107, 1), (246594239, 1)] : List FactorBlock).map factorBlockValue).prod = 158313501439 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentySevenY_2
      · exact prime_twentySevenY_3
      · exact prime_twentySevenY_107
      · exact prime_twentySevenY_246594239
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 158313501439) ^ 79156750719 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (3 : ZMod 158313501439) ^ 52771167146 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (3 : ZMod 158313501439) ^ 1479565434 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (3 : ZMod 158313501439) ^ 642 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide

private theorem prime_twentySevenY_1663 : Nat.Prime 1663 := by norm_num
private theorem prime_twentySevenY_1789 : Nat.Prime 1789 := by norm_num
private theorem prime_twentySevenY_69813937 : Nat.Prime 69813937 := by
  apply lucas_primality 69813937 (10 : ZMod 69813937)
  · rw [← twentySevenYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 4), (3, 2), (271, 1), (1789, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 4), (3, 2), (271, 1), (1789, 1)] : List FactorBlock).map factorBlockValue).prod = 69813937 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentySevenY_2
      · exact prime_twentySevenY_3
      · exact prime_twentySevenY_271
      · exact prime_twentySevenY_1789
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (10 : ZMod 69813937) ^ 34906968 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (10 : ZMod 69813937) ^ 23271312 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (10 : ZMod 69813937) ^ 257616 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (10 : ZMod 69813937) ^ 39024 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide

private theorem prime_twentySevenY_1117022993 : Nat.Prime 1117022993 := by
  apply lucas_primality 1117022993 (3 : ZMod 1117022993)
  · rw [← twentySevenYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 4), (69813937, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 4), (69813937, 1)] : List FactorBlock).map factorBlockValue).prod = 1117022993 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_twentySevenY_2
      · exact prime_twentySevenY_69813937
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 1117022993) ^ 558511496 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (3 : ZMod 1117022993) ^ 16 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide

private theorem prime_twentySevenY_169787494937 : Nat.Prime 169787494937 := by
  apply lucas_primality 169787494937 (3 : ZMod 169787494937)
  · rw [← twentySevenYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (19, 1), (1117022993, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (19, 1), (1117022993, 1)] : List FactorBlock).map factorBlockValue).prod = 169787494937 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twentySevenY_2
      · exact prime_twentySevenY_19
      · exact prime_twentySevenY_1117022993
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 169787494937) ^ 84893747468 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (3 : ZMod 169787494937) ^ 8936183944 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (3 : ZMod 169787494937) ^ 152 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide

private theorem prime_twentySevenY_7159 : Nat.Prime 7159 := by norm_num
private theorem prime_twentySevenY_113819 : Nat.Prime 113819 := by norm_num
private theorem prime_twentySevenY_400896468733 : Nat.Prime 400896468733 := by
  apply lucas_primality 400896468733 (5 : ZMod 400896468733)
  · rw [← twentySevenYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (41, 1), (7159, 1), (113819, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (41, 1), (7159, 1), (113819, 1)] : List FactorBlock).map factorBlockValue).prod = 400896468733 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentySevenY_2
      · exact prime_twentySevenY_3
      · exact prime_twentySevenY_41
      · exact prime_twentySevenY_7159
      · exact prime_twentySevenY_113819
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 400896468733) ^ 200448234366 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (5 : ZMod 400896468733) ^ 133632156244 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (5 : ZMod 400896468733) ^ 9777962652 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (5 : ZMod 400896468733) ^ 55998948 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (5 : ZMod 400896468733) ^ 3522228 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide

private theorem prime_twentySevenY_408403242931592497828927 : Nat.Prime 408403242931592497828927 := by
  apply lucas_primality 408403242931592497828927 (3 : ZMod 408403242931592497828927)
  · rw [← twentySevenYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (169787494937, 1), (400896468733, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (169787494937, 1), (400896468733, 1)] : List FactorBlock).map factorBlockValue).prod = 408403242931592497828927 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentySevenY_2
      · exact prime_twentySevenY_3
      · exact prime_twentySevenY_169787494937
      · exact prime_twentySevenY_400896468733
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 408403242931592497828927) ^ 204201621465796248914463 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (3 : ZMod 408403242931592497828927) ^ 136134414310530832609642 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (3 : ZMod 408403242931592497828927) ^ 2405378812398 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (3 : ZMod 408403242931592497828927) ^ 1018724969622 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide

private theorem prime_twentySevenY_25913 : Nat.Prime 25913 := by norm_num
private theorem prime_twentySevenY_644701 : Nat.Prime 644701 := by norm_num
private theorem prime_twentySevenY_1731666887 : Nat.Prime 1731666887 := by
  apply lucas_primality 1731666887 (5 : ZMod 1731666887)
  · rw [← twentySevenYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (17, 1), (79, 1), (644701, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (17, 1), (79, 1), (644701, 1)] : List FactorBlock).map factorBlockValue).prod = 1731666887 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentySevenY_2
      · exact prime_twentySevenY_17
      · exact prime_twentySevenY_79
      · exact prime_twentySevenY_644701
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 1731666887) ^ 865833443 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (5 : ZMod 1731666887) ^ 101862758 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (5 : ZMod 1731666887) ^ 21919834 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (5 : ZMod 1731666887) ^ 2686 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide

private theorem prime_twentySevenY_7603997 : Nat.Prime 7603997 := by norm_num
private theorem prime_twentySevenY_14820266192971 : Nat.Prime 14820266192971 := by
  apply lucas_primality 14820266192971 (3 : ZMod 14820266192971)
  · rw [← twentySevenYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (5, 1), (7, 1), (9281, 1), (7603997, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (5, 1), (7, 1), (9281, 1), (7603997, 1)] : List FactorBlock).map factorBlockValue).prod = 14820266192971 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_twentySevenY_2
      · exact prime_twentySevenY_3
      · exact prime_twentySevenY_5
      · exact prime_twentySevenY_7
      · exact prime_twentySevenY_9281
      · exact prime_twentySevenY_7603997
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 14820266192971) ^ 7410133096485 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (3 : ZMod 14820266192971) ^ 4940088730990 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (3 : ZMod 14820266192971) ^ 2964053238594 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (3 : ZMod 14820266192971) ^ 2117180884710 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (3 : ZMod 14820266192971) ^ 1596839370 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (3 : ZMod 14820266192971) ^ 1949010 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide

private theorem prime_twentySevenY_257 : Nat.Prime 257 := by norm_num
private theorem prime_twentySevenY_9871 : Nat.Prime 9871 := by norm_num
private theorem prime_twentySevenY_20294777 : Nat.Prime 20294777 := by
  apply lucas_primality 20294777 (3 : ZMod 20294777)
  · rw [← twentySevenYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (257, 1), (9871, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (257, 1), (9871, 1)] : List FactorBlock).map factorBlockValue).prod = 20294777 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twentySevenY_2
      · exact prime_twentySevenY_257
      · exact prime_twentySevenY_9871
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 20294777) ^ 10147388 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (3 : ZMod 20294777) ^ 78968 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (3 : ZMod 20294777) ^ 2056 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide

private theorem prime_twentySevenY_1201 : Nat.Prime 1201 := by norm_num
private theorem prime_twentySevenY_1481 : Nat.Prime 1481 := by norm_num
private theorem prime_twentySevenY_2244321898991 : Nat.Prime 2244321898991 := by
  apply lucas_primality 2244321898991 (7 : ZMod 2244321898991)
  · rw [← twentySevenYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 1), (19, 1), (29, 1), (229, 1), (1201, 1), (1481, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 1), (19, 1), (29, 1), (229, 1), (1201, 1), (1481, 1)] : List FactorBlock).map factorBlockValue).prod = 2244321898991 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_twentySevenY_2
      · exact prime_twentySevenY_5
      · exact prime_twentySevenY_19
      · exact prime_twentySevenY_29
      · exact prime_twentySevenY_229
      · exact prime_twentySevenY_1201
      · exact prime_twentySevenY_1481
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 2244321898991) ^ 1122160949495 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (7 : ZMod 2244321898991) ^ 448864379798 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (7 : ZMod 2244321898991) ^ 118122205210 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (7 : ZMod 2244321898991) ^ 77390410310 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (7 : ZMod 2244321898991) ^ 9800532310 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (7 : ZMod 2244321898991) ^ 1868710990 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (7 : ZMod 2244321898991) ^ 1515409790 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide

private theorem prime_twentySevenY_4488643797983 : Nat.Prime 4488643797983 := by
  apply lucas_primality 4488643797983 (5 : ZMod 4488643797983)
  · rw [← twentySevenYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (2244321898991, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (2244321898991, 1)] : List FactorBlock).map factorBlockValue).prod = 4488643797983 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_twentySevenY_2
      · exact prime_twentySevenY_2244321898991
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 4488643797983) ^ 2244321898991 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (5 : ZMod 4488643797983) ^ 2 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide

private theorem prime_twentySevenY_11176723056977671 : Nat.Prime 11176723056977671 := by
  apply lucas_primality 11176723056977671 (3 : ZMod 11176723056977671)
  · rw [← twentySevenYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (5, 1), (83, 1), (4488643797983, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (5, 1), (83, 1), (4488643797983, 1)] : List FactorBlock).map factorBlockValue).prod = 11176723056977671 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentySevenY_2
      · exact prime_twentySevenY_3
      · exact prime_twentySevenY_5
      · exact prime_twentySevenY_83
      · exact prime_twentySevenY_4488643797983
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 11176723056977671) ^ 5588361528488835 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (3 : ZMod 11176723056977671) ^ 3725574352325890 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (3 : ZMod 11176723056977671) ^ 2235344611395534 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (3 : ZMod 11176723056977671) ^ 134659313939490 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (3 : ZMod 11176723056977671) ^ 2490 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide

private theorem prime_twentySevenY_32099548619639871113 : Nat.Prime 32099548619639871113 := by
  apply lucas_primality 32099548619639871113 (3 : ZMod 32099548619639871113)
  · rw [← twentySevenYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (359, 1), (11176723056977671, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (359, 1), (11176723056977671, 1)] : List FactorBlock).map factorBlockValue).prod = 32099548619639871113 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twentySevenY_2
      · exact prime_twentySevenY_359
      · exact prime_twentySevenY_11176723056977671
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 32099548619639871113) ^ 16049774309819935556 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (3 : ZMod 32099548619639871113) ^ 89413784455821368 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (3 : ZMod 32099548619639871113) ^ 2872 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide

private theorem prime_twentySevenY_421 : Nat.Prime 421 := by norm_num
private theorem prime_twentySevenY_2063 : Nat.Prime 2063 := by norm_num
private theorem prime_twentySevenY_29382133091 : Nat.Prime 29382133091 := by
  apply lucas_primality 29382133091 (2 : ZMod 29382133091)
  · rw [← twentySevenYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 1), (17, 1), (199, 1), (421, 1), (2063, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 1), (17, 1), (199, 1), (421, 1), (2063, 1)] : List FactorBlock).map factorBlockValue).prod = 29382133091 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_twentySevenY_2
      · exact prime_twentySevenY_5
      · exact prime_twentySevenY_17
      · exact prime_twentySevenY_199
      · exact prime_twentySevenY_421
      · exact prime_twentySevenY_2063
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 29382133091) ^ 14691066545 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (2 : ZMod 29382133091) ^ 5876426618 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (2 : ZMod 29382133091) ^ 1728360770 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (2 : ZMod 29382133091) ^ 147648910 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (2 : ZMod 29382133091) ^ 69791290 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (2 : ZMod 29382133091) ^ 14242430 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide

private theorem prime_twentySevenY_6121 : Nat.Prime 6121 := by norm_num
private theorem prime_twentySevenY_1323919 : Nat.Prime 1323919 := by norm_num
private theorem prime_twentySevenY_194488996777 : Nat.Prime 194488996777 := by
  apply lucas_primality 194488996777 (7 : ZMod 194488996777)
  · rw [← twentySevenYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (3, 1), (6121, 1), (1323919, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (3, 1), (6121, 1), (1323919, 1)] : List FactorBlock).map factorBlockValue).prod = 194488996777 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentySevenY_2
      · exact prime_twentySevenY_3
      · exact prime_twentySevenY_6121
      · exact prime_twentySevenY_1323919
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 194488996777) ^ 97244498388 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (7 : ZMod 194488996777) ^ 64829665592 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (7 : ZMod 194488996777) ^ 31774056 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (7 : ZMod 194488996777) ^ 146904 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide

private theorem prime_twentySevenY_14781163755053 : Nat.Prime 14781163755053 := by
  apply lucas_primality 14781163755053 (2 : ZMod 14781163755053)
  · rw [← twentySevenYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (19, 1), (194488996777, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (19, 1), (194488996777, 1)] : List FactorBlock).map factorBlockValue).prod = 14781163755053 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twentySevenY_2
      · exact prime_twentySevenY_19
      · exact prime_twentySevenY_194488996777
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 14781163755053) ^ 7390581877526 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (2 : ZMod 14781163755053) ^ 777955987108 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (2 : ZMod 14781163755053) ^ 76 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide

private theorem prime_twentySevenY_4345662143985583 : Nat.Prime 4345662143985583 := by
  apply lucas_primality 4345662143985583 (3 : ZMod 4345662143985583)
  · rw [← twentySevenYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (7, 2), (14781163755053, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (7, 2), (14781163755053, 1)] : List FactorBlock).map factorBlockValue).prod = 4345662143985583 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentySevenY_2
      · exact prime_twentySevenY_3
      · exact prime_twentySevenY_7
      · exact prime_twentySevenY_14781163755053
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 4345662143985583) ^ 2172831071992791 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (3 : ZMod 4345662143985583) ^ 1448554047995194 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (3 : ZMod 4345662143985583) ^ 620808877712226 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (3 : ZMod 4345662143985583) ^ 294 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide

private theorem prime_twentySevenY_625905997466200023976603201 : Nat.Prime 625905997466200023976603201 := by
  apply lucas_primality 625905997466200023976603201 (79 : ZMod 625905997466200023976603201)
  · rw [← twentySevenYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 6), (3, 5), (5, 2), (7, 2), (11, 1), (13, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 6), (3, 5), (5, 2), (7, 2), (11, 1), (13, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod = 625905997466200023976603201 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_twentySevenY_2
      · exact prime_twentySevenY_3
      · exact prime_twentySevenY_5
      · exact prime_twentySevenY_7
      · exact prime_twentySevenY_11
      · exact prime_twentySevenY_13
      · exact prime_twentySevenY_19
      · exact prime_twentySevenY_23
      · exact prime_twentySevenY_29
      · exact prime_twentySevenY_31
      · exact prime_twentySevenY_37
      · exact prime_twentySevenY_41
      · exact prime_twentySevenY_43
      · exact prime_twentySevenY_47
      · exact prime_twentySevenY_53
      · exact prime_twentySevenY_59
      · exact prime_twentySevenY_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (79 : ZMod 625905997466200023976603201) ^ 312952998733100011988301600 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (79 : ZMod 625905997466200023976603201) ^ 208635332488733341325534400 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (79 : ZMod 625905997466200023976603201) ^ 125181199493240004795320640 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (79 : ZMod 625905997466200023976603201) ^ 89415142495171431996657600 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (79 : ZMod 625905997466200023976603201) ^ 56900545224200002179691200 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (79 : ZMod 625905997466200023976603201) ^ 48146615189707694152046400 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (79 : ZMod 625905997466200023976603201) ^ 32942420919273685472452800 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (79 : ZMod 625905997466200023976603201) ^ 27213304237660870607678400 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (79 : ZMod 625905997466200023976603201) ^ 21582965429868966344020800 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (79 : ZMod 625905997466200023976603201) ^ 20190516047296774966987200 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (79 : ZMod 625905997466200023976603201) ^ 16916378309897297945313600 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (79 : ZMod 625905997466200023976603201) ^ 15265999938200000584795200 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (79 : ZMod 625905997466200023976603201) ^ 14555953429446512185502400 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (79 : ZMod 625905997466200023976603201) ^ 13317148882259574978225600 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (79 : ZMod 625905997466200023976603201) ^ 11809547122003774037294400 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (79 : ZMod 625905997466200023976603201) ^ 10608576228240678372484800 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (79 : ZMod 625905997466200023976603201) ^ 10260754056822951212731200 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide

private theorem prime_twentySevenY_1604711 : Nat.Prime 1604711 := by norm_num
private theorem prime_twentySevenY_420313 : Nat.Prime 420313 := by norm_num
private theorem prime_twentySevenY_68090707 : Nat.Prime 68090707 := by
  apply lucas_primality 68090707 (2 : ZMod 68090707)
  · rw [← twentySevenYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 4), (420313, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 4), (420313, 1)] : List FactorBlock).map factorBlockValue).prod = 68090707 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twentySevenY_2
      · exact prime_twentySevenY_3
      · exact prime_twentySevenY_420313
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 68090707) ^ 34045353 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (2 : ZMod 68090707) ^ 22696902 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (2 : ZMod 68090707) ^ 162 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide

private theorem prime_twentySevenY_94207 : Nat.Prime 94207 := by norm_num
private theorem prime_twentySevenY_828277 : Nat.Prime 828277 := by norm_num
private theorem prime_twentySevenY_1404530844103 : Nat.Prime 1404530844103 := by
  apply lucas_primality 1404530844103 (6 : ZMod 1404530844103)
  · rw [← twentySevenYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 2), (94207, 1), (828277, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 2), (94207, 1), (828277, 1)] : List FactorBlock).map factorBlockValue).prod = 1404530844103 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentySevenY_2
      · exact prime_twentySevenY_3
      · exact prime_twentySevenY_94207
      · exact prime_twentySevenY_828277
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 1404530844103) ^ 702265422051 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (6 : ZMod 1404530844103) ^ 468176948034 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (6 : ZMod 1404530844103) ^ 14908986 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (6 : ZMod 1404530844103) ^ 1695726 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide

private theorem prime_twentySevenY_5618123376413 : Nat.Prime 5618123376413 := by
  apply lucas_primality 5618123376413 (2 : ZMod 5618123376413)
  · rw [← twentySevenYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (1404530844103, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (1404530844103, 1)] : List FactorBlock).map factorBlockValue).prod = 5618123376413 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_twentySevenY_2
      · exact prime_twentySevenY_1404530844103
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 5618123376413) ^ 2809061688206 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (2 : ZMod 5618123376413) ^ 4 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide

private theorem prime_twentySevenY_9257 : Nat.Prime 9257 := by norm_num
private theorem prime_twentySevenY_35267 : Nat.Prime 35267 := by norm_num
private theorem prime_twentySevenY_6032797 : Nat.Prime 6032797 := by norm_num
private theorem prime_twentySevenY_132887 : Nat.Prime 132887 := by norm_num
private theorem prime_twentySevenY_87173873 : Nat.Prime 87173873 := by
  apply lucas_primality 87173873 (3 : ZMod 87173873)
  · rw [← twentySevenYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 4), (41, 1), (132887, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 4), (41, 1), (132887, 1)] : List FactorBlock).map factorBlockValue).prod = 87173873 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twentySevenY_2
      · exact prime_twentySevenY_41
      · exact prime_twentySevenY_132887
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 87173873) ^ 43586936 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (3 : ZMod 87173873) ^ 2126192 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (3 : ZMod 87173873) ^ 656 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide

private theorem prime_twentySevenY_74187982766308990109 : Nat.Prime 74187982766308990109 := by
  apply lucas_primality 74187982766308990109 (2 : ZMod 74187982766308990109)
  · rw [← twentySevenYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (35267, 1), (6032797, 1), (87173873, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (35267, 1), (6032797, 1), (87173873, 1)] : List FactorBlock).map factorBlockValue).prod = 74187982766308990109 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentySevenY_2
      · exact prime_twentySevenY_35267
      · exact prime_twentySevenY_6032797
      · exact prime_twentySevenY_87173873
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 74187982766308990109) ^ 37093991383154495054 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (2 : ZMod 74187982766308990109) ^ 2103609118051124 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (2 : ZMod 74187982766308990109) ^ 12297443916364 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (2 : ZMod 74187982766308990109) ^ 851034607196 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide

private theorem prime_twentySevenY_37309 : Nat.Prime 37309 := by norm_num
private theorem prime_twentySevenY_1222615931 : Nat.Prime 1222615931 := by
  apply lucas_primality 1222615931 (2 : ZMod 1222615931)
  · rw [← twentySevenYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 1), (29, 1), (113, 1), (37309, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 1), (29, 1), (113, 1), (37309, 1)] : List FactorBlock).map factorBlockValue).prod = 1222615931 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentySevenY_2
      · exact prime_twentySevenY_5
      · exact prime_twentySevenY_29
      · exact prime_twentySevenY_113
      · exact prime_twentySevenY_37309
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1222615931) ^ 611307965 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (2 : ZMod 1222615931) ^ 244523186 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (2 : ZMod 1222615931) ^ 42159170 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (2 : ZMod 1222615931) ^ 10819610 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (2 : ZMod 1222615931) ^ 32770 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide

private theorem prime_twentySevenY_2531 : Nat.Prime 2531 := by norm_num
private theorem prime_twentySevenY_6763 : Nat.Prime 6763 := by norm_num
private theorem prime_twentySevenY_462094662389 : Nat.Prime 462094662389 := by
  apply lucas_primality 462094662389 (2 : ZMod 462094662389)
  · rw [← twentySevenYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (17, 1), (397, 1), (2531, 1), (6763, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (17, 1), (397, 1), (2531, 1), (6763, 1)] : List FactorBlock).map factorBlockValue).prod = 462094662389 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentySevenY_2
      · exact prime_twentySevenY_17
      · exact prime_twentySevenY_397
      · exact prime_twentySevenY_2531
      · exact prime_twentySevenY_6763
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 462094662389) ^ 231047331194 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (2 : ZMod 462094662389) ^ 27182038964 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (2 : ZMod 462094662389) ^ 1163966404 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (2 : ZMod 462094662389) ^ 182573948 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (2 : ZMod 462094662389) ^ 68326876 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide

private theorem prime_twentySevenY_1667237541899513 : Nat.Prime 1667237541899513 := by
  apply lucas_primality 1667237541899513 (3 : ZMod 1667237541899513)
  · rw [← twentySevenYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (11, 1), (41, 1), (462094662389, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (11, 1), (41, 1), (462094662389, 1)] : List FactorBlock).map factorBlockValue).prod = 1667237541899513 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentySevenY_2
      · exact prime_twentySevenY_11
      · exact prime_twentySevenY_41
      · exact prime_twentySevenY_462094662389
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1667237541899513) ^ 833618770949756 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (3 : ZMod 1667237541899513) ^ 151567049263592 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (3 : ZMod 1667237541899513) ^ 40664330290232 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (3 : ZMod 1667237541899513) ^ 3608 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide

private theorem prime_twentySevenY_483498887150858771 : Nat.Prime 483498887150858771 := by
  apply lucas_primality 483498887150858771 (2 : ZMod 483498887150858771)
  · rw [← twentySevenYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 1), (29, 1), (1667237541899513, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 1), (29, 1), (1667237541899513, 1)] : List FactorBlock).map factorBlockValue).prod = 483498887150858771 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentySevenY_2
      · exact prime_twentySevenY_5
      · exact prime_twentySevenY_29
      · exact prime_twentySevenY_1667237541899513
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 483498887150858771) ^ 241749443575429385 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (2 : ZMod 483498887150858771) ^ 96699777430171754 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (2 : ZMod 483498887150858771) ^ 16672375418995130 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (2 : ZMod 483498887150858771) ^ 290 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide

private theorem prime_twentySevenY_997 : Nat.Prime 997 := by norm_num
private theorem prime_twentySevenY_12024319 : Nat.Prime 12024319 := by norm_num
private theorem prime_twentySevenY_47947 : Nat.Prime 47947 := by norm_num
private theorem prime_twentySevenY_31645021 : Nat.Prime 31645021 := by
  apply lucas_primality 31645021 (2 : ZMod 31645021)
  · rw [← twentySevenYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (5, 1), (11, 1), (47947, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (5, 1), (11, 1), (47947, 1)] : List FactorBlock).map factorBlockValue).prod = 31645021 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentySevenY_2
      · exact prime_twentySevenY_3
      · exact prime_twentySevenY_5
      · exact prime_twentySevenY_11
      · exact prime_twentySevenY_47947
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 31645021) ^ 15822510 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (2 : ZMod 31645021) ^ 10548340 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (2 : ZMod 31645021) ^ 6329004 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (2 : ZMod 31645021) ^ 2876820 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (2 : ZMod 31645021) ^ 660 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide

private theorem prime_twentySevenY_172633 : Nat.Prime 172633 := by norm_num
private theorem prime_twentySevenY_1529873647 : Nat.Prime 1529873647 := by
  apply lucas_primality 1529873647 (3 : ZMod 1529873647)
  · rw [← twentySevenYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (7, 1), (211, 1), (172633, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (7, 1), (211, 1), (172633, 1)] : List FactorBlock).map factorBlockValue).prod = 1529873647 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentySevenY_2
      · exact prime_twentySevenY_3
      · exact prime_twentySevenY_7
      · exact prime_twentySevenY_211
      · exact prime_twentySevenY_172633
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1529873647) ^ 764936823 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (3 : ZMod 1529873647) ^ 509957882 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (3 : ZMod 1529873647) ^ 218553378 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (3 : ZMod 1529873647) ^ 7250586 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (3 : ZMod 1529873647) ^ 8862 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide

private theorem prime_twentySevenY_8731 : Nat.Prime 8731 := by norm_num
private theorem prime_twentySevenY_13777811 : Nat.Prime 13777811 := by norm_num
private theorem prime_twentySevenY_413334331 : Nat.Prime 413334331 := by
  apply lucas_primality 413334331 (2 : ZMod 413334331)
  · rw [← twentySevenYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (5, 1), (13777811, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (5, 1), (13777811, 1)] : List FactorBlock).map factorBlockValue).prod = 413334331 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentySevenY_2
      · exact prime_twentySevenY_3
      · exact prime_twentySevenY_5
      · exact prime_twentySevenY_13777811
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 413334331) ^ 206667165 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (2 : ZMod 413334331) ^ 137778110 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (2 : ZMod 413334331) ^ 82666866 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (2 : ZMod 413334331) ^ 30 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide

private theorem prime_twentySevenY_90143041 : Nat.Prime 90143041 := by
  apply lucas_primality 90143041 (11 : ZMod 90143041)
  · rw [← twentySevenYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 6), (3, 1), (5, 1), (13, 1), (31, 1), (233, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 6), (3, 1), (5, 1), (13, 1), (31, 1), (233, 1)] : List FactorBlock).map factorBlockValue).prod = 90143041 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_twentySevenY_2
      · exact prime_twentySevenY_3
      · exact prime_twentySevenY_5
      · exact prime_twentySevenY_13
      · exact prime_twentySevenY_31
      · exact prime_twentySevenY_233
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 90143041) ^ 45071520 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (11 : ZMod 90143041) ^ 30047680 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (11 : ZMod 90143041) ^ 18028608 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (11 : ZMod 90143041) ^ 6934080 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (11 : ZMod 90143041) ^ 2907840 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (11 : ZMod 90143041) ^ 386880 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide

private theorem prime_twentySevenY_157952242161841 : Nat.Prime 157952242161841 := by
  apply lucas_primality 157952242161841 (11 : ZMod 157952242161841)
  · rw [← twentySevenYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 4), (3, 1), (5, 1), (7, 2), (149, 1), (90143041, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 4), (3, 1), (5, 1), (7, 2), (149, 1), (90143041, 1)] : List FactorBlock).map factorBlockValue).prod = 157952242161841 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_twentySevenY_2
      · exact prime_twentySevenY_3
      · exact prime_twentySevenY_5
      · exact prime_twentySevenY_7
      · exact prime_twentySevenY_149
      · exact prime_twentySevenY_90143041
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 157952242161841) ^ 78976121080920 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (11 : ZMod 157952242161841) ^ 52650747387280 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (11 : ZMod 157952242161841) ^ 31590448432368 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (11 : ZMod 157952242161841) ^ 22564606023120 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (11 : ZMod 157952242161841) ^ 1060082162160 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (11 : ZMod 157952242161841) ^ 1752240 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide

private theorem prime_twentySevenY_3691 : Nat.Prime 3691 := by norm_num
private theorem prime_twentySevenY_401987 : Nat.Prime 401987 := by norm_num
private theorem prime_twentySevenY_86843 : Nat.Prime 86843 := by norm_num
private theorem prime_twentySevenY_171877 : Nat.Prime 171877 := by norm_num
private theorem prime_twentySevenY_3074820748067 : Nat.Prime 3074820748067 := by
  apply lucas_primality 3074820748067 (2 : ZMod 3074820748067)
  · rw [← twentySevenYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (103, 1), (86843, 1), (171877, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (103, 1), (86843, 1), (171877, 1)] : List FactorBlock).map factorBlockValue).prod = 3074820748067 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentySevenY_2
      · exact prime_twentySevenY_103
      · exact prime_twentySevenY_86843
      · exact prime_twentySevenY_171877
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 3074820748067) ^ 1537410374033 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (2 : ZMod 3074820748067) ^ 29852628622 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (2 : ZMod 3074820748067) ^ 35406662 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (2 : ZMod 3074820748067) ^ 17889658 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide

private theorem prime_twentySevenY_43047490472939 : Nat.Prime 43047490472939 := by
  apply lucas_primality 43047490472939 (7 : ZMod 43047490472939)
  · rw [← twentySevenYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (7, 1), (3074820748067, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (7, 1), (3074820748067, 1)] : List FactorBlock).map factorBlockValue).prod = 43047490472939 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twentySevenY_2
      · exact prime_twentySevenY_7
      · exact prime_twentySevenY_3074820748067
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 43047490472939) ^ 21523745236469 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (7 : ZMod 43047490472939) ^ 6149641496134 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (7 : ZMod 43047490472939) ^ 14 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide

private theorem prime_twentySevenY_377440396466729153 : Nat.Prime 377440396466729153 := by
  apply lucas_primality 377440396466729153 (3 : ZMod 377440396466729153)
  · rw [← twentySevenYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 6), (137, 1), (43047490472939, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 6), (137, 1), (43047490472939, 1)] : List FactorBlock).map factorBlockValue).prod = 377440396466729153 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twentySevenY_2
      · exact prime_twentySevenY_137
      · exact prime_twentySevenY_43047490472939
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 377440396466729153) ^ 188720198233364576 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (3 : ZMod 377440396466729153) ^ 2755039390268096 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (3 : ZMod 377440396466729153) ^ 8768 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide

private theorem prime_twentySevenY_1109 : Nat.Prime 1109 := by norm_num
private theorem prime_twentySevenY_2111303 : Nat.Prime 2111303 := by norm_num
private theorem prime_twentySevenY_237513142289 : Nat.Prime 237513142289 := by
  apply lucas_primality 237513142289 (3 : ZMod 237513142289)
  · rw [← twentySevenYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 4), (79, 1), (89, 1), (2111303, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 4), (79, 1), (89, 1), (2111303, 1)] : List FactorBlock).map factorBlockValue).prod = 237513142289 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentySevenY_2
      · exact prime_twentySevenY_79
      · exact prime_twentySevenY_89
      · exact prime_twentySevenY_2111303
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 237513142289) ^ 118756571144 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (3 : ZMod 237513142289) ^ 3006495472 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (3 : ZMod 237513142289) ^ 2668686992 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (3 : ZMod 237513142289) ^ 112496 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide

private theorem prime_twentySevenY_503 : Nat.Prime 503 := by norm_num
private theorem prime_twentySevenY_1258781 : Nat.Prime 1258781 := by norm_num
private theorem prime_twentySevenY_2089450581901 : Nat.Prime 2089450581901 := by
  apply lucas_primality 2089450581901 (14 : ZMod 2089450581901)
  · rw [← twentySevenYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (5, 2), (11, 1), (503, 1), (1258781, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (5, 2), (11, 1), (503, 1), (1258781, 1)] : List FactorBlock).map factorBlockValue).prod = 2089450581901 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_twentySevenY_2
      · exact prime_twentySevenY_3
      · exact prime_twentySevenY_5
      · exact prime_twentySevenY_11
      · exact prime_twentySevenY_503
      · exact prime_twentySevenY_1258781
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (14 : ZMod 2089450581901) ^ 1044725290950 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (14 : ZMod 2089450581901) ^ 696483527300 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (14 : ZMod 2089450581901) ^ 417890116380 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (14 : ZMod 2089450581901) ^ 189950052900 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (14 : ZMod 2089450581901) ^ 4153977300 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (14 : ZMod 2089450581901) ^ 1659900 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide

private theorem prime_twentySevenY_426757 : Nat.Prime 426757 := by norm_num
private theorem prime_twentySevenY_10506247 : Nat.Prime 10506247 := by norm_num
private theorem prime_twentySevenY_201589 : Nat.Prime 201589 := by norm_num
private theorem prime_twentySevenY_2558093 : Nat.Prime 2558093 := by norm_num
private theorem prime_twentySevenY_120669917887819 : Nat.Prime 120669917887819 := by
  apply lucas_primality 120669917887819 (2 : ZMod 120669917887819)
  · rw [← twentySevenYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 2), (13, 1), (201589, 1), (2558093, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 2), (13, 1), (201589, 1), (2558093, 1)] : List FactorBlock).map factorBlockValue).prod = 120669917887819 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentySevenY_2
      · exact prime_twentySevenY_3
      · exact prime_twentySevenY_13
      · exact prime_twentySevenY_201589
      · exact prime_twentySevenY_2558093
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 120669917887819) ^ 60334958943909 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (2 : ZMod 120669917887819) ^ 40223305962606 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (2 : ZMod 120669917887819) ^ 9282301375986 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (2 : ZMod 120669917887819) ^ 598593762 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (2 : ZMod 120669917887819) ^ 47171826 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide

private theorem prime_twentySevenY_11953 : Nat.Prime 11953 := by norm_num
private theorem prime_twentySevenY_339907 : Nat.Prime 339907 := by norm_num
private theorem prime_twentySevenY_26921 : Nat.Prime 26921 := by norm_num
private theorem prime_twentySevenY_96293 : Nat.Prime 96293 := by norm_num
private theorem prime_twentySevenY_115327 : Nat.Prime 115327 := by norm_num
private theorem prime_twentySevenY_1793775758729587 : Nat.Prime 1793775758729587 := by
  apply lucas_primality 1793775758729587 (2 : ZMod 1793775758729587)
  · rw [← twentySevenYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (26921, 1), (96293, 1), (115327, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (26921, 1), (96293, 1), (115327, 1)] : List FactorBlock).map factorBlockValue).prod = 1793775758729587 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentySevenY_2
      · exact prime_twentySevenY_3
      · exact prime_twentySevenY_26921
      · exact prime_twentySevenY_96293
      · exact prime_twentySevenY_115327
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1793775758729587) ^ 896887879364793 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (2 : ZMod 1793775758729587) ^ 597925252909862 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (2 : ZMod 1793775758729587) ^ 66631096866 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (2 : ZMod 1793775758729587) ^ 18628309002 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (2 : ZMod 1793775758729587) ^ 15553823118 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide

private theorem prime_twentySevenY_4816121 : Nat.Prime 4816121 := by norm_num
private theorem prime_twentySevenY_7480679 : Nat.Prime 7480679 := by norm_num
private theorem prime_twentySevenY_1187 : Nat.Prime 1187 := by norm_num
private theorem prime_twentySevenY_15313 : Nat.Prime 15313 := by norm_num
private theorem prime_twentySevenY_133183 : Nat.Prime 133183 := by norm_num
private theorem prime_twentySevenY_14524829569039 : Nat.Prime 14524829569039 := by
  apply lucas_primality 14524829569039 (3 : ZMod 14524829569039)
  · rw [← twentySevenYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (1187, 1), (15313, 1), (133183, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (1187, 1), (15313, 1), (133183, 1)] : List FactorBlock).map factorBlockValue).prod = 14524829569039 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentySevenY_2
      · exact prime_twentySevenY_3
      · exact prime_twentySevenY_1187
      · exact prime_twentySevenY_15313
      · exact prime_twentySevenY_133183
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 14524829569039) ^ 7262414784519 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (3 : ZMod 14524829569039) ^ 4841609856346 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (3 : ZMod 14524829569039) ^ 12236587674 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (3 : ZMod 14524829569039) ^ 948529326 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (3 : ZMod 14524829569039) ^ 109059186 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide

private theorem prime_twentySevenY_386047 : Nat.Prime 386047 := by norm_num
private theorem prime_twentySevenY_27743 : Nat.Prime 27743 := by norm_num
private theorem prime_twentySevenY_2446488713 : Nat.Prime 2446488713 := by
  apply lucas_primality 2446488713 (3 : ZMod 2446488713)
  · rw [← twentySevenYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (73, 1), (151, 1), (27743, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (73, 1), (151, 1), (27743, 1)] : List FactorBlock).map factorBlockValue).prod = 2446488713 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentySevenY_2
      · exact prime_twentySevenY_73
      · exact prime_twentySevenY_151
      · exact prime_twentySevenY_27743
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 2446488713) ^ 1223244356 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (3 : ZMod 2446488713) ^ 33513544 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (3 : ZMod 2446488713) ^ 16201912 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (3 : ZMod 2446488713) ^ 88184 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide

private theorem prime_twentySevenY_545135169191 : Nat.Prime 545135169191 := by
  apply lucas_primality 545135169191 (7 : ZMod 545135169191)
  · rw [← twentySevenYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 1), (53, 1), (271, 1), (461, 1), (8233, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 1), (53, 1), (271, 1), (461, 1), (8233, 1)] : List FactorBlock).map factorBlockValue).prod = 545135169191 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_twentySevenY_2
      · exact prime_twentySevenY_5
      · exact prime_twentySevenY_53
      · exact prime_twentySevenY_271
      · exact prime_twentySevenY_461
      · exact prime_twentySevenY_8233
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 545135169191) ^ 272567584595 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (7 : ZMod 545135169191) ^ 109027033838 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (7 : ZMod 545135169191) ^ 10285569230 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (7 : ZMod 545135169191) ^ 2011568890 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (7 : ZMod 545135169191) ^ 1182505790 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (7 : ZMod 545135169191) ^ 66213430 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide

private theorem prime_twentySevenY_727 : Nat.Prime 727 := by norm_num
private theorem prime_twentySevenY_517267 : Nat.Prime 517267 := by norm_num
private theorem prime_twentySevenY_40346827 : Nat.Prime 40346827 := by
  apply lucas_primality 40346827 (2 : ZMod 40346827)
  · rw [← twentySevenYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (13, 1), (517267, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (13, 1), (517267, 1)] : List FactorBlock).map factorBlockValue).prod = 40346827 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentySevenY_2
      · exact prime_twentySevenY_3
      · exact prime_twentySevenY_13
      · exact prime_twentySevenY_517267
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 40346827) ^ 20173413 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (2 : ZMod 40346827) ^ 13448942 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (2 : ZMod 40346827) ^ 3103602 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (2 : ZMod 40346827) ^ 78 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide

private theorem prime_twentySevenY_4159 : Nat.Prime 4159 := by norm_num
private theorem prime_twentySevenY_16453 : Nat.Prime 16453 := by norm_num
private theorem prime_twentySevenY_910838081 : Nat.Prime 910838081 := by
  apply lucas_primality 910838081 (3 : ZMod 910838081)
  · rw [← twentySevenYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 6), (5, 1), (173, 1), (16453, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 6), (5, 1), (173, 1), (16453, 1)] : List FactorBlock).map factorBlockValue).prod = 910838081 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentySevenY_2
      · exact prime_twentySevenY_5
      · exact prime_twentySevenY_173
      · exact prime_twentySevenY_16453
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 910838081) ^ 455419040 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (3 : ZMod 910838081) ^ 182167616 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (3 : ZMod 910838081) ^ 5264960 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (3 : ZMod 910838081) ^ 55360 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide

private theorem prime_twentySevenY_75763511577581 : Nat.Prime 75763511577581 := by
  apply lucas_primality 75763511577581 (3 : ZMod 75763511577581)
  · rw [← twentySevenYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (5, 1), (4159, 1), (910838081, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (5, 1), (4159, 1), (910838081, 1)] : List FactorBlock).map factorBlockValue).prod = 75763511577581 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentySevenY_2
      · exact prime_twentySevenY_5
      · exact prime_twentySevenY_4159
      · exact prime_twentySevenY_910838081
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 75763511577581) ^ 37881755788790 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (3 : ZMod 75763511577581) ^ 15152702315516 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (3 : ZMod 75763511577581) ^ 18216761620 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (3 : ZMod 75763511577581) ^ 83180 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide

private theorem prime_twentySevenY_17274080639688469 : Nat.Prime 17274080639688469 := by
  apply lucas_primality 17274080639688469 (2 : ZMod 17274080639688469)
  · rw [← twentySevenYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (19, 1), (75763511577581, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (19, 1), (75763511577581, 1)] : List FactorBlock).map factorBlockValue).prod = 17274080639688469 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentySevenY_2
      · exact prime_twentySevenY_3
      · exact prime_twentySevenY_19
      · exact prime_twentySevenY_75763511577581
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 17274080639688469) ^ 8637040319844234 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (2 : ZMod 17274080639688469) ^ 5758026879896156 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (2 : ZMod 17274080639688469) ^ 909162138930972 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (2 : ZMod 17274080639688469) ^ 228 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide

private theorem prime_twentySevenY_6841 : Nat.Prime 6841 := by norm_num
private theorem prime_twentySevenY_31147 : Nat.Prime 31147 := by norm_num
private theorem prime_twentySevenY_487709 : Nat.Prime 487709 := by norm_num
private theorem prime_twentySevenY_839 : Nat.Prime 839 := by norm_num
private theorem prime_twentySevenY_4409 : Nat.Prime 4409 := by norm_num
private theorem prime_twentySevenY_7361310491 : Nat.Prime 7361310491 := by
  apply lucas_primality 7361310491 (6 : ZMod 7361310491)
  · rw [← twentySevenYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 1), (199, 1), (839, 1), (4409, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 1), (199, 1), (839, 1), (4409, 1)] : List FactorBlock).map factorBlockValue).prod = 7361310491 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentySevenY_2
      · exact prime_twentySevenY_5
      · exact prime_twentySevenY_199
      · exact prime_twentySevenY_839
      · exact prime_twentySevenY_4409
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 7361310491) ^ 3680655245 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (6 : ZMod 7361310491) ^ 1472262098 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (6 : ZMod 7361310491) ^ 36991510 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (6 : ZMod 7361310491) ^ 8773910 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (6 : ZMod 7361310491) ^ 1669610 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide

private theorem prime_twentySevenY_131 : Nat.Prime 131 := by norm_num
private theorem prime_twentySevenY_8377 : Nat.Prime 8377 := by norm_num
private theorem prime_twentySevenY_310243 : Nat.Prime 310243 := by norm_num
private theorem prime_twentySevenY_2179 : Nat.Prime 2179 := by norm_num
private theorem prime_twentySevenY_284357 : Nat.Prime 284357 := by norm_num
private theorem prime_twentySevenY_4137394351 : Nat.Prime 4137394351 := by
  apply lucas_primality 4137394351 (3 : ZMod 4137394351)
  · rw [← twentySevenYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (5, 2), (97, 1), (284357, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (5, 2), (97, 1), (284357, 1)] : List FactorBlock).map factorBlockValue).prod = 4137394351 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentySevenY_2
      · exact prime_twentySevenY_3
      · exact prime_twentySevenY_5
      · exact prime_twentySevenY_97
      · exact prime_twentySevenY_284357
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 4137394351) ^ 2068697175 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (3 : ZMod 4137394351) ^ 1379131450 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (3 : ZMod 4137394351) ^ 827478870 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (3 : ZMod 4137394351) ^ 42653550 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (3 : ZMod 4137394351) ^ 14550 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide

private theorem prime_twentySevenY_1442461166532641 : Nat.Prime 1442461166532641 := by
  apply lucas_primality 1442461166532641 (3 : ZMod 1442461166532641)
  · rw [← twentySevenYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 5), (5, 1), (2179, 1), (4137394351, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 5), (5, 1), (2179, 1), (4137394351, 1)] : List FactorBlock).map factorBlockValue).prod = 1442461166532641 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentySevenY_2
      · exact prime_twentySevenY_5
      · exact prime_twentySevenY_2179
      · exact prime_twentySevenY_4137394351
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1442461166532641) ^ 721230583266320 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (3 : ZMod 1442461166532641) ^ 288492233306528 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (3 : ZMod 1442461166532641) ^ 661983096160 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (3 : ZMod 1442461166532641) ^ 348640 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide

private theorem prime_twentySevenY_1277 : Nat.Prime 1277 := by norm_num
private theorem prime_twentySevenY_23539 : Nat.Prime 23539 := by norm_num
private theorem prime_twentySevenY_8521 : Nat.Prime 8521 := by norm_num
private theorem prime_twentySevenY_1192327 : Nat.Prime 1192327 := by norm_num
private theorem prime_twentySevenY_101598183671 : Nat.Prime 101598183671 := by
  apply lucas_primality 101598183671 (17 : ZMod 101598183671)
  · rw [← twentySevenYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 1), (8521, 1), (1192327, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 1), (8521, 1), (1192327, 1)] : List FactorBlock).map factorBlockValue).prod = 101598183671 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentySevenY_2
      · exact prime_twentySevenY_5
      · exact prime_twentySevenY_8521
      · exact prime_twentySevenY_1192327
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (17 : ZMod 101598183671) ^ 50799091835 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (17 : ZMod 101598183671) ^ 20319636734 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (17 : ZMod 101598183671) ^ 11923270 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (17 : ZMod 101598183671) ^ 85210 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide

private theorem prime_twentySevenY_203196367343 : Nat.Prime 203196367343 := by
  apply lucas_primality 203196367343 (5 : ZMod 203196367343)
  · rw [← twentySevenYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (101598183671, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (101598183671, 1)] : List FactorBlock).map factorBlockValue).prod = 203196367343 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_twentySevenY_2
      · exact prime_twentySevenY_101598183671
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 203196367343) ^ 101598183671 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (5 : ZMod 203196367343) ^ 2 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide

private theorem prime_twentySevenY_1211050349364281 : Nat.Prime 1211050349364281 := by
  apply lucas_primality 1211050349364281 (3 : ZMod 1211050349364281)
  · rw [← twentySevenYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (5, 1), (149, 1), (203196367343, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (5, 1), (149, 1), (203196367343, 1)] : List FactorBlock).map factorBlockValue).prod = 1211050349364281 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentySevenY_2
      · exact prime_twentySevenY_5
      · exact prime_twentySevenY_149
      · exact prime_twentySevenY_203196367343
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1211050349364281) ^ 605525174682140 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (3 : ZMod 1211050349364281) ^ 242210069872856 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (3 : ZMod 1211050349364281) ^ 8127854693720 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (3 : ZMod 1211050349364281) ^ 5960 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide

private theorem prime_twentySevenY_16090014941653837367 : Nat.Prime 16090014941653837367 := by
  apply lucas_primality 16090014941653837367 (5 : ZMod 16090014941653837367)
  · rw [← twentySevenYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (7, 1), (13, 1), (73, 1), (1211050349364281, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (7, 1), (13, 1), (73, 1), (1211050349364281, 1)] : List FactorBlock).map factorBlockValue).prod = 16090014941653837367 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentySevenY_2
      · exact prime_twentySevenY_7
      · exact prime_twentySevenY_13
      · exact prime_twentySevenY_73
      · exact prime_twentySevenY_1211050349364281
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 16090014941653837367) ^ 8045007470826918683 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (5 : ZMod 16090014941653837367) ^ 2298573563093405338 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (5 : ZMod 16090014941653837367) ^ 1237693457050295182 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (5 : ZMod 16090014941653837367) ^ 220411163584299142 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (5 : ZMod 16090014941653837367) ^ 13286 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide

private theorem prime_twentySevenY_5827 : Nat.Prime 5827 := by norm_num
private theorem prime_twentySevenY_797 : Nat.Prime 797 := by norm_num
private theorem prime_twentySevenY_18637 : Nat.Prime 18637 := by norm_num
private theorem prime_twentySevenY_2741 : Nat.Prime 2741 := by norm_num
private theorem prime_twentySevenY_22618733 : Nat.Prime 22618733 := by
  apply lucas_primality 22618733 (2 : ZMod 22618733)
  · rw [← twentySevenYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (2063, 1), (2741, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (2063, 1), (2741, 1)] : List FactorBlock).map factorBlockValue).prod = 22618733 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twentySevenY_2
      · exact prime_twentySevenY_2063
      · exact prime_twentySevenY_2741
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 22618733) ^ 11309366 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (2 : ZMod 22618733) ^ 10964 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (2 : ZMod 22618733) ^ 8252 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide

private theorem prime_twentySevenY_47499339301 : Nat.Prime 47499339301 := by
  apply lucas_primality 47499339301 (11 : ZMod 47499339301)
  · rw [← twentySevenYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (5, 2), (7, 1), (22618733, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (5, 2), (7, 1), (22618733, 1)] : List FactorBlock).map factorBlockValue).prod = 47499339301 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentySevenY_2
      · exact prime_twentySevenY_3
      · exact prime_twentySevenY_5
      · exact prime_twentySevenY_7
      · exact prime_twentySevenY_22618733
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 47499339301) ^ 23749669650 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (11 : ZMod 47499339301) ^ 15833113100 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (11 : ZMod 47499339301) ^ 9499867860 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (11 : ZMod 47499339301) ^ 6785619900 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (11 : ZMod 47499339301) ^ 2100 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide

private theorem prime_twentySevenY_64029109377749 : Nat.Prime 64029109377749 := by
  apply lucas_primality 64029109377749 (2 : ZMod 64029109377749)
  · rw [← twentySevenYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (337, 1), (47499339301, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (337, 1), (47499339301, 1)] : List FactorBlock).map factorBlockValue).prod = 64029109377749 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twentySevenY_2
      · exact prime_twentySevenY_337
      · exact prime_twentySevenY_47499339301
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 64029109377749) ^ 32014554688874 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (2 : ZMod 64029109377749) ^ 189997357204 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (2 : ZMod 64029109377749) ^ 1348 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide

private theorem prime_twentySevenY_2386621022946216227 : Nat.Prime 2386621022946216227 := by
  apply lucas_primality 2386621022946216227 (2 : ZMod 2386621022946216227)
  · rw [← twentySevenYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (18637, 1), (64029109377749, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (18637, 1), (64029109377749, 1)] : List FactorBlock).map factorBlockValue).prod = 2386621022946216227 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twentySevenY_2
      · exact prime_twentySevenY_18637
      · exact prime_twentySevenY_64029109377749
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 2386621022946216227) ^ 1193310511473108113 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (2 : ZMod 2386621022946216227) ^ 128058218755498 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (2 : ZMod 2386621022946216227) ^ 37274 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide

private theorem prime_twentySevenY_5478154431229826878806721 : Nat.Prime 5478154431229826878806721 := by
  apply lucas_primality 5478154431229826878806721 (23 : ZMod 5478154431229826878806721)
  · rw [← twentySevenYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 6), (3, 2), (5, 1), (797, 1), (2386621022946216227, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 6), (3, 2), (5, 1), (797, 1), (2386621022946216227, 1)] : List FactorBlock).map factorBlockValue).prod = 5478154431229826878806721 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentySevenY_2
      · exact prime_twentySevenY_3
      · exact prime_twentySevenY_5
      · exact prime_twentySevenY_797
      · exact prime_twentySevenY_2386621022946216227
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (23 : ZMod 5478154431229826878806721) ^ 2739077215614913439403360 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (23 : ZMod 5478154431229826878806721) ^ 1826051477076608959602240 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (23 : ZMod 5478154431229826878806721) ^ 1095630886245965375761344 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (23 : ZMod 5478154431229826878806721) ^ 6873468546085102733760 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (23 : ZMod 5478154431229826878806721) ^ 2295360 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide

private theorem prime_twentySevenY_101 : Nat.Prime 101 := by norm_num
private theorem prime_twentySevenY_1549 : Nat.Prime 1549 := by norm_num
private theorem prime_twentySevenY_7333 : Nat.Prime 7333 := by norm_num
private theorem prime_twentySevenY_33614473 : Nat.Prime 33614473 := by
  apply lucas_primality 33614473 (5 : ZMod 33614473)
  · rw [← twentySevenYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (3, 1), (191, 1), (7333, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (3, 1), (191, 1), (7333, 1)] : List FactorBlock).map factorBlockValue).prod = 33614473 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentySevenY_2
      · exact prime_twentySevenY_3
      · exact prime_twentySevenY_191
      · exact prime_twentySevenY_7333
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 33614473) ^ 16807236 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (5 : ZMod 33614473) ^ 11204824 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (5 : ZMod 33614473) ^ 175992 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (5 : ZMod 33614473) ^ 4584 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide

private theorem prime_twentySevenY_9202883 : Nat.Prime 9202883 := by norm_num
private theorem prime_twentySevenY_48094266559 : Nat.Prime 48094266559 := by
  apply lucas_primality 48094266559 (11 : ZMod 48094266559)
  · rw [← twentySevenYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (13, 1), (67, 1), (9202883, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (13, 1), (67, 1), (9202883, 1)] : List FactorBlock).map factorBlockValue).prod = 48094266559 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentySevenY_2
      · exact prime_twentySevenY_3
      · exact prime_twentySevenY_13
      · exact prime_twentySevenY_67
      · exact prime_twentySevenY_9202883
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 48094266559) ^ 24047133279 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (11 : ZMod 48094266559) ^ 16031422186 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (11 : ZMod 48094266559) ^ 3699558966 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (11 : ZMod 48094266559) ^ 717824874 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (11 : ZMod 48094266559) ^ 5226 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide

private theorem prime_twentySevenY_11157869841689 : Nat.Prime 11157869841689 := by
  apply lucas_primality 11157869841689 (3 : ZMod 11157869841689)
  · rw [← twentySevenYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (29, 1), (48094266559, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (29, 1), (48094266559, 1)] : List FactorBlock).map factorBlockValue).prod = 11157869841689 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twentySevenY_2
      · exact prime_twentySevenY_29
      · exact prime_twentySevenY_48094266559
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 11157869841689) ^ 5578934920844 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (3 : ZMod 11157869841689) ^ 384754132472 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (3 : ZMod 11157869841689) ^ 232 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide

private theorem prime_twentySevenY_89262958733513 : Nat.Prime 89262958733513 := by
  apply lucas_primality 89262958733513 (3 : ZMod 89262958733513)
  · rw [← twentySevenYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (11157869841689, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (11157869841689, 1)] : List FactorBlock).map factorBlockValue).prod = 89262958733513 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_twentySevenY_2
      · exact prime_twentySevenY_11157869841689
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 89262958733513) ^ 44631479366756 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (3 : ZMod 89262958733513) ^ 8 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide

private theorem prime_twentySevenY_1399 : Nat.Prime 1399 := by norm_num
private theorem prime_twentySevenY_12941 : Nat.Prime 12941 := by norm_num
private theorem prime_twentySevenY_17389 : Nat.Prime 17389 := by norm_num
private theorem prime_twentySevenY_25214051 : Nat.Prime 25214051 := by
  apply lucas_primality 25214051 (6 : ZMod 25214051)
  · rw [← twentySevenYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 2), (29, 1), (17389, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 2), (29, 1), (17389, 1)] : List FactorBlock).map factorBlockValue).prod = 25214051 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentySevenY_2
      · exact prime_twentySevenY_5
      · exact prime_twentySevenY_29
      · exact prime_twentySevenY_17389
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 25214051) ^ 12607025 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (6 : ZMod 25214051) ^ 5042810 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (6 : ZMod 25214051) ^ 869450 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (6 : ZMod 25214051) ^ 1450 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide

private theorem prime_twentySevenY_2773545611 : Nat.Prime 2773545611 := by
  apply lucas_primality 2773545611 (2 : ZMod 2773545611)
  · rw [← twentySevenYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 1), (11, 1), (25214051, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 1), (11, 1), (25214051, 1)] : List FactorBlock).map factorBlockValue).prod = 2773545611 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentySevenY_2
      · exact prime_twentySevenY_5
      · exact prime_twentySevenY_11
      · exact prime_twentySevenY_25214051
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 2773545611) ^ 1386772805 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (2 : ZMod 2773545611) ^ 554709122 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (2 : ZMod 2773545611) ^ 252140510 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (2 : ZMod 2773545611) ^ 110 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide

private theorem prime_twentySevenY_11970622857077 : Nat.Prime 11970622857077 := by
  apply lucas_primality 11970622857077 (2 : ZMod 11970622857077)
  · rw [← twentySevenYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (13, 1), (83, 1), (2773545611, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (13, 1), (83, 1), (2773545611, 1)] : List FactorBlock).map factorBlockValue).prod = 11970622857077 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentySevenY_2
      · exact prime_twentySevenY_13
      · exact prime_twentySevenY_83
      · exact prime_twentySevenY_2773545611
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 11970622857077) ^ 5985311428538 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (2 : ZMod 11970622857077) ^ 920817142852 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (2 : ZMod 11970622857077) ^ 144224371772 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (2 : ZMod 11970622857077) ^ 4316 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide

private theorem prime_twentySevenY_55113911370054181597633 : Nat.Prime 55113911370054181597633 := by
  apply lucas_primality 55113911370054181597633 (5 : ZMod 55113911370054181597633)
  · rw [← twentySevenYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 6), (3, 1), (17, 1), (109, 1), (12941, 1), (11970622857077, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 6), (3, 1), (17, 1), (109, 1), (12941, 1), (11970622857077, 1)] : List FactorBlock).map factorBlockValue).prod = 55113911370054181597633 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_twentySevenY_2
      · exact prime_twentySevenY_3
      · exact prime_twentySevenY_17
      · exact prime_twentySevenY_109
      · exact prime_twentySevenY_12941
      · exact prime_twentySevenY_11970622857077
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 55113911370054181597633) ^ 27556955685027090798816 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (5 : ZMod 55113911370054181597633) ^ 18371303790018060532544 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (5 : ZMod 55113911370054181597633) ^ 3241994786473775388096 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (5 : ZMod 55113911370054181597633) ^ 505632214404166803648 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (5 : ZMod 55113911370054181597633) ^ 4258860317599426752 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (5 : ZMod 55113911370054181597633) ^ 4604097216 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide

private theorem prime_twentySevenY_330683468220325089585799 : Nat.Prime 330683468220325089585799 := by
  apply lucas_primality 330683468220325089585799 (6 : ZMod 330683468220325089585799)
  · rw [← twentySevenYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (55113911370054181597633, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (55113911370054181597633, 1)] : List FactorBlock).map factorBlockValue).prod = 330683468220325089585799 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twentySevenY_2
      · exact prime_twentySevenY_3
      · exact prime_twentySevenY_55113911370054181597633
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (6 : ZMod 330683468220325089585799) ^ 165341734110162544792899 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (6 : ZMod 330683468220325089585799) ^ 110227822740108363195266 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (6 : ZMod 330683468220325089585799) ^ 6 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide

private theorem prime_twentySevenY_45281 : Nat.Prime 45281 := by norm_num
private theorem prime_twentySevenY_1553971 : Nat.Prime 1553971 := by norm_num
private theorem prime_twentySevenY_50581 : Nat.Prime 50581 := by norm_num
private theorem prime_twentySevenY_24885853 : Nat.Prime 24885853 := by
  apply lucas_primality 24885853 (5 : ZMod 24885853)
  · rw [← twentySevenYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (41, 1), (50581, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (41, 1), (50581, 1)] : List FactorBlock).map factorBlockValue).prod = 24885853 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentySevenY_2
      · exact prime_twentySevenY_3
      · exact prime_twentySevenY_41
      · exact prime_twentySevenY_50581
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 24885853) ^ 12442926 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (5 : ZMod 24885853) ^ 8295284 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (5 : ZMod 24885853) ^ 606972 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (5 : ZMod 24885853) ^ 492 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide

private theorem prime_twentySevenY_464062726467157 : Nat.Prime 464062726467157 := by
  apply lucas_primality 464062726467157 (5 : ZMod 464062726467157)
  · rw [← twentySevenYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (1553971, 1), (24885853, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (1553971, 1), (24885853, 1)] : List FactorBlock).map factorBlockValue).prod = 464062726467157 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentySevenY_2
      · exact prime_twentySevenY_3
      · exact prime_twentySevenY_1553971
      · exact prime_twentySevenY_24885853
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 464062726467157) ^ 232031363233578 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (5 : ZMod 464062726467157) ^ 154687575489052 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (5 : ZMod 464062726467157) ^ 298630236 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (5 : ZMod 464062726467157) ^ 18647652 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide

private theorem prime_twentySevenY_10070829414663419606081 : Nat.Prime 10070829414663419606081 := by
  apply lucas_primality 10070829414663419606081 (3 : ZMod 10070829414663419606081)
  · rw [← twentySevenYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 6), (5, 1), (73, 1), (929, 1), (464062726467157, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 6), (5, 1), (73, 1), (929, 1), (464062726467157, 1)] : List FactorBlock).map factorBlockValue).prod = 10070829414663419606081 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentySevenY_2
      · exact prime_twentySevenY_5
      · exact prime_twentySevenY_73
      · exact prime_twentySevenY_929
      · exact prime_twentySevenY_464062726467157
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 10070829414663419606081) ^ 5035414707331709803040 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (3 : ZMod 10070829414663419606081) ^ 2014165882932683921216 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (3 : ZMod 10070829414663419606081) ^ 137956567324156432960 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (3 : ZMod 10070829414663419606081) ^ 10840505290272787520 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (3 : ZMod 10070829414663419606081) ^ 21701440 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide

private theorem prime_twentySevenY_31921205870776201222806763271 : Nat.Prime 31921205870776201222806763271 := by
  apply lucas_primality 31921205870776201222806763271 (7 : ZMod 31921205870776201222806763271)
  · rw [← twentySevenYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 1), (7, 1), (45281, 1), (10070829414663419606081, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 1), (7, 1), (45281, 1), (10070829414663419606081, 1)] : List FactorBlock).map factorBlockValue).prod = 31921205870776201222806763271 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentySevenY_2
      · exact prime_twentySevenY_5
      · exact prime_twentySevenY_7
      · exact prime_twentySevenY_45281
      · exact prime_twentySevenY_10070829414663419606081
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 31921205870776201222806763271) ^ 15960602935388100611403381635 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (7 : ZMod 31921205870776201222806763271) ^ 6384241174155240244561352654 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (7 : ZMod 31921205870776201222806763271) ^ 4560172267253743031829537610 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (7 : ZMod 31921205870776201222806763271) ^ 704958059026439372425670 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (7 : ZMod 31921205870776201222806763271) ^ 3169670 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide

private theorem prime_twentySevenY_373 : Nat.Prime 373 := by norm_num
private theorem prime_twentySevenY_55249 : Nat.Prime 55249 := by norm_num
private theorem prime_twentySevenY_157429 : Nat.Prime 157429 := by norm_num
private theorem prime_twentySevenY_773027 : Nat.Prime 773027 := by norm_num
private theorem prime_twentySevenY_17678041 : Nat.Prime 17678041 := by norm_num
private theorem prime_twentySevenY_176780411 : Nat.Prime 176780411 := by
  apply lucas_primality 176780411 (2 : ZMod 176780411)
  · rw [← twentySevenYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 1), (17678041, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 1), (17678041, 1)] : List FactorBlock).map factorBlockValue).prod = 176780411 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twentySevenY_2
      · exact prime_twentySevenY_5
      · exact prime_twentySevenY_17678041
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 176780411) ^ 88390205 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (2 : ZMod 176780411) ^ 35356082 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (2 : ZMod 176780411) ^ 10 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide

private theorem prime_twentySevenY_6367 : Nat.Prime 6367 := by norm_num
private theorem prime_twentySevenY_58741289 : Nat.Prime 58741289 := by
  apply lucas_primality 58741289 (3 : ZMod 58741289)
  · rw [← twentySevenYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (107, 1), (163, 1), (421, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (107, 1), (163, 1), (421, 1)] : List FactorBlock).map factorBlockValue).prod = 58741289 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentySevenY_2
      · exact prime_twentySevenY_107
      · exact prime_twentySevenY_163
      · exact prime_twentySevenY_421
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 58741289) ^ 29370644 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (3 : ZMod 58741289) ^ 548984 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (3 : ZMod 58741289) ^ 360376 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (3 : ZMod 58741289) ^ 139528 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide

private theorem prime_twentySevenY_1061 : Nat.Prime 1061 := by norm_num
private theorem prime_twentySevenY_112465159 : Nat.Prime 112465159 := by
  apply lucas_primality 112465159 (3 : ZMod 112465159)
  · rw [← twentySevenYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (13, 1), (1009, 1), (1429, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (13, 1), (1009, 1), (1429, 1)] : List FactorBlock).map factorBlockValue).prod = 112465159 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentySevenY_2
      · exact prime_twentySevenY_3
      · exact prime_twentySevenY_13
      · exact prime_twentySevenY_1009
      · exact prime_twentySevenY_1429
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 112465159) ^ 56232579 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (3 : ZMod 112465159) ^ 37488386 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (3 : ZMod 112465159) ^ 8651166 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (3 : ZMod 112465159) ^ 111462 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (3 : ZMod 112465159) ^ 78702 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide

private theorem prime_twentySevenY_2147859606583 : Nat.Prime 2147859606583 := by
  apply lucas_primality 2147859606583 (3 : ZMod 2147859606583)
  · rw [← twentySevenYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 2), (1061, 1), (112465159, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 2), (1061, 1), (112465159, 1)] : List FactorBlock).map factorBlockValue).prod = 2147859606583 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentySevenY_2
      · exact prime_twentySevenY_3
      · exact prime_twentySevenY_1061
      · exact prime_twentySevenY_112465159
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 2147859606583) ^ 1073929803291 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (3 : ZMod 2147859606583) ^ 715953202194 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (3 : ZMod 2147859606583) ^ 2024372862 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (3 : ZMod 2147859606583) ^ 19098 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide

private theorem prime_twentySevenY_17597407 : Nat.Prime 17597407 := by norm_num
private theorem prime_twentySevenY_6427 : Nat.Prime 6427 := by norm_num
private theorem prime_twentySevenY_28433 : Nat.Prime 28433 := by norm_num
private theorem prime_twentySevenY_1069823 : Nat.Prime 1069823 := by norm_num
private theorem prime_twentySevenY_95012158532938399 : Nat.Prime 95012158532938399 := by
  apply lucas_primality 95012158532938399 (3 : ZMod 95012158532938399)
  · rw [← twentySevenYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 5), (6427, 1), (28433, 1), (1069823, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 5), (6427, 1), (28433, 1), (1069823, 1)] : List FactorBlock).map factorBlockValue).prod = 95012158532938399 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentySevenY_2
      · exact prime_twentySevenY_3
      · exact prime_twentySevenY_6427
      · exact prime_twentySevenY_28433
      · exact prime_twentySevenY_1069823
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 95012158532938399) ^ 47506079266469199 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (3 : ZMod 95012158532938399) ^ 31670719510979466 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (3 : ZMod 95012158532938399) ^ 14783282796474 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (3 : ZMod 95012158532938399) ^ 3341615676606 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (3 : ZMod 95012158532938399) ^ 88811101026 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide

private theorem prime_twentySevenY_24513136901498106943 : Nat.Prime 24513136901498106943 := by
  apply lucas_primality 24513136901498106943 (5 : ZMod 24513136901498106943)
  · rw [← twentySevenYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (43, 1), (95012158532938399, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (43, 1), (95012158532938399, 1)] : List FactorBlock).map factorBlockValue).prod = 24513136901498106943 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentySevenY_2
      · exact prime_twentySevenY_3
      · exact prime_twentySevenY_43
      · exact prime_twentySevenY_95012158532938399
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 24513136901498106943) ^ 12256568450749053471 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (5 : ZMod 24513136901498106943) ^ 8171045633832702314 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (5 : ZMod 24513136901498106943) ^ 570072951197630394 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (5 : ZMod 24513136901498106943) ^ 258 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide

private theorem prime_twentySevenY_12759209 : Nat.Prime 12759209 := by norm_num
private theorem prime_twentySevenY_383 : Nat.Prime 383 := by norm_num
private theorem prime_twentySevenY_79181 : Nat.Prime 79181 := by norm_num
private theorem prime_twentySevenY_181957939 : Nat.Prime 181957939 := by
  apply lucas_primality 181957939 (2 : ZMod 181957939)
  · rw [← twentySevenYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (383, 1), (79181, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (383, 1), (79181, 1)] : List FactorBlock).map factorBlockValue).prod = 181957939 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentySevenY_2
      · exact prime_twentySevenY_3
      · exact prime_twentySevenY_383
      · exact prime_twentySevenY_79181
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 181957939) ^ 90978969 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (2 : ZMod 181957939) ^ 60652646 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (2 : ZMod 181957939) ^ 475086 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (2 : ZMod 181957939) ^ 2298 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide

private theorem prime_twentySevenY_1831 : Nat.Prime 1831 := by norm_num
private theorem prime_twentySevenY_5479 : Nat.Prime 5479 := by norm_num
private theorem prime_twentySevenY_9137 : Nat.Prime 9137 := by norm_num
private theorem prime_twentySevenY_183325663427 : Nat.Prime 183325663427 := by
  apply lucas_primality 183325663427 (2 : ZMod 183325663427)
  · rw [← twentySevenYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (1831, 1), (5479, 1), (9137, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (1831, 1), (5479, 1), (9137, 1)] : List FactorBlock).map factorBlockValue).prod = 183325663427 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentySevenY_2
      · exact prime_twentySevenY_1831
      · exact prime_twentySevenY_5479
      · exact prime_twentySevenY_9137
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 183325663427) ^ 91662831713 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (2 : ZMod 183325663427) ^ 100123246 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (2 : ZMod 183325663427) ^ 33459694 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (2 : ZMod 183325663427) ^ 20064098 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide

private theorem prime_twentySevenY_22741987 : Nat.Prime 22741987 := by
  apply lucas_primality 22741987 (2 : ZMod 22741987)
  · rw [← twentySevenYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (23, 1), (223, 1), (739, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (23, 1), (223, 1), (739, 1)] : List FactorBlock).map factorBlockValue).prod = 22741987 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentySevenY_2
      · exact prime_twentySevenY_3
      · exact prime_twentySevenY_23
      · exact prime_twentySevenY_223
      · exact prime_twentySevenY_739
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 22741987) ^ 11370993 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (2 : ZMod 22741987) ^ 7580662 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (2 : ZMod 22741987) ^ 988782 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (2 : ZMod 22741987) ^ 101982 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (2 : ZMod 22741987) ^ 30774 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide

private theorem prime_twentySevenY_272085132469 : Nat.Prime 272085132469 := by
  apply lucas_primality 272085132469 (2 : ZMod 272085132469)
  · rw [← twentySevenYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (997, 1), (22741987, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (997, 1), (22741987, 1)] : List FactorBlock).map factorBlockValue).prod = 272085132469 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentySevenY_2
      · exact prime_twentySevenY_3
      · exact prime_twentySevenY_997
      · exact prime_twentySevenY_22741987
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 272085132469) ^ 136042566234 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (2 : ZMod 272085132469) ^ 90695044156 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (2 : ZMod 272085132469) ^ 272903844 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (2 : ZMod 272085132469) ^ 11964 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide

private theorem prime_twentySevenY_3967 : Nat.Prime 3967 := by norm_num
private theorem prime_twentySevenY_317 : Nat.Prime 317 := by norm_num
private theorem prime_twentySevenY_71837 : Nat.Prime 71837 := by norm_num
private theorem prime_twentySevenY_4053474563 : Nat.Prime 4053474563 := by
  apply lucas_primality 4053474563 (2 : ZMod 4053474563)
  · rw [← twentySevenYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (89, 1), (317, 1), (71837, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (89, 1), (317, 1), (71837, 1)] : List FactorBlock).map factorBlockValue).prod = 4053474563 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentySevenY_2
      · exact prime_twentySevenY_89
      · exact prime_twentySevenY_317
      · exact prime_twentySevenY_71837
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 4053474563) ^ 2026737281 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (2 : ZMod 4053474563) ^ 45544658 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (2 : ZMod 4053474563) ^ 12786986 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (2 : ZMod 4053474563) ^ 56426 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide

private theorem prime_twentySevenY_128641068731369 : Nat.Prime 128641068731369 := by
  apply lucas_primality 128641068731369 (3 : ZMod 128641068731369)
  · rw [← twentySevenYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (3967, 1), (4053474563, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (3967, 1), (4053474563, 1)] : List FactorBlock).map factorBlockValue).prod = 128641068731369 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twentySevenY_2
      · exact prime_twentySevenY_3967
      · exact prime_twentySevenY_4053474563
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 128641068731369) ^ 64320534365684 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (3 : ZMod 128641068731369) ^ 32427796504 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (3 : ZMod 128641068731369) ^ 31736 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide

private theorem prime_twentySevenY_1543692824776429 : Nat.Prime 1543692824776429 := by
  apply lucas_primality 1543692824776429 (2 : ZMod 1543692824776429)
  · rw [← twentySevenYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (128641068731369, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (128641068731369, 1)] : List FactorBlock).map factorBlockValue).prod = 1543692824776429 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twentySevenY_2
      · exact prime_twentySevenY_3
      · exact prime_twentySevenY_128641068731369
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 1543692824776429) ^ 771846412388214 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (2 : ZMod 1543692824776429) ^ 514564274925476 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (2 : ZMod 1543692824776429) ^ 12 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide

private theorem prime_twentySevenY_2671 : Nat.Prime 2671 := by norm_num
private theorem prime_twentySevenY_11131 : Nat.Prime 11131 := by norm_num
private theorem prime_twentySevenY_266933 : Nat.Prime 266933 := by norm_num
private theorem prime_twentySevenY_35769023 : Nat.Prime 35769023 := by
  apply lucas_primality 35769023 (5 : ZMod 35769023)
  · rw [← twentySevenYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (67, 1), (266933, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (67, 1), (266933, 1)] : List FactorBlock).map factorBlockValue).prod = 35769023 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twentySevenY_2
      · exact prime_twentySevenY_67
      · exact prime_twentySevenY_266933
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 35769023) ^ 17884511 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (5 : ZMod 35769023) ^ 533866 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (5 : ZMod 35769023) ^ 134 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide

private theorem prime_twentySevenY_641 : Nat.Prime 641 := by norm_num
private theorem prime_twentySevenY_195047 : Nat.Prime 195047 := by norm_num
private theorem prime_twentySevenY_389828345987 : Nat.Prime 389828345987 := by
  apply lucas_primality 389828345987 (2 : ZMod 389828345987)
  · rw [← twentySevenYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (641, 1), (1559, 1), (195047, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (641, 1), (1559, 1), (195047, 1)] : List FactorBlock).map factorBlockValue).prod = 389828345987 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentySevenY_2
      · exact prime_twentySevenY_641
      · exact prime_twentySevenY_1559
      · exact prime_twentySevenY_195047
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 389828345987) ^ 194914172993 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (2 : ZMod 389828345987) ^ 608156546 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (2 : ZMod 389828345987) ^ 250050254 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (2 : ZMod 389828345987) ^ 1998638 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide

private theorem prime_twentySevenY_571 : Nat.Prime 571 := by norm_num
private theorem prime_twentySevenY_11213231 : Nat.Prime 11213231 := by norm_num
private theorem prime_twentySevenY_12829519 : Nat.Prime 12829519 := by norm_num
private theorem prime_twentySevenY_433 : Nat.Prime 433 := by norm_num
private theorem prime_twentySevenY_6043 : Nat.Prime 6043 := by norm_num
private theorem prime_twentySevenY_2491021289 : Nat.Prime 2491021289 := by
  apply lucas_primality 2491021289 (3 : ZMod 2491021289)
  · rw [← twentySevenYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (7, 1), (17, 1), (433, 1), (6043, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (7, 1), (17, 1), (433, 1), (6043, 1)] : List FactorBlock).map factorBlockValue).prod = 2491021289 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentySevenY_2
      · exact prime_twentySevenY_7
      · exact prime_twentySevenY_17
      · exact prime_twentySevenY_433
      · exact prime_twentySevenY_6043
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 2491021289) ^ 1245510644 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (3 : ZMod 2491021289) ^ 355860184 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (3 : ZMod 2491021289) ^ 146530664 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (3 : ZMod 2491021289) ^ 5752936 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (3 : ZMod 2491021289) ^ 412216 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide

private theorem prime_twentySevenY_4982042579 : Nat.Prime 4982042579 := by
  apply lucas_primality 4982042579 (2 : ZMod 4982042579)
  · rw [← twentySevenYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (2491021289, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (2491021289, 1)] : List FactorBlock).map factorBlockValue).prod = 4982042579 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_twentySevenY_2
      · exact prime_twentySevenY_2491021289
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 4982042579) ^ 2491021289 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (2 : ZMod 4982042579) ^ 2 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide

private theorem prime_twentySevenY_661 : Nat.Prime 661 := by norm_num
private theorem prime_twentySevenY_5167 : Nat.Prime 5167 := by norm_num
private theorem prime_twentySevenY_101130193 : Nat.Prime 101130193 := by
  apply lucas_primality 101130193 (7 : ZMod 101130193)
  · rw [← twentySevenYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 4), (3, 2), (29, 1), (61, 1), (397, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 4), (3, 2), (29, 1), (61, 1), (397, 1)] : List FactorBlock).map factorBlockValue).prod = 101130193 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentySevenY_2
      · exact prime_twentySevenY_3
      · exact prime_twentySevenY_29
      · exact prime_twentySevenY_61
      · exact prime_twentySevenY_397
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 101130193) ^ 50565096 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (7 : ZMod 101130193) ^ 33710064 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (7 : ZMod 101130193) ^ 3487248 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (7 : ZMod 101130193) ^ 1657872 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (7 : ZMod 101130193) ^ 254736 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide

private theorem prime_twentySevenY_1011301931 : Nat.Prime 1011301931 := by
  apply lucas_primality 1011301931 (10 : ZMod 1011301931)
  · rw [← twentySevenYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 1), (101130193, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 1), (101130193, 1)] : List FactorBlock).map factorBlockValue).prod = 1011301931 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twentySevenY_2
      · exact prime_twentySevenY_5
      · exact prime_twentySevenY_101130193
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (10 : ZMod 1011301931) ^ 505650965 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (10 : ZMod 1011301931) ^ 202260386 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (10 : ZMod 1011301931) ^ 10 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide

private theorem prime_twentySevenY_409 : Nat.Prime 409 := by norm_num
private theorem prime_twentySevenY_1487 : Nat.Prime 1487 := by norm_num
private theorem prime_twentySevenY_3329193743 : Nat.Prime 3329193743 := by
  apply lucas_primality 3329193743 (5 : ZMod 3329193743)
  · rw [← twentySevenYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (7, 1), (17, 1), (23, 1), (409, 1), (1487, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (7, 1), (17, 1), (23, 1), (409, 1), (1487, 1)] : List FactorBlock).map factorBlockValue).prod = 3329193743 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_twentySevenY_2
      · exact prime_twentySevenY_7
      · exact prime_twentySevenY_17
      · exact prime_twentySevenY_23
      · exact prime_twentySevenY_409
      · exact prime_twentySevenY_1487
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 3329193743) ^ 1664596871 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (5 : ZMod 3329193743) ^ 475599106 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (5 : ZMod 3329193743) ^ 195834926 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (5 : ZMod 3329193743) ^ 144747554 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (5 : ZMod 3329193743) ^ 8139838 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (5 : ZMod 3329193743) ^ 2238866 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide

private theorem prime_twentySevenY_6658387487 : Nat.Prime 6658387487 := by
  apply lucas_primality 6658387487 (5 : ZMod 6658387487)
  · rw [← twentySevenYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3329193743, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3329193743, 1)] : List FactorBlock).map factorBlockValue).prod = 6658387487 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_twentySevenY_2
      · exact prime_twentySevenY_3329193743
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 6658387487) ^ 3329193743 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (5 : ZMod 6658387487) ^ 2 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide

private theorem prime_twentySevenY_91991947754398274417310557 : Nat.Prime 91991947754398274417310557 := by
  apply lucas_primality 91991947754398274417310557 (2 : ZMod 91991947754398274417310557)
  · rw [← twentySevenYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (661, 1), (5167, 1), (1011301931, 1), (6658387487, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (661, 1), (5167, 1), (1011301931, 1), (6658387487, 1)] : List FactorBlock).map factorBlockValue).prod = 91991947754398274417310557 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentySevenY_2
      · exact prime_twentySevenY_661
      · exact prime_twentySevenY_5167
      · exact prime_twentySevenY_1011301931
      · exact prime_twentySevenY_6658387487
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 91991947754398274417310557) ^ 45995973877199137208655278 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (2 : ZMod 91991947754398274417310557) ^ 139170874061116905321196 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (2 : ZMod 91991947754398274417310557) ^ 17803744485078048077668 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (2 : ZMod 91991947754398274417310557) ^ 90963880256249876 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (2 : ZMod 91991947754398274417310557) ^ 13815949872849188 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide

private theorem prime_twentySevenY_2043491 : Nat.Prime 2043491 := by norm_num
private theorem prime_twentySevenY_64320922717 : Nat.Prime 64320922717 := by
  apply lucas_primality 64320922717 (2 : ZMod 64320922717)
  · rw [← twentySevenYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (43, 1), (61, 1), (2043491, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (43, 1), (61, 1), (2043491, 1)] : List FactorBlock).map factorBlockValue).prod = 64320922717 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentySevenY_2
      · exact prime_twentySevenY_3
      · exact prime_twentySevenY_43
      · exact prime_twentySevenY_61
      · exact prime_twentySevenY_2043491
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 64320922717) ^ 32160461358 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (2 : ZMod 64320922717) ^ 21440307572 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (2 : ZMod 64320922717) ^ 1495835412 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (2 : ZMod 64320922717) ^ 1054441356 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (2 : ZMod 64320922717) ^ 31476 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide

private theorem prime_twentySevenY_17443 : Nat.Prime 17443 := by norm_num
private theorem prime_twentySevenY_1412363 : Nat.Prime 1412363 := by norm_num
private theorem prime_twentySevenY_6203503565088673 : Nat.Prime 6203503565088673 := by
  apply lucas_primality 6203503565088673 (5 : ZMod 6203503565088673)
  · rw [← twentySevenYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 5), (3, 1), (43, 1), (61, 1), (17443, 1), (1412363, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 5), (3, 1), (43, 1), (61, 1), (17443, 1), (1412363, 1)] : List FactorBlock).map factorBlockValue).prod = 6203503565088673 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_twentySevenY_2
      · exact prime_twentySevenY_3
      · exact prime_twentySevenY_43
      · exact prime_twentySevenY_61
      · exact prime_twentySevenY_17443
      · exact prime_twentySevenY_1412363
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 6203503565088673) ^ 3101751782544336 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (5 : ZMod 6203503565088673) ^ 2067834521696224 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (5 : ZMod 6203503565088673) ^ 144267524769504 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (5 : ZMod 6203503565088673) ^ 101696779755552 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (5 : ZMod 6203503565088673) ^ 355644302304 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (5 : ZMod 6203503565088673) ^ 4392286944 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide

private theorem prime_twentySevenY_394088961367607422503787201 : Nat.Prime 394088961367607422503787201 := by
  apply lucas_primality 394088961367607422503787201 (103 : ZMod 394088961367607422503787201)
  · rw [← twentySevenYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 6), (3, 2), (5, 2), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 6), (3, 2), (5, 2), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod = 394088961367607422503787201 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_twentySevenY_2
      · exact prime_twentySevenY_3
      · exact prime_twentySevenY_5
      · exact prime_twentySevenY_7
      · exact prime_twentySevenY_11
      · exact prime_twentySevenY_13
      · exact prime_twentySevenY_17
      · exact prime_twentySevenY_19
      · exact prime_twentySevenY_23
      · exact prime_twentySevenY_29
      · exact prime_twentySevenY_31
      · exact prime_twentySevenY_37
      · exact prime_twentySevenY_41
      · exact prime_twentySevenY_43
      · exact prime_twentySevenY_47
      · exact prime_twentySevenY_53
      · exact prime_twentySevenY_59
      · exact prime_twentySevenY_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (103 : ZMod 394088961367607422503787201) ^ 197044480683803711251893600 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 131362987122535807501262400 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 78817792273521484500757440 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 56298423052515346071969600 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 35826269215237038409435200 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 30314535489815955577214400 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 23181703609859260147281600 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 20741524282505653815988800 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 17134302668156844456686400 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 13589274529917497327716800 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 12712547140890562016251200 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 10651053009935335743345600 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 9611925887014815183019200 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 9164859566688544709390400 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 8384871518459732393697600 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 7435640780520894764222400 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 6679473921484871567860800 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 6460474776518154467275200 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide

private theorem prime_twentySevenY_349 : Nat.Prime 349 := by norm_num
private theorem prime_twentySevenY_593 : Nat.Prime 593 := by norm_num
private theorem prime_twentySevenY_189799 : Nat.Prime 189799 := by norm_num
private theorem prime_twentySevenY_27647 : Nat.Prime 27647 := by norm_num
private theorem prime_twentySevenY_2384407 : Nat.Prime 2384407 := by norm_num
private theorem prime_twentySevenY_85838653 : Nat.Prime 85838653 := by
  apply lucas_primality 85838653 (2 : ZMod 85838653)
  · rw [← twentySevenYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 2), (2384407, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 2), (2384407, 1)] : List FactorBlock).map factorBlockValue).prod = 85838653 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twentySevenY_2
      · exact prime_twentySevenY_3
      · exact prime_twentySevenY_2384407
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 85838653) ^ 42919326 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (2 : ZMod 85838653) ^ 28612884 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (2 : ZMod 85838653) ^ 36 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide

private theorem prime_twentySevenY_28478174873893 : Nat.Prime 28478174873893 := by
  apply lucas_primality 28478174873893 (2 : ZMod 28478174873893)
  · rw [← twentySevenYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (27647, 1), (85838653, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (27647, 1), (85838653, 1)] : List FactorBlock).map factorBlockValue).prod = 28478174873893 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentySevenY_2
      · exact prime_twentySevenY_3
      · exact prime_twentySevenY_27647
      · exact prime_twentySevenY_85838653
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 28478174873893) ^ 14239087436946 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (2 : ZMod 28478174873893) ^ 9492724957964 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (2 : ZMod 28478174873893) ^ 1030063836 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (2 : ZMod 28478174873893) ^ 331764 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide

private theorem prime_twentySevenY_1115424064252435572814549 : Nat.Prime 1115424064252435572814549 := by
  apply lucas_primality 1115424064252435572814549 (2 : ZMod 1115424064252435572814549)
  · rw [← twentySevenYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (29, 1), (593, 1), (189799, 1), (28478174873893, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (29, 1), (593, 1), (189799, 1), (28478174873893, 1)] : List FactorBlock).map factorBlockValue).prod = 1115424064252435572814549 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_twentySevenY_2
      · exact prime_twentySevenY_3
      · exact prime_twentySevenY_29
      · exact prime_twentySevenY_593
      · exact prime_twentySevenY_189799
      · exact prime_twentySevenY_28478174873893
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1115424064252435572814549) ^ 557712032126217786407274 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (2 : ZMod 1115424064252435572814549) ^ 371808021417478524271516 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (2 : ZMod 1115424064252435572814549) ^ 38462898767325364579812 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (2 : ZMod 1115424064252435572814549) ^ 1880984931285726092436 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (2 : ZMod 1115424064252435572814549) ^ 5876870079676055052 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (2 : ZMod 1115424064252435572814549) ^ 39167680836 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide

private theorem prime_twentySevenY_16712263 : Nat.Prime 16712263 := by norm_num
private theorem prime_twentySevenY_875837 : Nat.Prime 875837 := by norm_num
private theorem prime_twentySevenY_359093171 : Nat.Prime 359093171 := by
  apply lucas_primality 359093171 (6 : ZMod 359093171)
  · rw [← twentySevenYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 1), (41, 1), (875837, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 1), (41, 1), (875837, 1)] : List FactorBlock).map factorBlockValue).prod = 359093171 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentySevenY_2
      · exact prime_twentySevenY_5
      · exact prime_twentySevenY_41
      · exact prime_twentySevenY_875837
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 359093171) ^ 179546585 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (6 : ZMod 359093171) ^ 71818634 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (6 : ZMod 359093171) ^ 8758370 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (6 : ZMod 359093171) ^ 410 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide

private theorem prime_twentySevenY_2671787 : Nat.Prime 2671787 := by norm_num
private theorem prime_twentySevenY_47071543367 : Nat.Prime 47071543367 := by
  apply lucas_primality 47071543367 (5 : ZMod 47071543367)
  · rw [← twentySevenYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (23, 1), (383, 1), (2671787, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (23, 1), (383, 1), (2671787, 1)] : List FactorBlock).map factorBlockValue).prod = 47071543367 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentySevenY_2
      · exact prime_twentySevenY_23
      · exact prime_twentySevenY_383
      · exact prime_twentySevenY_2671787
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 47071543367) ^ 23535771683 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (5 : ZMod 47071543367) ^ 2046588842 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (5 : ZMod 47071543367) ^ 122902202 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (5 : ZMod 47071543367) ^ 17618 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide

private theorem prime_twentySevenY_20719 : Nat.Prime 20719 := by norm_num
private theorem prime_twentySevenY_12986333 : Nat.Prime 12986333 := by norm_num
private theorem prime_twentySevenY_10589 : Nat.Prime 10589 := by norm_num
private theorem prime_twentySevenY_98880083 : Nat.Prime 98880083 := by
  apply lucas_primality 98880083 (6 : ZMod 98880083)
  · rw [← twentySevenYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (7, 1), (23, 1), (29, 1), (10589, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (7, 1), (23, 1), (29, 1), (10589, 1)] : List FactorBlock).map factorBlockValue).prod = 98880083 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentySevenY_2
      · exact prime_twentySevenY_7
      · exact prime_twentySevenY_23
      · exact prime_twentySevenY_29
      · exact prime_twentySevenY_10589
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 98880083) ^ 49440041 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (6 : ZMod 98880083) ^ 14125726 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (6 : ZMod 98880083) ^ 4299134 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (6 : ZMod 98880083) ^ 3409658 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (6 : ZMod 98880083) ^ 9338 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide

private theorem prime_twentySevenY_1018963687663171715671 : Nat.Prime 1018963687663171715671 := by
  apply lucas_primality 1018963687663171715671 (3 : ZMod 1018963687663171715671)
  · rw [← twentySevenYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 3), (5, 1), (2939, 1), (12986333, 1), (98880083, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 3), (5, 1), (2939, 1), (12986333, 1), (98880083, 1)] : List FactorBlock).map factorBlockValue).prod = 1018963687663171715671 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_twentySevenY_2
      · exact prime_twentySevenY_3
      · exact prime_twentySevenY_5
      · exact prime_twentySevenY_2939
      · exact prime_twentySevenY_12986333
      · exact prime_twentySevenY_98880083
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1018963687663171715671) ^ 509481843831585857835 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (3 : ZMod 1018963687663171715671) ^ 339654562554390571890 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (3 : ZMod 1018963687663171715671) ^ 203792737532634343134 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (3 : ZMod 1018963687663171715671) ^ 346704214924522530 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (3 : ZMod 1018963687663171715671) ^ 78464312262990 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (3 : ZMod 1018963687663171715671) ^ 10305044825490 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide

private theorem prime_twentySevenY_18341346377937090882079 : Nat.Prime 18341346377937090882079 := by
  apply lucas_primality 18341346377937090882079 (3 : ZMod 18341346377937090882079)
  · rw [← twentySevenYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 2), (1018963687663171715671, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 2), (1018963687663171715671, 1)] : List FactorBlock).map factorBlockValue).prod = 18341346377937090882079 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twentySevenY_2
      · exact prime_twentySevenY_3
      · exact prime_twentySevenY_1018963687663171715671
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 18341346377937090882079) ^ 9170673188968545441039 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (3 : ZMod 18341346377937090882079) ^ 6113782125979030294026 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (3 : ZMod 18341346377937090882079) ^ 18 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide

private theorem prime_twentySevenY_1033 : Nat.Prime 1033 := by norm_num
private theorem prime_twentySevenY_42181 : Nat.Prime 42181 := by norm_num
private theorem prime_twentySevenY_21765397 : Nat.Prime 21765397 := by
  apply lucas_primality 21765397 (2 : ZMod 21765397)
  · rw [← twentySevenYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (43, 1), (42181, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (43, 1), (42181, 1)] : List FactorBlock).map factorBlockValue).prod = 21765397 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentySevenY_2
      · exact prime_twentySevenY_3
      · exact prime_twentySevenY_43
      · exact prime_twentySevenY_42181
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 21765397) ^ 10882698 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (2 : ZMod 21765397) ^ 7255132 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (2 : ZMod 21765397) ^ 506172 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (2 : ZMod 21765397) ^ 516 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide

private theorem prime_twentySevenY_2829501611 : Nat.Prime 2829501611 := by
  apply lucas_primality 2829501611 (2 : ZMod 2829501611)
  · rw [← twentySevenYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 1), (13, 1), (21765397, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 1), (13, 1), (21765397, 1)] : List FactorBlock).map factorBlockValue).prod = 2829501611 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentySevenY_2
      · exact prime_twentySevenY_5
      · exact prime_twentySevenY_13
      · exact prime_twentySevenY_21765397
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 2829501611) ^ 1414750805 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (2 : ZMod 2829501611) ^ 565900322 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (2 : ZMod 2829501611) ^ 217653970 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (2 : ZMod 2829501611) ^ 130 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide

private theorem prime_twentySevenY_170345164567419641 : Nat.Prime 170345164567419641 := by
  apply lucas_primality 170345164567419641 (3 : ZMod 170345164567419641)
  · rw [← twentySevenYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (5, 1), (31, 1), (47, 1), (1033, 1), (2829501611, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (5, 1), (31, 1), (47, 1), (1033, 1), (2829501611, 1)] : List FactorBlock).map factorBlockValue).prod = 170345164567419641 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_twentySevenY_2
      · exact prime_twentySevenY_5
      · exact prime_twentySevenY_31
      · exact prime_twentySevenY_47
      · exact prime_twentySevenY_1033
      · exact prime_twentySevenY_2829501611
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 170345164567419641) ^ 85172582283709820 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (3 : ZMod 170345164567419641) ^ 34069032913483928 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (3 : ZMod 170345164567419641) ^ 5495005308626440 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (3 : ZMod 170345164567419641) ^ 3624365203562120 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (3 : ZMod 170345164567419641) ^ 164903353889080 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (3 : ZMod 170345164567419641) ^ 60203240 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide

private theorem prime_twentySevenY_340690329134839283 : Nat.Prime 340690329134839283 := by
  apply lucas_primality 340690329134839283 (2 : ZMod 340690329134839283)
  · rw [← twentySevenYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (170345164567419641, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (170345164567419641, 1)] : List FactorBlock).map factorBlockValue).prod = 340690329134839283 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_twentySevenY_2
      · exact prime_twentySevenY_170345164567419641
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 340690329134839283) ^ 170345164567419641 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (2 : ZMod 340690329134839283) ^ 2 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide

private theorem prime_twentySevenY_352273800325423818623 : Nat.Prime 352273800325423818623 := by
  apply lucas_primality 352273800325423818623 (5 : ZMod 352273800325423818623)
  · rw [← twentySevenYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (11, 1), (47, 1), (340690329134839283, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (11, 1), (47, 1), (340690329134839283, 1)] : List FactorBlock).map factorBlockValue).prod = 352273800325423818623 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentySevenY_2
      · exact prime_twentySevenY_11
      · exact prime_twentySevenY_47
      · exact prime_twentySevenY_340690329134839283
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 352273800325423818623) ^ 176136900162711909311 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (5 : ZMod 352273800325423818623) ^ 32024890938674892602 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (5 : ZMod 352273800325423818623) ^ 7495187240966464226 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (5 : ZMod 352273800325423818623) ^ 1034 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide

private theorem prime_twentySevenY_363546561935837380818937 : Nat.Prime 363546561935837380818937 := by
  apply lucas_primality 363546561935837380818937 (10 : ZMod 363546561935837380818937)
  · rw [← twentySevenYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (3, 1), (43, 1), (352273800325423818623, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (3, 1), (43, 1), (352273800325423818623, 1)] : List FactorBlock).map factorBlockValue).prod = 363546561935837380818937 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentySevenY_2
      · exact prime_twentySevenY_3
      · exact prime_twentySevenY_43
      · exact prime_twentySevenY_352273800325423818623
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (10 : ZMod 363546561935837380818937) ^ 181773280967918690409468 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (10 : ZMod 363546561935837380818937) ^ 121182187311945793606312 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (10 : ZMod 363546561935837380818937) ^ 8454571207810171646952 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (10 : ZMod 363546561935837380818937) ^ 1032 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide

private theorem prime_twentySevenY_439253 : Nat.Prime 439253 := by norm_num
private theorem prime_twentySevenY_924727 : Nat.Prime 924727 := by norm_num
private theorem prime_twentySevenY_4788236407 : Nat.Prime 4788236407 := by
  apply lucas_primality 4788236407 (3 : ZMod 4788236407)
  · rw [← twentySevenYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (863, 1), (924727, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (863, 1), (924727, 1)] : List FactorBlock).map factorBlockValue).prod = 4788236407 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentySevenY_2
      · exact prime_twentySevenY_3
      · exact prime_twentySevenY_863
      · exact prime_twentySevenY_924727
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 4788236407) ^ 2394118203 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (3 : ZMod 4788236407) ^ 1596078802 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (3 : ZMod 4788236407) ^ 5548362 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (3 : ZMod 4788236407) ^ 5178 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide

private theorem prime_twentySevenY_1097895041784632863 : Nat.Prime 1097895041784632863 := by
  apply lucas_primality 1097895041784632863 (3 : ZMod 1097895041784632863)
  · rw [← twentySevenYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 2), (29, 1), (439253, 1), (4788236407, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 2), (29, 1), (439253, 1), (4788236407, 1)] : List FactorBlock).map factorBlockValue).prod = 1097895041784632863 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentySevenY_2
      · exact prime_twentySevenY_3
      · exact prime_twentySevenY_29
      · exact prime_twentySevenY_439253
      · exact prime_twentySevenY_4788236407
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1097895041784632863) ^ 548947520892316431 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (3 : ZMod 1097895041784632863) ^ 365965013928210954 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (3 : ZMod 1097895041784632863) ^ 37858449716711478 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (3 : ZMod 1097895041784632863) ^ 2499459404454 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (3 : ZMod 1097895041784632863) ^ 229290066 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide

private theorem prime_twentySevenY_1923195919434642801711457 : Nat.Prime 1923195919434642801711457 := by
  apply lucas_primality 1923195919434642801711457 (5 : ZMod 1923195919434642801711457)
  · rw [← twentySevenYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 5), (3, 1), (71, 1), (257, 1), (1097895041784632863, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 5), (3, 1), (71, 1), (257, 1), (1097895041784632863, 1)] : List FactorBlock).map factorBlockValue).prod = 1923195919434642801711457 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentySevenY_2
      · exact prime_twentySevenY_3
      · exact prime_twentySevenY_71
      · exact prime_twentySevenY_257
      · exact prime_twentySevenY_1097895041784632863
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 1923195919434642801711457) ^ 961597959717321400855728 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (5 : ZMod 1923195919434642801711457) ^ 641065306478214267237152 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (5 : ZMod 1923195919434642801711457) ^ 27087266470910461995936 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (5 : ZMod 1923195919434642801711457) ^ 7483252604804057594208 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (5 : ZMod 1923195919434642801711457) ^ 1751712 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide

private theorem prime_twentySevenY_439 : Nat.Prime 439 := by norm_num
private theorem prime_twentySevenY_2284423 : Nat.Prime 2284423 := by norm_num
private theorem prime_twentySevenY_704321 : Nat.Prime 704321 := by norm_num
private theorem prime_twentySevenY_63388891 : Nat.Prime 63388891 := by
  apply lucas_primality 63388891 (2 : ZMod 63388891)
  · rw [← twentySevenYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 2), (5, 1), (704321, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 2), (5, 1), (704321, 1)] : List FactorBlock).map factorBlockValue).prod = 63388891 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentySevenY_2
      · exact prime_twentySevenY_3
      · exact prime_twentySevenY_5
      · exact prime_twentySevenY_704321
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 63388891) ^ 31694445 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (2 : ZMod 63388891) ^ 21129630 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (2 : ZMod 63388891) ^ 12677778 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (2 : ZMod 63388891) ^ 90 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide

private theorem prime_twentySevenY_1652843 : Nat.Prime 1652843 := by norm_num
private theorem prime_twentySevenY_961954627 : Nat.Prime 961954627 := by
  apply lucas_primality 961954627 (2 : ZMod 961954627)
  · rw [← twentySevenYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (97, 1), (1652843, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (97, 1), (1652843, 1)] : List FactorBlock).map factorBlockValue).prod = 961954627 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentySevenY_2
      · exact prime_twentySevenY_3
      · exact prime_twentySevenY_97
      · exact prime_twentySevenY_1652843
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 961954627) ^ 480977313 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (2 : ZMod 961954627) ^ 320651542 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (2 : ZMod 961954627) ^ 9917058 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (2 : ZMod 961954627) ^ 582 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide

private theorem prime_twentySevenY_5771727763 : Nat.Prime 5771727763 := by
  apply lucas_primality 5771727763 (3 : ZMod 5771727763)
  · rw [← twentySevenYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (961954627, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (961954627, 1)] : List FactorBlock).map factorBlockValue).prod = 5771727763 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twentySevenY_2
      · exact prime_twentySevenY_3
      · exact prime_twentySevenY_961954627
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 5771727763) ^ 2885863881 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (3 : ZMod 5771727763) ^ 1923909254 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (3 : ZMod 5771727763) ^ 6 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide

private theorem prime_twentySevenY_12953 : Nat.Prime 12953 := by norm_num
private theorem prime_twentySevenY_570841 : Nat.Prime 570841 := by norm_num
private theorem prime_twentySevenY_673 : Nat.Prime 673 := by norm_num
private theorem prime_twentySevenY_420956117 : Nat.Prime 420956117 := by
  apply lucas_primality 420956117 (5 : ZMod 420956117)
  · rw [← twentySevenYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (7, 1), (89, 1), (251, 1), (673, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (7, 1), (89, 1), (251, 1), (673, 1)] : List FactorBlock).map factorBlockValue).prod = 420956117 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentySevenY_2
      · exact prime_twentySevenY_7
      · exact prime_twentySevenY_89
      · exact prime_twentySevenY_251
      · exact prime_twentySevenY_673
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 420956117) ^ 210478058 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (5 : ZMod 420956117) ^ 60136588 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (5 : ZMod 420956117) ^ 4729844 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (5 : ZMod 420956117) ^ 1677116 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (5 : ZMod 420956117) ^ 625492 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide

private theorem prime_twentySevenY_73221106990981 : Nat.Prime 73221106990981 := by
  apply lucas_primality 73221106990981 (2 : ZMod 73221106990981)
  · rw [← twentySevenYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (5, 1), (13, 1), (223, 1), (420956117, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (5, 1), (13, 1), (223, 1), (420956117, 1)] : List FactorBlock).map factorBlockValue).prod = 73221106990981 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_twentySevenY_2
      · exact prime_twentySevenY_3
      · exact prime_twentySevenY_5
      · exact prime_twentySevenY_13
      · exact prime_twentySevenY_223
      · exact prime_twentySevenY_420956117
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 73221106990981) ^ 36610553495490 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (2 : ZMod 73221106990981) ^ 24407035663660 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (2 : ZMod 73221106990981) ^ 14644221398196 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (2 : ZMod 73221106990981) ^ 5632392845460 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (2 : ZMod 73221106990981) ^ 328345771260 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (2 : ZMod 73221106990981) ^ 173940 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide

private theorem prime_twentySevenY_732211069909811 : Nat.Prime 732211069909811 := by
  apply lucas_primality 732211069909811 (6 : ZMod 732211069909811)
  · rw [← twentySevenYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 1), (73221106990981, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 1), (73221106990981, 1)] : List FactorBlock).map factorBlockValue).prod = 732211069909811 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twentySevenY_2
      · exact prime_twentySevenY_5
      · exact prime_twentySevenY_73221106990981
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (6 : ZMod 732211069909811) ^ 366105534954905 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (6 : ZMod 732211069909811) ^ 146442213981962 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (6 : ZMod 732211069909811) ^ 10 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide

private theorem prime_twentySevenY_3019 : Nat.Prime 3019 := by norm_num
private theorem prime_twentySevenY_4250387 : Nat.Prime 4250387 := by norm_num
private theorem prime_twentySevenY_66178525591 : Nat.Prime 66178525591 := by
  apply lucas_primality 66178525591 (3 : ZMod 66178525591)
  · rw [← twentySevenYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 2), (5, 1), (173, 1), (4250387, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 2), (5, 1), (173, 1), (4250387, 1)] : List FactorBlock).map factorBlockValue).prod = 66178525591 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentySevenY_2
      · exact prime_twentySevenY_3
      · exact prime_twentySevenY_5
      · exact prime_twentySevenY_173
      · exact prime_twentySevenY_4250387
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 66178525591) ^ 33089262795 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (3 : ZMod 66178525591) ^ 22059508530 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (3 : ZMod 66178525591) ^ 13235705118 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (3 : ZMod 66178525591) ^ 382534830 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (3 : ZMod 66178525591) ^ 15570 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide

private theorem prime_twentySevenY_331 : Nat.Prime 331 := by norm_num
private theorem prime_twentySevenY_9677 : Nat.Prime 9677 := by norm_num
private theorem prime_twentySevenY_50165569 : Nat.Prime 50165569 := by
  apply lucas_primality 50165569 (19 : ZMod 50165569)
  · rw [← twentySevenYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 6), (3, 4), (9677, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 6), (3, 4), (9677, 1)] : List FactorBlock).map factorBlockValue).prod = 50165569 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twentySevenY_2
      · exact prime_twentySevenY_3
      · exact prime_twentySevenY_9677
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (19 : ZMod 50165569) ^ 25082784 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (19 : ZMod 50165569) ^ 16721856 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (19 : ZMod 50165569) ^ 5184 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide

private theorem prime_twentySevenY_564563313527 : Nat.Prime 564563313527 := by
  apply lucas_primality 564563313527 (5 : ZMod 564563313527)
  · rw [← twentySevenYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (17, 1), (331, 1), (50165569, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (17, 1), (331, 1), (50165569, 1)] : List FactorBlock).map factorBlockValue).prod = 564563313527 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentySevenY_2
      · exact prime_twentySevenY_17
      · exact prime_twentySevenY_331
      · exact prime_twentySevenY_50165569
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 564563313527) ^ 282281656763 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (5 : ZMod 564563313527) ^ 33209606678 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (5 : ZMod 564563313527) ^ 1705629346 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (5 : ZMod 564563313527) ^ 11254 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide

private theorem prime_twentySevenY_180533 : Nat.Prime 180533 := by norm_num
private theorem prime_twentySevenY_2161 : Nat.Prime 2161 := by norm_num
private theorem prime_twentySevenY_8537 : Nat.Prime 8537 := by norm_num
private theorem prime_twentySevenY_561521 : Nat.Prime 561521 := by norm_num
private theorem prime_twentySevenY_19518469961 : Nat.Prime 19518469961 := by
  apply lucas_primality 19518469961 (3 : ZMod 19518469961)
  · rw [← twentySevenYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (5, 1), (11, 1), (79, 1), (561521, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (5, 1), (11, 1), (79, 1), (561521, 1)] : List FactorBlock).map factorBlockValue).prod = 19518469961 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentySevenY_2
      · exact prime_twentySevenY_5
      · exact prime_twentySevenY_11
      · exact prime_twentySevenY_79
      · exact prime_twentySevenY_561521
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 19518469961) ^ 9759234980 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (3 : ZMod 19518469961) ^ 3903693992 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (3 : ZMod 19518469961) ^ 1774406360 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (3 : ZMod 19518469961) ^ 247069240 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (3 : ZMod 19518469961) ^ 34760 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide

private theorem prime_twentySevenY_44650621068881221949 : Nat.Prime 44650621068881221949 := by
  apply lucas_primality 44650621068881221949 (2 : ZMod 44650621068881221949)
  · rw [← twentySevenYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (31, 1), (2161, 1), (8537, 1), (19518469961, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (31, 1), (2161, 1), (8537, 1), (19518469961, 1)] : List FactorBlock).map factorBlockValue).prod = 44650621068881221949 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentySevenY_2
      · exact prime_twentySevenY_31
      · exact prime_twentySevenY_2161
      · exact prime_twentySevenY_8537
      · exact prime_twentySevenY_19518469961
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 44650621068881221949) ^ 22325310534440610974 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (2 : ZMod 44650621068881221949) ^ 1440342615125200708 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (2 : ZMod 44650621068881221949) ^ 20662018079075068 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (2 : ZMod 44650621068881221949) ^ 5230247284629404 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (2 : ZMod 44650621068881221949) ^ 2287608668 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide

private theorem prime_twentySevenY_1964627327030773765757 : Nat.Prime 1964627327030773765757 := by
  apply lucas_primality 1964627327030773765757 (3 : ZMod 1964627327030773765757)
  · rw [← twentySevenYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (11, 1), (44650621068881221949, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (11, 1), (44650621068881221949, 1)] : List FactorBlock).map factorBlockValue).prod = 1964627327030773765757 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twentySevenY_2
      · exact prime_twentySevenY_11
      · exact prime_twentySevenY_44650621068881221949
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 1964627327030773765757) ^ 982313663515386882878 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (3 : ZMod 1964627327030773765757) ^ 178602484275524887796 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide
    · change (3 : ZMod 1964627327030773765757) ^ 44 ≠ 1
      rw [← twentySevenYFastPow_eq_pow]
      decide

private theorem phi_twentySevenY_31921205870776201222806763191 : Nat.totient 31921205870776201222806763191 = 21275376693362318615860316160 := by
  rw [← show ((([(3, 2), (3923, 1), (8197093, 1), (110295707065568641, 1)] : List FactorBlock).map factorBlockValue).prod) = 31921205870776201222806763191 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentySevenY_3, prime_twentySevenY_3923, prime_twentySevenY_8197093, prime_twentySevenY_110295707065568641]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentySevenY_31921205870776201222806763192 : Nat.totient 31921205870776201222806763192 = 15806363962226117442011136000 := by
  rw [← show ((([(2, 3), (137, 1), (457, 1), (7243, 1), (17881, 1), (12439517, 1), (39558401, 1)] : List FactorBlock).map factorBlockValue).prod) = 31921205870776201222806763192 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentySevenY_2, prime_twentySevenY_137, prime_twentySevenY_457, prime_twentySevenY_7243, prime_twentySevenY_17881, prime_twentySevenY_12439517, prime_twentySevenY_39558401]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentySevenY_31921205870776201222806763193 : Nat.totient 31921205870776201222806763193 = 27221443884940331621593094976 := by
  rw [← show ((([(7, 1), (199, 1), (15739, 1), (74093, 1), (19650511420917463, 1)] : List FactorBlock).map factorBlockValue).prod) = 31921205870776201222806763193 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentySevenY_7, prime_twentySevenY_199, prime_twentySevenY_15739, prime_twentySevenY_74093, prime_twentySevenY_19650511420917463]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentySevenY_31921205870776201222806763194 : Nat.totient 31921205870776201222806763194 = 10505652988184425469555277120 := by
  rw [← show ((([(2, 1), (3, 1), (79, 1), (189067, 1), (2202311, 1), (161735950924213, 1)] : List FactorBlock).map factorBlockValue).prod) = 31921205870776201222806763194 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentySevenY_2, prime_twentySevenY_3, prime_twentySevenY_79, prime_twentySevenY_189067, prime_twentySevenY_2202311, prime_twentySevenY_161735950924213]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentySevenY_31921205870776201222806763195 : Nat.totient 31921205870776201222806763195 = 25478470811523248849149747200 := by
  rw [← show ((([(5, 1), (521, 1), (2689, 1), (4557018159684647015431, 1)] : List FactorBlock).map factorBlockValue).prod) = 31921205870776201222806763195 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentySevenY_5, prime_twentySevenY_521, prime_twentySevenY_2689, prime_twentySevenY_4557018159684647015431]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentySevenY_31921205870776201222806763196 : Nat.totient 31921205870776201222806763196 = 15954424123808855261491200000 := by
  rw [← show ((([(2, 2), (5981, 1), (9001, 1), (9187, 1), (31724881, 1), (508605457, 1)] : List FactorBlock).map factorBlockValue).prod) = 31921205870776201222806763196 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentySevenY_2, prime_twentySevenY_5981, prime_twentySevenY_9001, prime_twentySevenY_9187, prime_twentySevenY_31724881, prime_twentySevenY_508605457]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentySevenY_31921205870776201222806763197 : Nat.totient 31921205870776201222806763197 = 21060840936268555610991759360 := by
  rw [← show ((([(3, 1), (97, 1), (36749, 1), (160512643, 1), (18596513447881, 1)] : List FactorBlock).map factorBlockValue).prod) = 31921205870776201222806763197 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentySevenY_3, prime_twentySevenY_97, prime_twentySevenY_36749, prime_twentySevenY_160512643, prime_twentySevenY_18596513447881]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentySevenY_31921205870776201222806763198 : Nat.totient 31921205870776201222806763198 = 15960602935388100611403381598 := by
  rw [← show ((([(2, 1), (15960602935388100611403381599, 1)] : List FactorBlock).map factorBlockValue).prod) = 31921205870776201222806763198 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentySevenY_2, prime_twentySevenY_15960602935388100611403381599]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentySevenY_31921205870776201222806763199 : Nat.totient 31921205870776201222806763199 = 31921132515843496370576411280 := by
  rw [← show ((([(435161, 1), (73354932704852229916759, 1)] : List FactorBlock).map factorBlockValue).prod) = 31921205870776201222806763199 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentySevenY_435161, prime_twentySevenY_73354932704852229916759]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentySevenY_31921205870776201222806763200 : Nat.totient 31921205870776201222806763200 = 4200426948402737263411200000 := by
  rw [← show ((([(2, 6), (3, 6), (5, 2), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 31921205870776201222806763200 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentySevenY_2, prime_twentySevenY_3, prime_twentySevenY_5, prime_twentySevenY_7, prime_twentySevenY_11, prime_twentySevenY_13, prime_twentySevenY_17, prime_twentySevenY_19, prime_twentySevenY_23, prime_twentySevenY_29, prime_twentySevenY_31, prime_twentySevenY_37, prime_twentySevenY_41, prime_twentySevenY_43, prime_twentySevenY_47, prime_twentySevenY_53, prime_twentySevenY_59, prime_twentySevenY_61]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentySevenY_31921205870776201222806763201 : Nat.totient 31921205870776201222806763201 = 31921065799752208488491647152 := by
  rw [← show ((([(227893, 1), (140071023992734314888157, 1)] : List FactorBlock).map factorBlockValue).prod) = 31921205870776201222806763201 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentySevenY_227893, prime_twentySevenY_140071023992734314888157]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentySevenY_31921205870776201222806763202 : Nat.totient 31921205870776201222806763202 = 15890291909241016467740811412 := by
  rw [← show ((([(2, 1), (227, 1), (70311026147084143662569963, 1)] : List FactorBlock).map factorBlockValue).prod) = 31921205870776201222806763202 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentySevenY_2, prime_twentySevenY_227, prime_twentySevenY_70311026147084143662569963]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentySevenY_31921205870776201222806763203 : Nat.totient 31921205870776201222806763203 = 21208173183769398764640670304 := by
  rw [← show ((([(3, 1), (293, 1), (36315365040701025281918957, 1)] : List FactorBlock).map factorBlockValue).prod) = 31921205870776201222806763203 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentySevenY_3, prime_twentySevenY_293, prime_twentySevenY_36315365040701025281918957]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentySevenY_31921205870776201222806763204 : Nat.totient 31921205870776201222806763204 = 15960235661923862672737224704 := by
  rw [← show ((([(2, 2), (43457, 1), (183636732118969333034993, 1)] : List FactorBlock).map factorBlockValue).prod) = 31921205870776201222806763204 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentySevenY_2, prime_twentySevenY_43457, prime_twentySevenY_183636732118969333034993]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentySevenY_31921205870776201222806763205 : Nat.totient 31921205870776201222806763205 = 25536964327583178410368747200 := by
  rw [← show ((([(5, 1), (69198781, 1), (92259445641899967061, 1)] : List FactorBlock).map factorBlockValue).prod) = 31921205870776201222806763205 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentySevenY_5, prime_twentySevenY_69198781, prime_twentySevenY_92259445641899967061]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentySevenY_31921205870776201222806763206 : Nat.totient 31921205870776201222806763206 = 10636404730263280306334937600 := by
  rw [← show ((([(2, 1), (3, 1), (2663, 1), (9063547, 1), (26126021, 1), (8436948721, 1)] : List FactorBlock).map factorBlockValue).prod) = 31921205870776201222806763206 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentySevenY_2, prime_twentySevenY_3, prime_twentySevenY_2663, prime_twentySevenY_9063547, prime_twentySevenY_26126021, prime_twentySevenY_8436948721]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentySevenY_31921205870776201222806763207 : Nat.totient 31921205870776201222806763207 = 27105323008971450352600001088 := by
  rw [← show ((([(7, 1), (107, 1), (216104610427, 1), (197212046147609, 1)] : List FactorBlock).map factorBlockValue).prod) = 31921205870776201222806763207 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentySevenY_7, prime_twentySevenY_107, prime_twentySevenY_216104610427, prime_twentySevenY_197212046147609]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentySevenY_31921205870776201222806763208 : Nat.totient 31921205870776201222806763208 = 15960602935388100611403381600 := by
  rw [← show ((([(2, 3), (3990150733847025152850845401, 1)] : List FactorBlock).map factorBlockValue).prod) = 31921205870776201222806763208 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentySevenY_2, prime_twentySevenY_3990150733847025152850845401]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentySevenY_31921205870776201222806763209 : Nat.totient 31921205870776201222806763209 = 21280803913151441936032356600 := by
  rw [← show ((([(3, 2), (30429025931, 1), (116559782766332771, 1)] : List FactorBlock).map factorBlockValue).prod) = 31921205870776201222806763209 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentySevenY_3, prime_twentySevenY_30429025931, prime_twentySevenY_116559782766332771]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentySevenY_31921205870776201222806763210 : Nat.totient 31921205870776201222806763210 = 12614645211583848194073033808 := by
  rw [← show ((([(2, 1), (5, 1), (83, 1), (38459284181658073762417787, 1)] : List FactorBlock).map factorBlockValue).prod) = 31921205870776201222806763210 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentySevenY_2, prime_twentySevenY_5, prime_twentySevenY_83, prime_twentySevenY_38459284181658073762417787]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentySevenY_31921205870776201222806763211 : Nat.totient 31921205870776201222806763211 = 28977861734208663219192816000 := by
  rw [← show ((([(11, 1), (701, 1), (1686677, 1), (13313779, 1), (184346679547, 1)] : List FactorBlock).map factorBlockValue).prod) = 31921205870776201222806763211 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentySevenY_11, prime_twentySevenY_701, prime_twentySevenY_1686677, prime_twentySevenY_13313779, prime_twentySevenY_184346679547]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentySevenY_31921205870776201222806763212 : Nat.totient 31921205870776201222806763212 = 10636459169680880857285128192 := by
  rw [← show ((([(2, 2), (3, 1), (3137, 1), (19309, 1), (43916097622182558197, 1)] : List FactorBlock).map factorBlockValue).prod) = 31921205870776201222806763212 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentySevenY_2, prime_twentySevenY_3, prime_twentySevenY_3137, prime_twentySevenY_19309, prime_twentySevenY_43916097622182558197]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentySevenY_31921205870776201222806763213 : Nat.totient 31921205870776201222806763213 = 29243798587348207586541964800 := by
  rw [← show ((([(13, 1), (233, 1), (311, 1), (25903, 1), (614266579, 1), (2129671771, 1)] : List FactorBlock).map factorBlockValue).prod) = 31921205870776201222806763213 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentySevenY_13, prime_twentySevenY_233, prime_twentySevenY_311, prime_twentySevenY_25903, prime_twentySevenY_614266579, prime_twentySevenY_2129671771]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentySevenY_31921205870776201222806763214 : Nat.totient 31921205870776201222806763214 = 13680516800945340262001747232 := by
  rw [← show ((([(2, 1), (7, 1), (16767625597, 1), (135981455480185333, 1)] : List FactorBlock).map factorBlockValue).prod) = 31921205870776201222806763214 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentySevenY_2, prime_twentySevenY_7, prime_twentySevenY_16767625597, prime_twentySevenY_135981455480185333]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentySevenY_31921205870776201222806763215 : Nat.totient 31921205870776201222806763215 = 17019022488969288677097600000 := by
  rw [← show ((([(3, 1), (5, 1), (3181, 1), (73571, 1), (455881, 1), (19946477413151, 1)] : List FactorBlock).map factorBlockValue).prod) = 31921205870776201222806763215 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentySevenY_3, prime_twentySevenY_5, prime_twentySevenY_3181, prime_twentySevenY_73571, prime_twentySevenY_455881, prime_twentySevenY_19946477413151]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentySevenY_31921205870776201222806763216 : Nat.totient 31921205870776201222806763216 = 15937838067534342156894412800 := by
  rw [← show ((([(2, 4), (1559, 1), (2521, 1), (2591, 1), (342553, 1), (571933002133, 1)] : List FactorBlock).map factorBlockValue).prod) = 31921205870776201222806763216 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentySevenY_2, prime_twentySevenY_1559, prime_twentySevenY_2521, prime_twentySevenY_2591, prime_twentySevenY_342553, prime_twentySevenY_571933002133]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentySevenY_31921205870776201222806763217 : Nat.totient 31921205870776201222806763217 = 30038686298086986223411474432 := by
  rw [← show ((([(17, 1), (6257, 1), (300098768163432966586193, 1)] : List FactorBlock).map factorBlockValue).prod) = 31921205870776201222806763217 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentySevenY_17, prime_twentySevenY_6257, prime_twentySevenY_300098768163432966586193]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentySevenY_31921205870776201222806763218 : Nat.totient 31921205870776201222806763218 = 10638994852183451653731525120 := by
  rw [← show ((([(2, 1), (3, 2), (8233, 1), (93811, 1), (8274073, 1), (277508030299, 1)] : List FactorBlock).map factorBlockValue).prod) = 31921205870776201222806763218 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentySevenY_2, prime_twentySevenY_3, prime_twentySevenY_8233, prime_twentySevenY_93811, prime_twentySevenY_8274073, prime_twentySevenY_277508030299]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentySevenY_31921205870776201222806763219 : Nat.totient 31921205870776201222806763219 = 30241142403655625167764174336 := by
  rw [← show ((([(19, 1), (127269069457, 1), (13200878061346993, 1)] : List FactorBlock).map factorBlockValue).prod) = 31921205870776201222806763219 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentySevenY_19, prime_twentySevenY_127269069457, prime_twentySevenY_13200878061346993]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentySevenY_31921205870776201222806763220 : Nat.totient 31921205870776201222806763220 = 12768481836543209875367851296 := by
  rw [← show ((([(2, 2), (5, 1), (24949783, 1), (63970908826694406967, 1)] : List FactorBlock).map factorBlockValue).prod) = 31921205870776201222806763220 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentySevenY_2, prime_twentySevenY_5, prime_twentySevenY_24949783, prime_twentySevenY_63970908826694406967]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentySevenY_31921205870776201222806763221 : Nat.totient 31921205870776201222806763221 = 17966940458166031206156150528 := by
  rw [← show ((([(3, 1), (7, 1), (67, 1), (12583, 1), (277259, 1), (2674733, 1), (2431279603, 1)] : List FactorBlock).map factorBlockValue).prod) = 31921205870776201222806763221 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentySevenY_3, prime_twentySevenY_7, prime_twentySevenY_67, prime_twentySevenY_12583, prime_twentySevenY_277259, prime_twentySevenY_2674733, prime_twentySevenY_2431279603]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentySevenY_31921205870776201222806763222 : Nat.totient 31921205870776201222806763222 = 14494317343647060745308235720 := by
  rw [← show ((([(2, 1), (11, 1), (947, 1), (1532168852393981051301083, 1)] : List FactorBlock).map factorBlockValue).prod) = 31921205870776201222806763222 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentySevenY_2, prime_twentySevenY_11, prime_twentySevenY_947, prime_twentySevenY_1532168852393981051301083]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentySevenY_31921205870776201222806763223 : Nat.totient 31921205870776201222806763223 = 30338847562587627415306784544 := by
  rw [← show ((([(23, 1), (157, 1), (8839990548539518477653493, 1)] : List FactorBlock).map factorBlockValue).prod) = 31921205870776201222806763223 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentySevenY_23, prime_twentySevenY_157, prime_twentySevenY_8839990548539518477653493]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentySevenY_31921205870776201222806763224 : Nat.totient 31921205870776201222806763224 = 10627854531086620139232936960 := by
  rw [← show ((([(2, 3), (3, 1), (919, 1), (11257, 1), (425291, 1), (302303849620517, 1)] : List FactorBlock).map factorBlockValue).prod) = 31921205870776201222806763224 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentySevenY_2, prime_twentySevenY_3, prime_twentySevenY_919, prime_twentySevenY_11257, prime_twentySevenY_425291, prime_twentySevenY_302303849620517]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentySevenY_31921205870776201222806763225 : Nat.totient 31921205870776201222806763225 = 25296053694275189193984000000 := by
  rw [← show ((([(5, 2), (191, 1), (251, 1), (6271, 1), (13217, 1), (481513, 1), (667351259, 1)] : List FactorBlock).map factorBlockValue).prod) = 31921205870776201222806763225 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentySevenY_5, prime_twentySevenY_191, prime_twentySevenY_251, prime_twentySevenY_6271, prime_twentySevenY_13217, prime_twentySevenY_481513, prime_twentySevenY_667351259]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentySevenY_31921205870776201222806763226 : Nat.totient 31921205870776201222806763226 = 14731275818847431620483200000 := by
  rw [← show ((([(2, 1), (13, 2), (9281, 1), (14626967, 1), (695686433921251, 1)] : List FactorBlock).map factorBlockValue).prod) = 31921205870776201222806763226 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentySevenY_2, prime_twentySevenY_13, prime_twentySevenY_9281, prime_twentySevenY_14626967, prime_twentySevenY_695686433921251]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentySevenY_31921205870776201222806763227 : Nat.totient 31921205870776201222806763227 = 21069986901359321511017571456 := by
  rw [← show ((([(3, 3), (103, 1), (5009, 1), (2291539082278737626663, 1)] : List FactorBlock).map factorBlockValue).prod) = 31921205870776201222806763227 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentySevenY_3, prime_twentySevenY_103, prime_twentySevenY_5009, prime_twentySevenY_2291539082278737626663]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentySevenY_31921205870776201222806763228 : Nat.totient 31921205870776201222806763228 = 13679919282653795261358158400 := by
  rw [← show ((([(2, 2), (7, 1), (32051, 1), (80149, 1), (443794142129759999, 1)] : List FactorBlock).map factorBlockValue).prod) = 31921205870776201222806763228 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentySevenY_2, prime_twentySevenY_7, prime_twentySevenY_32051, prime_twentySevenY_80149, prime_twentySevenY_443794142129759999]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentySevenY_31921205870776201222806763229 : Nat.totient 31921205870776201222806763229 = 30820474633852883939261702400 := by
  rw [← show ((([(29, 1), (1100731236923317283545060801, 1)] : List FactorBlock).map factorBlockValue).prod) = 31921205870776201222806763229 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentySevenY_29, prime_twentySevenY_1100731236923317283545060801]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentySevenY_31921205870776201222806763230 : Nat.totient 31921205870776201222806763230 = 8436431590339536703019335680 := by
  rw [← show ((([(2, 1), (3, 1), (5, 1), (139, 1), (577, 1), (2303321, 1), (5759873610810107, 1)] : List FactorBlock).map factorBlockValue).prod) = 31921205870776201222806763230 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentySevenY_2, prime_twentySevenY_3, prime_twentySevenY_5, prime_twentySevenY_139, prime_twentySevenY_577, prime_twentySevenY_2303321, prime_twentySevenY_5759873610810107]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentySevenY_31921205870776201222806763231 : Nat.totient 31921205870776201222806763231 = 30456313953024766986380779200 := by
  rw [← show ((([(31, 1), (71, 1), (361727, 1), (40093901583788580553, 1)] : List FactorBlock).map factorBlockValue).prod) = 31921205870776201222806763231 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentySevenY_31, prime_twentySevenY_71, prime_twentySevenY_361727, prime_twentySevenY_40093901583788580553]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentySevenY_31921205870776201222806763232 : Nat.totient 31921205870776201222806763232 = 15781270207563868218688435200 := by
  rw [← show ((([(2, 5), (89, 1), (142723051, 1), (78531733309302509, 1)] : List FactorBlock).map factorBlockValue).prod) = 31921205870776201222806763232 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentySevenY_2, prime_twentySevenY_89, prime_twentySevenY_142723051, prime_twentySevenY_78531733309302509]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentySevenY_31921205870776201222806763233 : Nat.totient 31921205870776201222806763233 = 19216029111215955730747645440 := by
  rw [← show ((([(3, 1), (11, 1), (149, 1), (60793, 1), (106788750604720147493, 1)] : List FactorBlock).map factorBlockValue).prod) = 31921205870776201222806763233 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentySevenY_3, prime_twentySevenY_11, prime_twentySevenY_149, prime_twentySevenY_60793, prime_twentySevenY_106788750604720147493]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentySevenY_31921205870776201222806763234 : Nat.totient 31921205870776201222806763234 = 15021629082636244214325758272 := by
  rw [← show ((([(2, 1), (17, 1), (130787, 1), (7178534534772569414123, 1)] : List FactorBlock).map factorBlockValue).prod) = 31921205870776201222806763234 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentySevenY_2, prime_twentySevenY_17, prime_twentySevenY_130787, prime_twentySevenY_7178534534772569414123]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentySevenY_31921205870776201222806763235 : Nat.totient 31921205870776201222806763235 = 21888822664382070110504749056 := by
  rw [← show ((([(5, 1), (7, 1), (5188849, 1), (175768162351756354129, 1)] : List FactorBlock).map factorBlockValue).prod) = 31921205870776201222806763235 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentySevenY_5, prime_twentySevenY_7, prime_twentySevenY_5188849, prime_twentySevenY_175768162351756354129]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentySevenY_31921205870776201222806763236 : Nat.totient 31921205870776201222806763236 = 10620369962419606207605964800 := by
  rw [← show ((([(2, 2), (3, 2), (769, 1), (2143, 1), (8597, 1), (9792301, 1), (6391408799, 1)] : List FactorBlock).map factorBlockValue).prod) = 31921205870776201222806763236 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentySevenY_2, prime_twentySevenY_3, prime_twentySevenY_769, prime_twentySevenY_2143, prime_twentySevenY_8597, prime_twentySevenY_9792301, prime_twentySevenY_6391408799]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentySevenY_31921205870776201222806763237 : Nat.totient 31921205870776201222806763237 = 31058405278286565959589765312 := by
  rw [← show ((([(37, 1), (475637, 1), (1813852357585221913373, 1)] : List FactorBlock).map factorBlockValue).prod) = 31921205870776201222806763237 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentySevenY_37, prime_twentySevenY_475637, prime_twentySevenY_1813852357585221913373]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentySevenY_31921205870776201222806763238 : Nat.totient 31921205870776201222806763238 = 15120570846665626668849241800 := by
  rw [← show ((([(2, 1), (19, 1), (42559471, 1), (19737833053457806831, 1)] : List FactorBlock).map factorBlockValue).prod) = 31921205870776201222806763238 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentySevenY_2, prime_twentySevenY_19, prime_twentySevenY_42559471, prime_twentySevenY_19737833053457806831]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentySevenY_31921205870776201222806763239 : Nat.totient 31921205870776201222806763239 = 19642109203772277142556368896 := by
  rw [← show ((([(3, 1), (13, 1), (11489, 1), (71241401185919644928609, 1)] : List FactorBlock).map factorBlockValue).prod) = 31921205870776201222806763239 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentySevenY_3, prime_twentySevenY_13, prime_twentySevenY_11489, prime_twentySevenY_71241401185919644928609]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentySevenY_31921205870776201222806763240 : Nat.totient 31921205870776201222806763240 = 12755907642344530086674989056 := by
  rw [← show ((([(2, 3), (5, 1), (2377, 1), (3089, 1), (4157, 1), (6528503, 1), (4004779187, 1)] : List FactorBlock).map factorBlockValue).prod) = 31921205870776201222806763240 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentySevenY_2, prime_twentySevenY_5, prime_twentySevenY_2377, prime_twentySevenY_3089, prime_twentySevenY_4157, prime_twentySevenY_6528503, prime_twentySevenY_4004779187]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentySevenY_31921205870776201222806763241 : Nat.totient 31921205870776201222806763241 = 31139364915476014942248355200 := by
  rw [← show ((([(41, 1), (9587, 1), (1173541, 1), (69201329442777503, 1)] : List FactorBlock).map factorBlockValue).prod) = 31921205870776201222806763241 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentySevenY_41, prime_twentySevenY_9587, prime_twentySevenY_1173541, prime_twentySevenY_69201329442777503]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentySevenY_31921205870776201222806763242 : Nat.totient 31921205870776201222806763242 = 9087419101640678716281154560 := by
  rw [← show ((([(2, 1), (3, 1), (7, 1), (277, 1), (6810796141, 1), (402858330250993, 1)] : List FactorBlock).map factorBlockValue).prod) = 31921205870776201222806763242 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentySevenY_2, prime_twentySevenY_3, prime_twentySevenY_7, prime_twentySevenY_277, prime_twentySevenY_6810796141, prime_twentySevenY_402858330250993]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentySevenY_31921205870776201222806763243 : Nat.totient 31921205870776201222806763243 = 30676436372142754742255616000 := by
  rw [← show ((([(43, 1), (109, 1), (151, 1), (4993, 1), (5443, 1), (1659615521571361, 1)] : List FactorBlock).map factorBlockValue).prod) = 31921205870776201222806763243 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentySevenY_43, prime_twentySevenY_109, prime_twentySevenY_151, prime_twentySevenY_4993, prime_twentySevenY_5443, prime_twentySevenY_1659615521571361]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentySevenY_31921205870776201222806763244 : Nat.totient 31921205870776201222806763244 = 14509639032171000555821255800 := by
  rw [← show ((([(2, 2), (11, 2), (65952904691686366162823891, 1)] : List FactorBlock).map factorBlockValue).prod) = 31921205870776201222806763244 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentySevenY_2, prime_twentySevenY_11, prime_twentySevenY_65952904691686366162823891]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentySevenY_31921205870776201222806763245 : Nat.totient 31921205870776201222806763245 = 16941101785182382994115471360 := by
  rw [← show ((([(3, 2), (5, 1), (281, 1), (739, 1), (3540386347, 1), (964862349257, 1)] : List FactorBlock).map factorBlockValue).prod) = 31921205870776201222806763245 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentySevenY_3, prime_twentySevenY_5, prime_twentySevenY_281, prime_twentySevenY_739, prime_twentySevenY_3540386347, prime_twentySevenY_964862349257]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentySevenY_31921205870776201222806763246 : Nat.totient 31921205870776201222806763246 = 15266662964096727651678545280 := by
  rw [← show ((([(2, 1), (23, 1), (24289169, 1), (180464111, 1), (158313501439, 1)] : List FactorBlock).map factorBlockValue).prod) = 31921205870776201222806763246 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentySevenY_2, prime_twentySevenY_23, prime_twentySevenY_24289169, prime_twentySevenY_180464111, prime_twentySevenY_158313501439]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentySevenY_31921205870776201222806763247 : Nat.totient 31921205870776201222806763247 = 31223244728606109644017050552 := by
  rw [← show ((([(47, 1), (1663, 1), (408403242931592497828927, 1)] : List FactorBlock).map factorBlockValue).prod) = 31921205870776201222806763247 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentySevenY_47, prime_twentySevenY_1663, prime_twentySevenY_408403242931592497828927]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentySevenY_31921205870776201222806763248 : Nat.totient 31921205870776201222806763248 = 10639991330552752375962800640 := by
  rw [← show ((([(2, 4), (3, 1), (25913, 1), (1731666887, 1), (14820266192971, 1)] : List FactorBlock).map factorBlockValue).prod) = 31921205870776201222806763248 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentySevenY_2, prime_twentySevenY_3, prime_twentySevenY_25913, prime_twentySevenY_1731666887, prime_twentySevenY_14820266192971]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentySevenY_31921205870776201222806763249 : Nat.totient 31921205870776201222806763249 = 27361032255341416165250258304 := by
  rw [← show ((([(7, 2), (20294777, 1), (32099548619639871113, 1)] : List FactorBlock).map factorBlockValue).prod) = 31921205870776201222806763249 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentySevenY_7, prime_twentySevenY_20294777, prime_twentySevenY_32099548619639871113]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentySevenY_31921205870776201222806763250 : Nat.totient 31921205870776201222806763250 = 12768482347875911336510838000 := by
  rw [← show ((([(2, 1), (5, 3), (29382133091, 1), (4345662143985583, 1)] : List FactorBlock).map factorBlockValue).prod) = 31921205870776201222806763250 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentySevenY_2, prime_twentySevenY_5, prime_twentySevenY_29382133091, prime_twentySevenY_4345662143985583]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentySevenY_31921205870776201222806763251 : Nat.totient 31921205870776201222806763251 = 20028991918918400767251302400 := by
  rw [← show ((([(3, 1), (17, 1), (625905997466200023976603201, 1)] : List FactorBlock).map factorBlockValue).prod) = 31921205870776201222806763251 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentySevenY_3, prime_twentySevenY_17, prime_twentySevenY_625905997466200023976603201]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentySevenY_31921205870776201222806763252 : Nat.totient 31921205870776201222806763252 = 14732854850669096593194410880 := by
  rw [← show ((([(2, 2), (13, 1), (1604711, 1), (68090707, 1), (5618123376413, 1)] : List FactorBlock).map factorBlockValue).prod) = 31921205870776201222806763252 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentySevenY_2, prime_twentySevenY_13, prime_twentySevenY_1604711, prime_twentySevenY_68090707, prime_twentySevenY_5618123376413]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentySevenY_31921205870776201222806763253 : Nat.totient 31921205870776201222806763253 = 31279828132426716278650845696 := by
  rw [← show ((([(53, 1), (877, 1), (9257, 1), (74187982766308990109, 1)] : List FactorBlock).map factorBlockValue).prod) = 31921205870776201222806763253 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentySevenY_53, prime_twentySevenY_877, prime_twentySevenY_9257, prime_twentySevenY_74187982766308990109]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentySevenY_31921205870776201222806763254 : Nat.totient 31921205870776201222806763254 = 10640401948222420416879709800 := by
  rw [← show ((([(2, 1), (3, 3), (1222615931, 1), (483498887150858771, 1)] : List FactorBlock).map factorBlockValue).prod) = 31921205870776201222806763254 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentySevenY_2, prime_twentySevenY_3, prime_twentySevenY_1222615931, prime_twentySevenY_483498887150858771]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentySevenY_31921205870776201222806763255 : Nat.totient 31921205870776201222806763255 = 23192134496374293138657830400 := by
  rw [← show ((([(5, 1), (11, 1), (997, 1), (12024319, 1), (31645021, 1), (1529873647, 1)] : List FactorBlock).map factorBlockValue).prod) = 31921205870776201222806763255 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentySevenY_5, prime_twentySevenY_11, prime_twentySevenY_997, prime_twentySevenY_12024319, prime_twentySevenY_31645021, prime_twentySevenY_1529873647]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentySevenY_31921205870776201222806763256 : Nat.totient 31921205870776201222806763256 = 13678949878642734766887744000 := by
  rw [← show ((([(2, 3), (7, 1), (8731, 1), (413334331, 1), (157952242161841, 1)] : List FactorBlock).map factorBlockValue).prod) = 31921205870776201222806763256 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentySevenY_2, prime_twentySevenY_7, prime_twentySevenY_8731, prime_twentySevenY_413334331, prime_twentySevenY_157952242161841]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentySevenY_31921205870776201222806763257 : Nat.totient 31921205870776201222806763257 = 20155249322637667857567636480 := by
  rw [← show ((([(3, 1), (19, 1), (3691, 1), (401987, 1), (377440396466729153, 1)] : List FactorBlock).map factorBlockValue).prod) = 31921205870776201222806763257 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentySevenY_3, prime_twentySevenY_19, prime_twentySevenY_3691, prime_twentySevenY_401987, prime_twentySevenY_377440396466729153]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentySevenY_31921205870776201222806763258 : Nat.totient 31921205870776201222806763258 = 15396341701600033437340492800 := by
  rw [← show ((([(2, 1), (29, 1), (1109, 1), (237513142289, 1), (2089450581901, 1)] : List FactorBlock).map factorBlockValue).prod) = 31921205870776201222806763258 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentySevenY_2, prime_twentySevenY_29, prime_twentySevenY_1109, prime_twentySevenY_237513142289, prime_twentySevenY_2089450581901]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentySevenY_31921205870776201222806763259 : Nat.totient 31921205870776201222806763259 = 31380091964630358494636149344 := by
  rw [← show ((([(59, 1), (426757, 1), (10506247, 1), (120669917887819, 1)] : List FactorBlock).map factorBlockValue).prod) = 31921205870776201222806763259 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentySevenY_59, prime_twentySevenY_426757, prime_twentySevenY_10506247, prime_twentySevenY_120669917887819]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentySevenY_31921205870776201222806763260 : Nat.totient 31921205870776201222806763260 = 8394987328928202759971364864 := by
  rw [← show ((([(2, 2), (3, 1), (5, 1), (73, 1), (11953, 1), (339907, 1), (1793775758729587, 1)] : List FactorBlock).map factorBlockValue).prod) = 31921205870776201222806763260 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentySevenY_2, prime_twentySevenY_3, prime_twentySevenY_5, prime_twentySevenY_73, prime_twentySevenY_11953, prime_twentySevenY_339907, prime_twentySevenY_1793775758729587]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentySevenY_31921205870776201222806763261 : Nat.totient 31921205870776201222806763261 = 31397896697341485856629340800 := by
  rw [← show ((([(61, 1), (4816121, 1), (7480679, 1), (14524829569039, 1)] : List FactorBlock).map factorBlockValue).prod) = 31921205870776201222806763261 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentySevenY_61, prime_twentySevenY_4816121, prime_twentySevenY_7480679, prime_twentySevenY_14524829569039]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentySevenY_31921205870776201222806763262 : Nat.totient 31921205870776201222806763262 = 15445704759829127034735326400 := by
  rw [← show ((([(2, 1), (31, 1), (386047, 1), (2446488713, 1), (545135169191, 1)] : List FactorBlock).map factorBlockValue).prod) = 31921205870776201222806763262 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentySevenY_2, prime_twentySevenY_31, prime_twentySevenY_386047, prime_twentySevenY_2446488713, prime_twentySevenY_545135169191]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentySevenY_31921205870776201222806763263 : Nat.totient 31921205870776201222806763263 = 18215598261186071314180717248 := by
  rw [← show ((([(3, 2), (7, 1), (727, 1), (40346827, 1), (17274080639688469, 1)] : List FactorBlock).map factorBlockValue).prod) = 31921205870776201222806763263 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentySevenY_3, prime_twentySevenY_7, prime_twentySevenY_727, prime_twentySevenY_40346827, prime_twentySevenY_17274080639688469]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentySevenY_31921205870776201222806763264 : Nat.totient 31921205870776201222806763264 = 15859824627623820361342156800 := by
  rw [← show ((([(2, 8), (163, 1), (6841, 1), (31147, 1), (487709, 1), (7361310491, 1)] : List FactorBlock).map factorBlockValue).prod) = 31921205870776201222806763264 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentySevenY_2, prime_twentySevenY_163, prime_twentySevenY_6841, prime_twentySevenY_31147, prime_twentySevenY_487709, prime_twentySevenY_7361310491]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentySevenY_31921205870776201222806763265 : Nat.totient 31921205870776201222806763265 = 23389771540617231655893811200 := by
  rw [← show ((([(5, 1), (13, 1), (131, 1), (8377, 1), (310243, 1), (1442461166532641, 1)] : List FactorBlock).map factorBlockValue).prod) = 31921205870776201222806763265 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentySevenY_5, prime_twentySevenY_13, prime_twentySevenY_131, prime_twentySevenY_8377, prime_twentySevenY_310243, prime_twentySevenY_1442461166532641]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentySevenY_31921205870776201222806763266 : Nat.totient 31921205870776201222806763266 = 9665107213698457570461572160 := by
  rw [← show ((([(2, 1), (3, 1), (11, 1), (1277, 1), (23539, 1), (16090014941653837367, 1)] : List FactorBlock).map factorBlockValue).prod) = 31921205870776201222806763266 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentySevenY_2, prime_twentySevenY_3, prime_twentySevenY_11, prime_twentySevenY_1277, prime_twentySevenY_23539, prime_twentySevenY_16090014941653837367]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentySevenY_31921205870776201222806763267 : Nat.totient 31921205870776201222806763267 = 31915727716344971395927950720 := by
  rw [← show ((([(5827, 1), (5478154431229826878806721, 1)] : List FactorBlock).map factorBlockValue).prod) = 31921205870776201222806763267 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentySevenY_5827, prime_twentySevenY_5478154431229826878806721]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentySevenY_31921205870776201222806763268 : Nat.totient 31921205870776201222806763268 = 14863411671591878459545190400 := by
  rw [← show ((([(2, 2), (17, 1), (101, 1), (1549, 1), (33614473, 1), (89262958733513, 1)] : List FactorBlock).map factorBlockValue).prod) = 31921205870776201222806763268 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentySevenY_2, prime_twentySevenY_17, prime_twentySevenY_101, prime_twentySevenY_1549, prime_twentySevenY_33614473, prime_twentySevenY_89262958733513]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentySevenY_31921205870776201222806763269 : Nat.totient 31921205870776201222806763269 = 20341001497168636910601606576 := by
  rw [← show ((([(3, 1), (23, 1), (1399, 1), (330683468220325089585799, 1)] : List FactorBlock).map factorBlockValue).prod) = 31921205870776201222806763269 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentySevenY_3, prime_twentySevenY_23, prime_twentySevenY_1399, prime_twentySevenY_330683468220325089585799]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentySevenY_31921205870776201222806763270 : Nat.totient 31921205870776201222806763270 = 10944171741503031354319257600 := by
  rw [← show ((([(2, 1), (5, 1), (7, 1), (45281, 1), (10070829414663419606081, 1)] : List FactorBlock).map factorBlockValue).prod) = 31921205870776201222806763270 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentySevenY_2, prime_twentySevenY_5, prime_twentySevenY_7, prime_twentySevenY_45281, prime_twentySevenY_10070829414663419606081]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentySevenY_31921205870776201222806763271 : Nat.totient 31921205870776201222806763271 = 31921205870776201222806763270 := by
  rw [← show ((([(31921205870776201222806763271, 1)] : List FactorBlock).map factorBlockValue).prod) = 31921205870776201222806763271 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentySevenY_31921205870776201222806763271]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentySevenY_31921205870776201222806763272 : Nat.totient 31921205870776201222806763272 = 10611602142969028764886917120 := by
  rw [← show ((([(2, 3), (3, 2), (373, 1), (55249, 1), (157429, 1), (773027, 1), (176780411, 1)] : List FactorBlock).map factorBlockValue).prod) = 31921205870776201222806763272 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentySevenY_2, prime_twentySevenY_3, prime_twentySevenY_373, prime_twentySevenY_55249, prime_twentySevenY_157429, prime_twentySevenY_773027, prime_twentySevenY_176780411]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentySevenY_31921205870776201222806763273 : Nat.totient 31921205870776201222806763273 = 31449540872456928479863403136 := by
  rw [← show ((([(79, 1), (503, 1), (6367, 1), (58741289, 1), (2147859606583, 1)] : List FactorBlock).map factorBlockValue).prod) = 31921205870776201222806763273 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentySevenY_79, prime_twentySevenY_503, prime_twentySevenY_6367, prime_twentySevenY_58741289, prime_twentySevenY_2147859606583]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentySevenY_31921205870776201222806763274 : Nat.totient 31921205870776201222806763274 = 15529234406012791059232528272 := by
  rw [← show ((([(2, 1), (37, 1), (17597407, 1), (24513136901498106943, 1)] : List FactorBlock).map factorBlockValue).prod) = 31921205870776201222806763274 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentySevenY_2, prime_twentySevenY_37, prime_twentySevenY_17597407, prime_twentySevenY_24513136901498106943]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentySevenY_31921205870776201222806763275 : Nat.totient 31921205870776201222806763275 = 17024641703121768909528572160 := by
  rw [← show ((([(3, 1), (5, 2), (12759209, 1), (181957939, 1), (183325663427, 1)] : List FactorBlock).map factorBlockValue).prod) = 31921205870776201222806763275 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentySevenY_3, prime_twentySevenY_5, prime_twentySevenY_12759209, prime_twentySevenY_181957939, prime_twentySevenY_183325663427]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentySevenY_31921205870776201222806763276 : Nat.totient 31921205870776201222806763276 = 15120571201891038895099114944 := by
  rw [← show ((([(2, 2), (19, 1), (272085132469, 1), (1543692824776429, 1)] : List FactorBlock).map factorBlockValue).prod) = 31921205870776201222806763276 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentySevenY_2, prime_twentySevenY_19, prime_twentySevenY_272085132469, prime_twentySevenY_1543692824776429]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentySevenY_31921205870776201222806763277 : Nat.totient 31921205870776201222806763277 = 24862119931455554586823992000 := by
  rw [← show ((([(7, 1), (11, 1), (2671, 1), (11131, 1), (35769023, 1), (389828345987, 1)] : List FactorBlock).map factorBlockValue).prod) = 31921205870776201222806763277 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentySevenY_7, prime_twentySevenY_11, prime_twentySevenY_2671, prime_twentySevenY_11131, prime_twentySevenY_35769023, prime_twentySevenY_389828345987]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentySevenY_31921205870776201222806763278 : Nat.totient 31921205870776201222806763278 = 9804706615559969056831305600 := by
  rw [← show ((([(2, 1), (3, 1), (13, 1), (571, 1), (11213231, 1), (12829519, 1), (4982042579, 1)] : List FactorBlock).map factorBlockValue).prod) = 31921205870776201222806763278 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentySevenY_2, prime_twentySevenY_3, prime_twentySevenY_13, prime_twentySevenY_571, prime_twentySevenY_11213231, prime_twentySevenY_12829519, prime_twentySevenY_4982042579]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentySevenY_31921205870776201222806763279 : Nat.totient 31921205870776201222806763279 = 31829213923021802948389452376 := by
  rw [← show ((([(347, 1), (91991947754398274417310557, 1)] : List FactorBlock).map factorBlockValue).prod) = 31921205870776201222806763279 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentySevenY_347, prime_twentySevenY_91991947754398274417310557]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentySevenY_31921205870776201222806763280 : Nat.totient 31921205870776201222806763280 = 12768482348111966316770340864 := by
  rw [← show ((([(2, 4), (5, 1), (64320922717, 1), (6203503565088673, 1)] : List FactorBlock).map factorBlockValue).prod) = 31921205870776201222806763280 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentySevenY_2, prime_twentySevenY_5, prime_twentySevenY_64320922717, prime_twentySevenY_6203503565088673]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentySevenY_31921205870776201222806763281 : Nat.totient 31921205870776201222806763281 = 21280803913850800815204508800 := by
  rw [← show ((([(3, 4), (394088961367607422503787201, 1)] : List FactorBlock).map factorBlockValue).prod) = 31921205870776201222806763281 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentySevenY_3, prime_twentySevenY_394088961367607422503787201]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentySevenY_31921205870776201222806763282 : Nat.totient 31921205870776201222806763282 = 15526702974393903173578508160 := by
  rw [← show ((([(2, 1), (41, 1), (349, 1), (1115424064252435572814549, 1)] : List FactorBlock).map factorBlockValue).prod) = 31921205870776201222806763282 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentySevenY_2, prime_twentySevenY_41, prime_twentySevenY_349, prime_twentySevenY_1115424064252435572814549]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentySevenY_31921205870776201222806763283 : Nat.totient 31921205870776201222806763283 = 31638715341323992722477175680 := by
  rw [← show ((([(113, 1), (16712263, 1), (359093171, 1), (47071543367, 1)] : List FactorBlock).map factorBlockValue).prod) = 31921205870776201222806763283 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentySevenY_113, prime_twentySevenY_16712263, prime_twentySevenY_359093171, prime_twentySevenY_47071543367]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentySevenY_31921205870776201222806763284 : Nat.totient 31921205870776201222806763284 = 9119904342194415573477408096 := by
  rw [← show ((([(2, 2), (3, 1), (7, 1), (20719, 1), (18341346377937090882079, 1)] : List FactorBlock).map factorBlockValue).prod) = 31921205870776201222806763284 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentySevenY_2, prime_twentySevenY_3, prime_twentySevenY_7, prime_twentySevenY_20719, prime_twentySevenY_18341346377937090882079]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentySevenY_31921205870776201222806763285 : Nat.totient 31921205870776201222806763285 = 24011523322738187328329084928 := by
  rw [← show ((([(5, 1), (17, 1), (1033, 1), (363546561935837380818937, 1)] : List FactorBlock).map factorBlockValue).prod) = 31921205870776201222806763285 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentySevenY_5, prime_twentySevenY_17, prime_twentySevenY_1033, prime_twentySevenY_363546561935837380818937]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentySevenY_31921205870776201222806763286 : Nat.totient 31921205870776201222806763286 = 15508651894320959553001181184 := by
  rw [← show ((([(2, 1), (43, 1), (193, 1), (1923195919434642801711457, 1)] : List FactorBlock).map factorBlockValue).prod) = 31921205870776201222806763286 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentySevenY_2, prime_twentySevenY_43, prime_twentySevenY_193, prime_twentySevenY_1923195919434642801711457]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentySevenY_31921205870776201222806763287 : Nat.totient 31921205870776201222806763287 = 20500169726675530405479530880 := by
  rw [← show ((([(3, 1), (29, 1), (439, 1), (2284423, 1), (63388891, 1), (5771727763, 1)] : List FactorBlock).map factorBlockValue).prod) = 31921205870776201222806763287 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentySevenY_3, prime_twentySevenY_29, prime_twentySevenY_439, prime_twentySevenY_2284423, prime_twentySevenY_63388891, prime_twentySevenY_5771727763]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentySevenY_31921205870776201222806763288 : Nat.totient 31921205870776201222806763288 = 14291948761970975198560512000 := by
  rw [← show ((([(2, 3), (11, 1), (67, 1), (12953, 1), (570841, 1), (732211069909811, 1)] : List FactorBlock).map factorBlockValue).prod) = 31921205870776201222806763288 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentySevenY_2, prime_twentySevenY_11, prime_twentySevenY_67, prime_twentySevenY_12953, prime_twentySevenY_570841, prime_twentySevenY_732211069909811]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentySevenY_31921205870776201222806763289 : Nat.totient 31921205870776201222806763289 = 31797874014888145119313245840 := by
  rw [← show ((([(283, 1), (3019, 1), (66178525591, 1), (564563313527, 1)] : List FactorBlock).map factorBlockValue).prod) = 31921205870776201222806763289 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentySevenY_283, prime_twentySevenY_3019, prime_twentySevenY_66178525591, prime_twentySevenY_564563313527]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentySevenY_31921205870776201222806763290 : Nat.totient 31921205870776201222806763290 = 8512274414484471587507092608 := by
  rw [← show ((([(2, 1), (3, 2), (5, 1), (180533, 1), (1964627327030773765757, 1)] : List FactorBlock).map factorBlockValue).prod) = 31921205870776201222806763290 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentySevenY_2, prime_twentySevenY_3, prime_twentySevenY_5, prime_twentySevenY_180533, prime_twentySevenY_1964627327030773765757]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

theorem freeKill_64TwentySevenY : certifiedKill 1 31921205870776201222806763190 99 := by
  norm_num [certifiedKill, windowDiscrepancy, Finset.sum_range_succ,
    phi_twentySevenY_31921205870776201222806763191, phi_twentySevenY_31921205870776201222806763192, phi_twentySevenY_31921205870776201222806763193,
    phi_twentySevenY_31921205870776201222806763194, phi_twentySevenY_31921205870776201222806763195, phi_twentySevenY_31921205870776201222806763196,
    phi_twentySevenY_31921205870776201222806763197, phi_twentySevenY_31921205870776201222806763198, phi_twentySevenY_31921205870776201222806763199,
    phi_twentySevenY_31921205870776201222806763200, phi_twentySevenY_31921205870776201222806763201, phi_twentySevenY_31921205870776201222806763202,
    phi_twentySevenY_31921205870776201222806763203, phi_twentySevenY_31921205870776201222806763204, phi_twentySevenY_31921205870776201222806763205,
    phi_twentySevenY_31921205870776201222806763206, phi_twentySevenY_31921205870776201222806763207, phi_twentySevenY_31921205870776201222806763208,
    phi_twentySevenY_31921205870776201222806763209, phi_twentySevenY_31921205870776201222806763210, phi_twentySevenY_31921205870776201222806763211,
    phi_twentySevenY_31921205870776201222806763212, phi_twentySevenY_31921205870776201222806763213, phi_twentySevenY_31921205870776201222806763214,
    phi_twentySevenY_31921205870776201222806763215, phi_twentySevenY_31921205870776201222806763216, phi_twentySevenY_31921205870776201222806763217,
    phi_twentySevenY_31921205870776201222806763218, phi_twentySevenY_31921205870776201222806763219, phi_twentySevenY_31921205870776201222806763220,
    phi_twentySevenY_31921205870776201222806763221, phi_twentySevenY_31921205870776201222806763222, phi_twentySevenY_31921205870776201222806763223,
    phi_twentySevenY_31921205870776201222806763224, phi_twentySevenY_31921205870776201222806763225, phi_twentySevenY_31921205870776201222806763226,
    phi_twentySevenY_31921205870776201222806763227, phi_twentySevenY_31921205870776201222806763228, phi_twentySevenY_31921205870776201222806763229,
    phi_twentySevenY_31921205870776201222806763230, phi_twentySevenY_31921205870776201222806763231, phi_twentySevenY_31921205870776201222806763232,
    phi_twentySevenY_31921205870776201222806763233, phi_twentySevenY_31921205870776201222806763234, phi_twentySevenY_31921205870776201222806763235,
    phi_twentySevenY_31921205870776201222806763236, phi_twentySevenY_31921205870776201222806763237, phi_twentySevenY_31921205870776201222806763238,
    phi_twentySevenY_31921205870776201222806763239, phi_twentySevenY_31921205870776201222806763240, phi_twentySevenY_31921205870776201222806763241,
    phi_twentySevenY_31921205870776201222806763242, phi_twentySevenY_31921205870776201222806763243, phi_twentySevenY_31921205870776201222806763244,
    phi_twentySevenY_31921205870776201222806763245, phi_twentySevenY_31921205870776201222806763246, phi_twentySevenY_31921205870776201222806763247,
    phi_twentySevenY_31921205870776201222806763248, phi_twentySevenY_31921205870776201222806763249, phi_twentySevenY_31921205870776201222806763250,
    phi_twentySevenY_31921205870776201222806763251, phi_twentySevenY_31921205870776201222806763252, phi_twentySevenY_31921205870776201222806763253,
    phi_twentySevenY_31921205870776201222806763254, phi_twentySevenY_31921205870776201222806763255, phi_twentySevenY_31921205870776201222806763256,
    phi_twentySevenY_31921205870776201222806763257, phi_twentySevenY_31921205870776201222806763258, phi_twentySevenY_31921205870776201222806763259,
    phi_twentySevenY_31921205870776201222806763260, phi_twentySevenY_31921205870776201222806763261, phi_twentySevenY_31921205870776201222806763262,
    phi_twentySevenY_31921205870776201222806763263, phi_twentySevenY_31921205870776201222806763264, phi_twentySevenY_31921205870776201222806763265,
    phi_twentySevenY_31921205870776201222806763266, phi_twentySevenY_31921205870776201222806763267, phi_twentySevenY_31921205870776201222806763268,
    phi_twentySevenY_31921205870776201222806763269, phi_twentySevenY_31921205870776201222806763270, phi_twentySevenY_31921205870776201222806763271,
    phi_twentySevenY_31921205870776201222806763272, phi_twentySevenY_31921205870776201222806763273, phi_twentySevenY_31921205870776201222806763274,
    phi_twentySevenY_31921205870776201222806763275, phi_twentySevenY_31921205870776201222806763276, phi_twentySevenY_31921205870776201222806763277,
    phi_twentySevenY_31921205870776201222806763278, phi_twentySevenY_31921205870776201222806763279, phi_twentySevenY_31921205870776201222806763280,
    phi_twentySevenY_31921205870776201222806763281, phi_twentySevenY_31921205870776201222806763282, phi_twentySevenY_31921205870776201222806763283,
    phi_twentySevenY_31921205870776201222806763284, phi_twentySevenY_31921205870776201222806763285, phi_twentySevenY_31921205870776201222806763286,
    phi_twentySevenY_31921205870776201222806763287, phi_twentySevenY_31921205870776201222806763288, phi_twentySevenY_31921205870776201222806763289,
    phi_twentySevenY_31921205870776201222806763290]

end TotientTailPeriodKiller
end Erdos249257
