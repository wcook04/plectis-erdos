import Erdos249257.DiagonalPincerCertificatesT64

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

private def twentyFourVFastPow {M : Type*} [Monoid M] (a : M) (n : ℕ) : M :=
  Nat.binaryRec 1 (fun b _ r => if b then r * r * a else r * r) n

private theorem twentyFourVFastPow_eq_pow {M : Type*} [Monoid M] (a : M) (n : ℕ) :
    twentyFourVFastPow a n = a ^ n := by
  induction n using Nat.binaryRec with
  | zero => simp [twentyFourVFastPow, Nat.binaryRec_zero]
  | bit b n ih =>
      rw [twentyFourVFastPow, Nat.binaryRec_eq b n (by left; simp)]
      change (if b then twentyFourVFastPow a n * twentyFourVFastPow a n * a
        else twentyFourVFastPow a n * twentyFourVFastPow a n) = _
      rw [ih]
      cases b <;> simp [Nat.bit, two_mul, pow_add]

private theorem prime_twentyFourV_3 : Nat.Prime 3 := by norm_num
private theorem prime_twentyFourV_5 : Nat.Prime 5 := by norm_num
private theorem prime_twentyFourV_131 : Nat.Prime 131 := by norm_num
private theorem prime_twentyFourV_2 : Nat.Prime 2 := by norm_num
private theorem prime_twentyFourV_11 : Nat.Prime 11 := by norm_num
private theorem prime_twentyFourV_16561 : Nat.Prime 16561 := by norm_num
private theorem prime_twentyFourV_23 : Nat.Prime 23 := by norm_num
private theorem prime_twentyFourV_47 : Nat.Prime 47 := by norm_num
private theorem prime_twentyFourV_727 : Nat.Prime 727 := by norm_num
private theorem prime_twentyFourV_78588701 : Nat.Prime 78588701 := by
  apply lucas_primality 78588701 (2 : ZMod 78588701)
  · rw [← twentyFourVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (5, 2), (23, 1), (47, 1), (727, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (5, 2), (23, 1), (47, 1), (727, 1)] : List FactorBlock).map factorBlockValue).prod = 78588701 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyFourV_2
      · exact prime_twentyFourV_5
      · exact prime_twentyFourV_23
      · exact prime_twentyFourV_47
      · exact prime_twentyFourV_727
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 78588701) ^ 39294350 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (2 : ZMod 78588701) ^ 15717740 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (2 : ZMod 78588701) ^ 3416900 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (2 : ZMod 78588701) ^ 1672100 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (2 : ZMod 78588701) ^ 108100 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide

private theorem prime_twentyFourV_31 : Nat.Prime 31 := by norm_num
private theorem prime_twentyFourV_241 : Nat.Prime 241 := by norm_num
private theorem prime_twentyFourV_140629 : Nat.Prime 140629 := by norm_num
private theorem prime_twentyFourV_338915891 : Nat.Prime 338915891 := by
  apply lucas_primality 338915891 (2 : ZMod 338915891)
  · rw [← twentyFourVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 1), (241, 1), (140629, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 1), (241, 1), (140629, 1)] : List FactorBlock).map factorBlockValue).prod = 338915891 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyFourV_2
      · exact prime_twentyFourV_5
      · exact prime_twentyFourV_241
      · exact prime_twentyFourV_140629
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 338915891) ^ 169457945 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (2 : ZMod 338915891) ^ 67783178 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (2 : ZMod 338915891) ^ 1406290 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (2 : ZMod 338915891) ^ 2410 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide

private theorem prime_twentyFourV_84051140969 : Nat.Prime 84051140969 := by
  apply lucas_primality 84051140969 (3 : ZMod 84051140969)
  · rw [← twentyFourVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (31, 1), (338915891, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (31, 1), (338915891, 1)] : List FactorBlock).map factorBlockValue).prod = 84051140969 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twentyFourV_2
      · exact prime_twentyFourV_31
      · exact prime_twentyFourV_338915891
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 84051140969) ^ 42025570484 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (3 : ZMod 84051140969) ^ 2711327128 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (3 : ZMod 84051140969) ^ 248 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide

private theorem prime_twentyFourV_14439900874538287236779989 : Nat.Prime 14439900874538287236779989 := by
  apply lucas_primality 14439900874538287236779989 (6 : ZMod 14439900874538287236779989)
  · rw [← twentyFourVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (11, 1), (16561, 1), (78588701, 1), (84051140969, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (11, 1), (16561, 1), (78588701, 1), (84051140969, 1)] : List FactorBlock).map factorBlockValue).prod = 14439900874538287236779989 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyFourV_2
      · exact prime_twentyFourV_3
      · exact prime_twentyFourV_11
      · exact prime_twentyFourV_16561
      · exact prime_twentyFourV_78588701
      · exact prime_twentyFourV_84051140969
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 14439900874538287236779989) ^ 7219950437269143618389994 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (6 : ZMod 14439900874538287236779989) ^ 4813300291512762412259996 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (6 : ZMod 14439900874538287236779989) ^ 1312718261321662476070908 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (6 : ZMod 14439900874538287236779989) ^ 871922038194450047508 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (6 : ZMod 14439900874538287236779989) ^ 183740164817564388 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (6 : ZMod 14439900874538287236779989) ^ 171798986998452 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide

private theorem prime_twentyFourV_7 : Nat.Prime 7 := by norm_num
private theorem prime_twentyFourV_83 : Nat.Prime 83 := by norm_num
private theorem prime_twentyFourV_28723 : Nat.Prime 28723 := by norm_num
private theorem prime_twentyFourV_77029 : Nat.Prime 77029 := by norm_num
private theorem prime_twentyFourV_73 : Nat.Prime 73 := by norm_num
private theorem prime_twentyFourV_27427 : Nat.Prime 27427 := by norm_num
private theorem prime_twentyFourV_3062407 : Nat.Prime 3062407 := by norm_num
private theorem prime_twentyFourV_61314624855971 : Nat.Prime 61314624855971 := by
  apply lucas_primality 61314624855971 (2 : ZMod 61314624855971)
  · rw [← twentyFourVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 1), (73, 1), (27427, 1), (3062407, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 1), (73, 1), (27427, 1), (3062407, 1)] : List FactorBlock).map factorBlockValue).prod = 61314624855971 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyFourV_2
      · exact prime_twentyFourV_5
      · exact prime_twentyFourV_73
      · exact prime_twentyFourV_27427
      · exact prime_twentyFourV_3062407
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 61314624855971) ^ 30657312427985 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (2 : ZMod 61314624855971) ^ 12262924971194 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (2 : ZMod 61314624855971) ^ 839926367890 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (2 : ZMod 61314624855971) ^ 2235557110 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (2 : ZMod 61314624855971) ^ 20021710 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide

private theorem prime_twentyFourV_425070381422753114311 : Nat.Prime 425070381422753114311 := by
  apply lucas_primality 425070381422753114311 (3 : ZMod 425070381422753114311)
  · rw [← twentyFourVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 2), (5, 1), (77029, 1), (61314624855971, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 2), (5, 1), (77029, 1), (61314624855971, 1)] : List FactorBlock).map factorBlockValue).prod = 425070381422753114311 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyFourV_2
      · exact prime_twentyFourV_3
      · exact prime_twentyFourV_5
      · exact prime_twentyFourV_77029
      · exact prime_twentyFourV_61314624855971
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 425070381422753114311) ^ 212535190711376557155 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (3 : ZMod 425070381422753114311) ^ 141690127140917704770 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (3 : ZMod 425070381422753114311) ^ 85014076284550622862 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (3 : ZMod 425070381422753114311) ^ 5518316237037390 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (3 : ZMod 425070381422753114311) ^ 6932610 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide

private theorem prime_twentyFourV_2026743229890552458590905599 : Nat.Prime 2026743229890552458590905599 := by
  apply lucas_primality 2026743229890552458590905599 (71 : ZMod 2026743229890552458590905599)
  · rw [← twentyFourVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (83, 1), (28723, 1), (425070381422753114311, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (83, 1), (28723, 1), (425070381422753114311, 1)] : List FactorBlock).map factorBlockValue).prod = 2026743229890552458590905599 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyFourV_2
      · exact prime_twentyFourV_83
      · exact prime_twentyFourV_28723
      · exact prime_twentyFourV_425070381422753114311
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (71 : ZMod 2026743229890552458590905599) ^ 1013371614945276229295452799 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (71 : ZMod 2026743229890552458590905599) ^ 24418593131211475404709706 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (71 : ZMod 2026743229890552458590905599) ^ 70561683316177016975626 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (71 : ZMod 2026743229890552458590905599) ^ 4768018 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide

private theorem prime_twentyFourV_13 : Nat.Prime 13 := by norm_num
private theorem prime_twentyFourV_58153 : Nat.Prime 58153 := by norm_num
private theorem prime_twentyFourV_392143 : Nat.Prime 392143 := by norm_num
private theorem prime_twentyFourV_3373 : Nat.Prime 3373 := by norm_num
private theorem prime_twentyFourV_9431 : Nat.Prime 9431 := by norm_num
private theorem prime_twentyFourV_19 : Nat.Prime 19 := by norm_num
private theorem prime_twentyFourV_152267 : Nat.Prime 152267 := by norm_num
private theorem prime_twentyFourV_75219899 : Nat.Prime 75219899 := by
  apply lucas_primality 75219899 (2 : ZMod 75219899)
  · rw [← twentyFourVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (13, 1), (19, 1), (152267, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (13, 1), (19, 1), (152267, 1)] : List FactorBlock).map factorBlockValue).prod = 75219899 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyFourV_2
      · exact prime_twentyFourV_13
      · exact prime_twentyFourV_19
      · exact prime_twentyFourV_152267
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 75219899) ^ 37609949 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (2 : ZMod 75219899) ^ 5786146 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (2 : ZMod 75219899) ^ 3958942 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (2 : ZMod 75219899) ^ 494 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide

private theorem prime_twentyFourV_95712095198917481 : Nat.Prime 95712095198917481 := by
  apply lucas_primality 95712095198917481 (3 : ZMod 95712095198917481)
  · rw [← twentyFourVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (5, 1), (3373, 1), (9431, 1), (75219899, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (5, 1), (3373, 1), (9431, 1), (75219899, 1)] : List FactorBlock).map factorBlockValue).prod = 95712095198917481 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyFourV_2
      · exact prime_twentyFourV_5
      · exact prime_twentyFourV_3373
      · exact prime_twentyFourV_9431
      · exact prime_twentyFourV_75219899
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 95712095198917481) ^ 47856047599458740 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (3 : ZMod 95712095198917481) ^ 19142419039783496 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (3 : ZMod 95712095198917481) ^ 28375954698760 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (3 : ZMod 95712095198917481) ^ 10148668773080 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (3 : ZMod 95712095198917481) ^ 1272430520 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide

private theorem prime_twentyFourV_1531 : Nat.Prime 1531 := by norm_num
private theorem prime_twentyFourV_11923 : Nat.Prime 11923 := by norm_num
private theorem prime_twentyFourV_28807 : Nat.Prime 28807 := by norm_num
private theorem prime_twentyFourV_23017 : Nat.Prime 23017 := by norm_num
private theorem prime_twentyFourV_152287 : Nat.Prime 152287 := by norm_num
private theorem prime_twentyFourV_151677853 : Nat.Prime 151677853 := by
  apply lucas_primality 151677853 (2 : ZMod 151677853)
  · rw [← twentyFourVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (83, 1), (152287, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (83, 1), (152287, 1)] : List FactorBlock).map factorBlockValue).prod = 151677853 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyFourV_2
      · exact prime_twentyFourV_3
      · exact prime_twentyFourV_83
      · exact prime_twentyFourV_152287
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 151677853) ^ 75838926 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (2 : ZMod 151677853) ^ 50559284 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (2 : ZMod 151677853) ^ 1827444 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (2 : ZMod 151677853) ^ 996 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide

private theorem prime_twentyFourV_4496625855541289 : Nat.Prime 4496625855541289 := by
  apply lucas_primality 4496625855541289 (3 : ZMod 4496625855541289)
  · rw [← twentyFourVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (7, 1), (23, 1), (23017, 1), (151677853, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (7, 1), (23, 1), (23017, 1), (151677853, 1)] : List FactorBlock).map factorBlockValue).prod = 4496625855541289 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyFourV_2
      · exact prime_twentyFourV_7
      · exact prime_twentyFourV_23
      · exact prime_twentyFourV_23017
      · exact prime_twentyFourV_151677853
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 4496625855541289) ^ 2248312927770644 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (3 : ZMod 4496625855541289) ^ 642375122220184 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (3 : ZMod 4496625855541289) ^ 195505471980056 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (3 : ZMod 4496625855541289) ^ 195361074664 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (3 : ZMod 4496625855541289) ^ 29645896 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide

private theorem prime_twentyFourV_337 : Nat.Prime 337 := by norm_num
private theorem prime_twentyFourV_20747 : Nat.Prime 20747 := by norm_num
private theorem prime_twentyFourV_127 : Nat.Prime 127 := by norm_num
private theorem prime_twentyFourV_251059 : Nat.Prime 251059 := by norm_num
private theorem prime_twentyFourV_499 : Nat.Prime 499 := by norm_num
private theorem prime_twentyFourV_11489 : Nat.Prime 11489 := by norm_num
private theorem prime_twentyFourV_206388397 : Nat.Prime 206388397 := by
  apply lucas_primality 206388397 (2 : ZMod 206388397)
  · rw [← twentyFourVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 2), (499, 1), (11489, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 2), (499, 1), (11489, 1)] : List FactorBlock).map factorBlockValue).prod = 206388397 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyFourV_2
      · exact prime_twentyFourV_3
      · exact prime_twentyFourV_499
      · exact prime_twentyFourV_11489
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 206388397) ^ 103194198 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (2 : ZMod 206388397) ^ 68796132 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (2 : ZMod 206388397) ^ 413604 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (2 : ZMod 206388397) ^ 17964 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide

private theorem prime_twentyFourV_631736582345061217 : Nat.Prime 631736582345061217 := by
  apply lucas_primality 631736582345061217 (11 : ZMod 631736582345061217)
  · rw [← twentyFourVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 5), (3, 1), (127, 1), (251059, 1), (206388397, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 5), (3, 1), (127, 1), (251059, 1), (206388397, 1)] : List FactorBlock).map factorBlockValue).prod = 631736582345061217 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyFourV_2
      · exact prime_twentyFourV_3
      · exact prime_twentyFourV_127
      · exact prime_twentyFourV_251059
      · exact prime_twentyFourV_206388397
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 631736582345061217) ^ 315868291172530608 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (11 : ZMod 631736582345061217) ^ 210578860781687072 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (11 : ZMod 631736582345061217) ^ 4974303797992608 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (11 : ZMod 631736582345061217) ^ 2516287336224 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (11 : ZMod 631736582345061217) ^ 3060911328 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide

private theorem prime_twentyFourV_26213277747825970138199 : Nat.Prime 26213277747825970138199 := by
  apply lucas_primality 26213277747825970138199 (7 : ZMod 26213277747825970138199)
  · rw [← twentyFourVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (20747, 1), (631736582345061217, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (20747, 1), (631736582345061217, 1)] : List FactorBlock).map factorBlockValue).prod = 26213277747825970138199 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twentyFourV_2
      · exact prime_twentyFourV_20747
      · exact prime_twentyFourV_631736582345061217
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 26213277747825970138199) ^ 13106638873912985069099 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (7 : ZMod 26213277747825970138199) ^ 1263473164690122434 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (7 : ZMod 26213277747825970138199) ^ 41494 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide

private theorem prime_twentyFourV_1289745691748533382739667199 : Nat.Prime 1289745691748533382739667199 := by
  apply lucas_primality 1289745691748533382739667199 (67 : ZMod 1289745691748533382739667199)
  · rw [← twentyFourVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (73, 1), (337, 1), (26213277747825970138199, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (73, 1), (337, 1), (26213277747825970138199, 1)] : List FactorBlock).map factorBlockValue).prod = 1289745691748533382739667199 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyFourV_2
      · exact prime_twentyFourV_73
      · exact prime_twentyFourV_337
      · exact prime_twentyFourV_26213277747825970138199
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (67 : ZMod 1289745691748533382739667199) ^ 644872845874266691369833599 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (67 : ZMod 1289745691748533382739667199) ^ 17667749202034703873146126 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (67 : ZMod 1289745691748533382739667199) ^ 3827138551182591640177054 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (67 : ZMod 1289745691748533382739667199) ^ 49202 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide

private theorem prime_twentyFourV_2579491383497066765479334399 : Nat.Prime 2579491383497066765479334399 := by
  apply lucas_primality 2579491383497066765479334399 (11 : ZMod 2579491383497066765479334399)
  · rw [← twentyFourVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (1289745691748533382739667199, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (1289745691748533382739667199, 1)] : List FactorBlock).map factorBlockValue).prod = 2579491383497066765479334399 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_twentyFourV_2
      · exact prime_twentyFourV_1289745691748533382739667199
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (11 : ZMod 2579491383497066765479334399) ^ 1289745691748533382739667199 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (11 : ZMod 2579491383497066765479334399) ^ 2 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide

private theorem prime_twentyFourV_24061 : Nat.Prime 24061 := by norm_num
private theorem prime_twentyFourV_53 : Nat.Prime 53 := by norm_num
private theorem prime_twentyFourV_227989 : Nat.Prime 227989 := by norm_num
private theorem prime_twentyFourV_8883997 : Nat.Prime 8883997 := by norm_num
private theorem prime_twentyFourV_41 : Nat.Prime 41 := by norm_num
private theorem prime_twentyFourV_2791 : Nat.Prime 2791 := by norm_num
private theorem prime_twentyFourV_549268801 : Nat.Prime 549268801 := by
  apply lucas_primality 549268801 (23 : ZMod 549268801)
  · rw [← twentyFourVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 6), (3, 1), (5, 2), (41, 1), (2791, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 6), (3, 1), (5, 2), (41, 1), (2791, 1)] : List FactorBlock).map factorBlockValue).prod = 549268801 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyFourV_2
      · exact prime_twentyFourV_3
      · exact prime_twentyFourV_5
      · exact prime_twentyFourV_41
      · exact prime_twentyFourV_2791
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (23 : ZMod 549268801) ^ 274634400 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (23 : ZMod 549268801) ^ 183089600 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (23 : ZMod 549268801) ^ 109853760 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (23 : ZMod 549268801) ^ 13396800 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (23 : ZMod 549268801) ^ 196800 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide

private theorem prime_twentyFourV_117926957393573560617899 : Nat.Prime 117926957393573560617899 := by
  apply lucas_primality 117926957393573560617899 (2 : ZMod 117926957393573560617899)
  · rw [← twentyFourVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (53, 1), (227989, 1), (8883997, 1), (549268801, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (53, 1), (227989, 1), (8883997, 1), (549268801, 1)] : List FactorBlock).map factorBlockValue).prod = 117926957393573560617899 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyFourV_2
      · exact prime_twentyFourV_53
      · exact prime_twentyFourV_227989
      · exact prime_twentyFourV_8883997
      · exact prime_twentyFourV_549268801
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 117926957393573560617899) ^ 58963478696786780308949 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (2 : ZMod 117926957393573560617899) ^ 2225036931954218124866 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (2 : ZMod 117926957393573560617899) ^ 517248452309425282 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (2 : ZMod 117926957393573560617899) ^ 13274087935146034 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (2 : ZMod 117926957393573560617899) ^ 214698080755498 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide

private theorem prime_twentyFourV_229 : Nat.Prime 229 := by norm_num
private theorem prime_twentyFourV_557 : Nat.Prime 557 := by norm_num
private theorem prime_twentyFourV_186227381 : Nat.Prime 186227381 := by
  apply lucas_primality 186227381 (2 : ZMod 186227381)
  · rw [← twentyFourVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (5, 1), (73, 1), (229, 1), (557, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (5, 1), (73, 1), (229, 1), (557, 1)] : List FactorBlock).map factorBlockValue).prod = 186227381 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyFourV_2
      · exact prime_twentyFourV_5
      · exact prime_twentyFourV_73
      · exact prime_twentyFourV_229
      · exact prime_twentyFourV_557
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 186227381) ^ 93113690 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (2 : ZMod 186227381) ^ 37245476 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (2 : ZMod 186227381) ^ 2551060 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (2 : ZMod 186227381) ^ 813220 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (2 : ZMod 186227381) ^ 334340 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide

private theorem prime_twentyFourV_372454763 : Nat.Prime 372454763 := by
  apply lucas_primality 372454763 (2 : ZMod 372454763)
  · rw [← twentyFourVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (186227381, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (186227381, 1)] : List FactorBlock).map factorBlockValue).prod = 372454763 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_twentyFourV_2
      · exact prime_twentyFourV_186227381
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 372454763) ^ 186227381 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (2 : ZMod 372454763) ^ 2 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide

private theorem prime_twentyFourV_991 : Nat.Prime 991 := by norm_num
private theorem prime_twentyFourV_56809 : Nat.Prime 56809 := by norm_num
private theorem prime_twentyFourV_2281 : Nat.Prime 2281 := by norm_num
private theorem prime_twentyFourV_20807 : Nat.Prime 20807 := by norm_num
private theorem prime_twentyFourV_1139058409 : Nat.Prime 1139058409 := by
  apply lucas_primality 1139058409 (13 : ZMod 1139058409)
  · rw [← twentyFourVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (3, 1), (2281, 1), (20807, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (3, 1), (2281, 1), (20807, 1)] : List FactorBlock).map factorBlockValue).prod = 1139058409 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyFourV_2
      · exact prime_twentyFourV_3
      · exact prime_twentyFourV_2281
      · exact prime_twentyFourV_20807
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (13 : ZMod 1139058409) ^ 569529204 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (13 : ZMod 1139058409) ^ 379686136 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (13 : ZMod 1139058409) ^ 499368 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (13 : ZMod 1139058409) ^ 54744 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide

private theorem prime_twentyFourV_8464683510949917373 : Nat.Prime 8464683510949917373 := by
  apply lucas_primality 8464683510949917373 (2 : ZMod 8464683510949917373)
  · rw [← twentyFourVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (11, 1), (991, 1), (56809, 1), (1139058409, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (11, 1), (991, 1), (56809, 1), (1139058409, 1)] : List FactorBlock).map factorBlockValue).prod = 8464683510949917373 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyFourV_2
      · exact prime_twentyFourV_3
      · exact prime_twentyFourV_11
      · exact prime_twentyFourV_991
      · exact prime_twentyFourV_56809
      · exact prime_twentyFourV_1139058409
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 8464683510949917373) ^ 4232341755474958686 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (2 : ZMod 8464683510949917373) ^ 2821561170316639124 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (2 : ZMod 8464683510949917373) ^ 769516682813628852 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (2 : ZMod 8464683510949917373) ^ 8541557528708292 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (2 : ZMod 8464683510949917373) ^ 149002508598108 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (2 : ZMod 8464683510949917373) ^ 7431298908 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide

private theorem prime_twentyFourV_3923 : Nat.Prime 3923 := by norm_num
private theorem prime_twentyFourV_8197093 : Nat.Prime 8197093 := by norm_num
private theorem prime_twentyFourV_149 : Nat.Prime 149 := by norm_num
private theorem prime_twentyFourV_929 : Nat.Prime 929 := by norm_num
private theorem prime_twentyFourV_1796567 : Nat.Prime 1796567 := by norm_num
private theorem prime_twentyFourV_110295707065568641 : Nat.Prime 110295707065568641 := by
  apply lucas_primality 110295707065568641 (26 : ZMod 110295707065568641)
  · rw [← twentyFourVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 7), (3, 2), (5, 1), (7, 1), (11, 1), (149, 1), (929, 1), (1796567, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 7), (3, 2), (5, 1), (7, 1), (11, 1), (149, 1), (929, 1), (1796567, 1)] : List FactorBlock).map factorBlockValue).prod = 110295707065568641 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyFourV_2
      · exact prime_twentyFourV_3
      · exact prime_twentyFourV_5
      · exact prime_twentyFourV_7
      · exact prime_twentyFourV_11
      · exact prime_twentyFourV_149
      · exact prime_twentyFourV_929
      · exact prime_twentyFourV_1796567
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (26 : ZMod 110295707065568641) ^ 55147853532784320 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (26 : ZMod 110295707065568641) ^ 36765235688522880 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (26 : ZMod 110295707065568641) ^ 22059141413113728 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (26 : ZMod 110295707065568641) ^ 15756529580795520 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (26 : ZMod 110295707065568641) ^ 10026882460506240 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (26 : ZMod 110295707065568641) ^ 740239644735360 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (26 : ZMod 110295707065568641) ^ 118725195980160 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (26 : ZMod 110295707065568641) ^ 61392481920 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide

private theorem prime_twentyFourV_1163 : Nat.Prime 1163 := by norm_num
private theorem prime_twentyFourV_60773 : Nat.Prime 60773 := by norm_num
private theorem prime_twentyFourV_1269173 : Nat.Prime 1269173 := by norm_num
private theorem prime_twentyFourV_3473737 : Nat.Prime 3473737 := by norm_num
private theorem prime_twentyFourV_13008301 : Nat.Prime 13008301 := by norm_num
private theorem prime_twentyFourV_18713 : Nat.Prime 18713 := by norm_num
private theorem prime_twentyFourV_109469 : Nat.Prime 109469 := by norm_num
private theorem prime_twentyFourV_1701179 : Nat.Prime 1701179 := by norm_num
private theorem prime_twentyFourV_2269 : Nat.Prime 2269 := by norm_num
private theorem prime_twentyFourV_300239 : Nat.Prime 300239 := by norm_num
private theorem prime_twentyFourV_1357034643673 : Nat.Prime 1357034643673 := by
  apply lucas_primality 1357034643673 (5 : ZMod 1357034643673)
  · rw [← twentyFourVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (3, 1), (83, 1), (2269, 1), (300239, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (3, 1), (83, 1), (2269, 1), (300239, 1)] : List FactorBlock).map factorBlockValue).prod = 1357034643673 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyFourV_2
      · exact prime_twentyFourV_3
      · exact prime_twentyFourV_83
      · exact prime_twentyFourV_2269
      · exact prime_twentyFourV_300239
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 1357034643673) ^ 678517321836 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (5 : ZMod 1357034643673) ^ 452344881224 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (5 : ZMod 1357034643673) ^ 16349814984 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (5 : ZMod 1357034643673) ^ 598076088 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (5 : ZMod 1357034643673) ^ 4519848 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide

private theorem prime_twentyFourV_5674881043693546884054535679 : Nat.Prime 5674881043693546884054535679 := by
  apply lucas_primality 5674881043693546884054535679 (103 : ZMod 5674881043693546884054535679)
  · rw [← twentyFourVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (24061, 1), (117926957393573560617899, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (24061, 1), (117926957393573560617899, 1)] : List FactorBlock).map factorBlockValue).prod = 5674881043693546884054535679 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twentyFourV_2
      · exact prime_twentyFourV_24061
      · exact prime_twentyFourV_117926957393573560617899
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (103 : ZMod 5674881043693546884054535679) ^ 2837440521846773442027267839 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (103 : ZMod 5674881043693546884054535679) ^ 235853914787147121235798 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (103 : ZMod 5674881043693546884054535679) ^ 48122 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide

private theorem prime_twentyFourV_71 : Nat.Prime 71 := by norm_num
private theorem prime_twentyFourV_11633 : Nat.Prime 11633 := by norm_num
private theorem prime_twentyFourV_43 : Nat.Prime 43 := by norm_num
private theorem prime_twentyFourV_109 : Nat.Prime 109 := by norm_num
private theorem prime_twentyFourV_173 : Nat.Prime 173 := by norm_num
private theorem prime_twentyFourV_311 : Nat.Prime 311 := by norm_num
private theorem prime_twentyFourV_2169877 : Nat.Prime 2169877 := by norm_num
private theorem prime_twentyFourV_789835229 : Nat.Prime 789835229 := by
  apply lucas_primality 789835229 (10 : ZMod 789835229)
  · rw [← twentyFourVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (7, 1), (13, 1), (2169877, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (7, 1), (13, 1), (2169877, 1)] : List FactorBlock).map factorBlockValue).prod = 789835229 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyFourV_2
      · exact prime_twentyFourV_7
      · exact prime_twentyFourV_13
      · exact prime_twentyFourV_2169877
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (10 : ZMod 789835229) ^ 394917614 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (10 : ZMod 789835229) ^ 112833604 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (10 : ZMod 789835229) ^ 60756556 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (10 : ZMod 789835229) ^ 364 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide

private theorem prime_twentyFourV_86881875191 : Nat.Prime 86881875191 := by
  apply lucas_primality 86881875191 (11 : ZMod 86881875191)
  · rw [← twentyFourVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 1), (11, 1), (789835229, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 1), (11, 1), (789835229, 1)] : List FactorBlock).map factorBlockValue).prod = 86881875191 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyFourV_2
      · exact prime_twentyFourV_5
      · exact prime_twentyFourV_11
      · exact prime_twentyFourV_789835229
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 86881875191) ^ 43440937595 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (11 : ZMod 86881875191) ^ 17376375038 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (11 : ZMod 86881875191) ^ 7898352290 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (11 : ZMod 86881875191) ^ 110 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide

private theorem prime_twentyFourV_8588487709947216218393 : Nat.Prime 8588487709947216218393 := by
  apply lucas_primality 8588487709947216218393 (5 : ZMod 8588487709947216218393)
  · rw [← twentyFourVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (7, 2), (43, 1), (109, 1), (173, 1), (311, 1), (86881875191, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (7, 2), (43, 1), (109, 1), (173, 1), (311, 1), (86881875191, 1)] : List FactorBlock).map factorBlockValue).prod = 8588487709947216218393 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyFourV_2
      · exact prime_twentyFourV_7
      · exact prime_twentyFourV_43
      · exact prime_twentyFourV_109
      · exact prime_twentyFourV_173
      · exact prime_twentyFourV_311
      · exact prime_twentyFourV_86881875191
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 8588487709947216218393) ^ 4294243854973608109196 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (5 : ZMod 8588487709947216218393) ^ 1226926815706745174056 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (5 : ZMod 8588487709947216218393) ^ 199732272324353865544 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (5 : ZMod 8588487709947216218393) ^ 78793465228873543288 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (5 : ZMod 8588487709947216218393) ^ 49644437629752694904 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (5 : ZMod 8588487709947216218393) ^ 27615716109155036072 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (5 : ZMod 8588487709947216218393) ^ 98852467112 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide

private theorem prime_twentyFourV_566437 : Nat.Prime 566437 := by norm_num
private theorem prime_twentyFourV_5397907 : Nat.Prime 5397907 := by norm_num
private theorem prime_twentyFourV_4111 : Nat.Prime 4111 := by norm_num
private theorem prime_twentyFourV_491 : Nat.Prime 491 := by norm_num
private theorem prime_twentyFourV_1197263 : Nat.Prime 1197263 := by norm_num
private theorem prime_twentyFourV_2351424533 : Nat.Prime 2351424533 := by
  apply lucas_primality 2351424533 (2 : ZMod 2351424533)
  · rw [← twentyFourVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (491, 1), (1197263, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (491, 1), (1197263, 1)] : List FactorBlock).map factorBlockValue).prod = 2351424533 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twentyFourV_2
      · exact prime_twentyFourV_491
      · exact prime_twentyFourV_1197263
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 2351424533) ^ 1175712266 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (2 : ZMod 2351424533) ^ 4789052 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (2 : ZMod 2351424533) ^ 1964 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide

private theorem prime_twentyFourV_3093346001652161 : Nat.Prime 3093346001652161 := by
  apply lucas_primality 3093346001652161 (3 : ZMod 3093346001652161)
  · rw [← twentyFourVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 6), (5, 1), (4111, 1), (2351424533, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 6), (5, 1), (4111, 1), (2351424533, 1)] : List FactorBlock).map factorBlockValue).prod = 3093346001652161 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyFourV_2
      · exact prime_twentyFourV_5
      · exact prime_twentyFourV_4111
      · exact prime_twentyFourV_2351424533
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 3093346001652161) ^ 1546673000826080 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (3 : ZMod 3093346001652161) ^ 618669200330432 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (3 : ZMod 3093346001652161) ^ 752455850560 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (3 : ZMod 3093346001652161) ^ 1315520 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide

private theorem prime_twentyFourV_373 : Nat.Prime 373 := by norm_num
private theorem prime_twentyFourV_9721 : Nat.Prime 9721 := by norm_num
private theorem prime_twentyFourV_36259331 : Nat.Prime 36259331 := by
  apply lucas_primality 36259331 (2 : ZMod 36259331)
  · rw [← twentyFourVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 1), (373, 1), (9721, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 1), (373, 1), (9721, 1)] : List FactorBlock).map factorBlockValue).prod = 36259331 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyFourV_2
      · exact prime_twentyFourV_5
      · exact prime_twentyFourV_373
      · exact prime_twentyFourV_9721
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 36259331) ^ 18129665 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (2 : ZMod 36259331) ^ 7251866 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (2 : ZMod 36259331) ^ 97210 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (2 : ZMod 36259331) ^ 3730 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide

private theorem prime_twentyFourV_1483 : Nat.Prime 1483 := by norm_num
private theorem prime_twentyFourV_25639 : Nat.Prime 25639 := by norm_num
private theorem prime_twentyFourV_5669 : Nat.Prime 5669 := by norm_num
private theorem prime_twentyFourV_6302833 : Nat.Prime 6302833 := by norm_num
private theorem prime_twentyFourV_75633997 : Nat.Prime 75633997 := by
  apply lucas_primality 75633997 (2 : ZMod 75633997)
  · rw [← twentyFourVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (6302833, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (6302833, 1)] : List FactorBlock).map factorBlockValue).prod = 75633997 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twentyFourV_2
      · exact prime_twentyFourV_3
      · exact prime_twentyFourV_6302833
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 75633997) ^ 37816998 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (2 : ZMod 75633997) ^ 25211332 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (2 : ZMod 75633997) ^ 12 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide

private theorem prime_twentyFourV_857538257987 : Nat.Prime 857538257987 := by
  apply lucas_primality 857538257987 (2 : ZMod 857538257987)
  · rw [← twentyFourVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5669, 1), (75633997, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5669, 1), (75633997, 1)] : List FactorBlock).map factorBlockValue).prod = 857538257987 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twentyFourV_2
      · exact prime_twentyFourV_5669
      · exact prime_twentyFourV_75633997
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 857538257987) ^ 428769128993 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (2 : ZMod 857538257987) ^ 151267994 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (2 : ZMod 857538257987) ^ 11338 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide

private theorem prime_twentyFourV_391270390764624620629 : Nat.Prime 391270390764624620629 := by
  apply lucas_primality 391270390764624620629 (2 : ZMod 391270390764624620629)
  · rw [← twentyFourVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (1483, 1), (25639, 1), (857538257987, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (1483, 1), (25639, 1), (857538257987, 1)] : List FactorBlock).map factorBlockValue).prod = 391270390764624620629 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyFourV_2
      · exact prime_twentyFourV_3
      · exact prime_twentyFourV_1483
      · exact prime_twentyFourV_25639
      · exact prime_twentyFourV_857538257987
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 391270390764624620629) ^ 195635195382312310314 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (2 : ZMod 391270390764624620629) ^ 130423463588208206876 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (2 : ZMod 391270390764624620629) ^ 263837080758344316 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (2 : ZMod 391270390764624620629) ^ 15260750839136652 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (2 : ZMod 391270390764624620629) ^ 456271644 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide

private theorem prime_twentyFourV_28374405218467734420272678399 : Nat.Prime 28374405218467734420272678399 := by
  apply lucas_primality 28374405218467734420272678399 (67 : ZMod 28374405218467734420272678399)
  · rw [← twentyFourVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (36259331, 1), (391270390764624620629, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (36259331, 1), (391270390764624620629, 1)] : List FactorBlock).map factorBlockValue).prod = 28374405218467734420272678399 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twentyFourV_2
      · exact prime_twentyFourV_36259331
      · exact prime_twentyFourV_391270390764624620629
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (67 : ZMod 28374405218467734420272678399) ^ 14187202609233867210136339199 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (67 : ZMod 28374405218467734420272678399) ^ 782540781529249241258 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (67 : ZMod 28374405218467734420272678399) ^ 72518662 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide

private theorem prime_twentyFourV_17 : Nat.Prime 17 := by norm_num
private theorem prime_twentyFourV_29 : Nat.Prime 29 := by norm_num
private theorem prime_twentyFourV_37 : Nat.Prime 37 := by norm_num
private theorem prime_twentyFourV_59 : Nat.Prime 59 := by norm_num
private theorem prime_twentyFourV_61 : Nat.Prime 61 := by norm_num
private theorem prime_twentyFourV_191 : Nat.Prime 191 := by norm_num
private theorem prime_twentyFourV_443 : Nat.Prime 443 := by norm_num
private theorem prime_twentyFourV_1721 : Nat.Prime 1721 := by norm_num
private theorem prime_twentyFourV_922507631 : Nat.Prime 922507631 := by
  apply lucas_primality 922507631 (11 : ZMod 922507631)
  · rw [← twentyFourVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 1), (11, 2), (443, 1), (1721, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 1), (11, 2), (443, 1), (1721, 1)] : List FactorBlock).map factorBlockValue).prod = 922507631 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyFourV_2
      · exact prime_twentyFourV_5
      · exact prime_twentyFourV_11
      · exact prime_twentyFourV_443
      · exact prime_twentyFourV_1721
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 922507631) ^ 461253815 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (11 : ZMod 922507631) ^ 184501526 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (11 : ZMod 922507631) ^ 83864330 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (11 : ZMod 922507631) ^ 2082410 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (11 : ZMod 922507631) ^ 536030 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide

private theorem prime_twentyFourV_103 : Nat.Prime 103 := by norm_num
private theorem prime_twentyFourV_19403 : Nat.Prime 19403 := by norm_num
private theorem prime_twentyFourV_9428965463 : Nat.Prime 9428965463 := by
  apply lucas_primality 9428965463 (5 : ZMod 9428965463)
  · rw [← twentyFourVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (7, 1), (103, 1), (337, 1), (19403, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (7, 1), (103, 1), (337, 1), (19403, 1)] : List FactorBlock).map factorBlockValue).prod = 9428965463 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyFourV_2
      · exact prime_twentyFourV_7
      · exact prime_twentyFourV_103
      · exact prime_twentyFourV_337
      · exact prime_twentyFourV_19403
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 9428965463) ^ 4714482731 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (5 : ZMod 9428965463) ^ 1346995066 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (5 : ZMod 9428965463) ^ 91543354 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (5 : ZMod 9428965463) ^ 27979126 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (5 : ZMod 9428965463) ^ 485954 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide

private theorem prime_twentyFourV_1716071714267 : Nat.Prime 1716071714267 := by
  apply lucas_primality 1716071714267 (2 : ZMod 1716071714267)
  · rw [← twentyFourVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (7, 1), (13, 1), (9428965463, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (7, 1), (13, 1), (9428965463, 1)] : List FactorBlock).map factorBlockValue).prod = 1716071714267 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyFourV_2
      · exact prime_twentyFourV_7
      · exact prime_twentyFourV_13
      · exact prime_twentyFourV_9428965463
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1716071714267) ^ 858035857133 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (2 : ZMod 1716071714267) ^ 245153102038 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (2 : ZMod 1716071714267) ^ 132005516482 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (2 : ZMod 1716071714267) ^ 182 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide

private theorem prime_twentyFourV_161036169666815281 : Nat.Prime 161036169666815281 := by
  apply lucas_primality 161036169666815281 (13 : ZMod 161036169666815281)
  · rw [← twentyFourVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 4), (3, 1), (5, 1), (17, 1), (23, 1), (1716071714267, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 4), (3, 1), (5, 1), (17, 1), (23, 1), (1716071714267, 1)] : List FactorBlock).map factorBlockValue).prod = 161036169666815281 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyFourV_2
      · exact prime_twentyFourV_3
      · exact prime_twentyFourV_5
      · exact prime_twentyFourV_17
      · exact prime_twentyFourV_23
      · exact prime_twentyFourV_1716071714267
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 161036169666815281) ^ 80518084833407640 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (13 : ZMod 161036169666815281) ^ 53678723222271760 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (13 : ZMod 161036169666815281) ^ 32207233933363056 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (13 : ZMod 161036169666815281) ^ 9472715862753840 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (13 : ZMod 161036169666815281) ^ 7001572594209360 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (13 : ZMod 161036169666815281) ^ 93840 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide

private theorem prime_twentyFourV_181 : Nat.Prime 181 := by norm_num
private theorem prime_twentyFourV_317 : Nat.Prime 317 := by norm_num
private theorem prime_twentyFourV_372377 : Nat.Prime 372377 := by norm_num
private theorem prime_twentyFourV_6305347 : Nat.Prime 6305347 := by norm_num
private theorem prime_twentyFourV_441374291 : Nat.Prime 441374291 := by
  apply lucas_primality 441374291 (6 : ZMod 441374291)
  · rw [← twentyFourVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 1), (7, 1), (6305347, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 1), (7, 1), (6305347, 1)] : List FactorBlock).map factorBlockValue).prod = 441374291 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyFourV_2
      · exact prime_twentyFourV_5
      · exact prime_twentyFourV_7
      · exact prime_twentyFourV_6305347
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 441374291) ^ 220687145 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (6 : ZMod 441374291) ^ 88274858 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (6 : ZMod 441374291) ^ 63053470 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (6 : ZMod 441374291) ^ 70 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide

private theorem prime_twentyFourV_4491424785217 : Nat.Prime 4491424785217 := by
  apply lucas_primality 4491424785217 (7 : ZMod 4491424785217)
  · rw [← twentyFourVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 6), (3, 1), (53, 1), (441374291, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 6), (3, 1), (53, 1), (441374291, 1)] : List FactorBlock).map factorBlockValue).prod = 4491424785217 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyFourV_2
      · exact prime_twentyFourV_3
      · exact prime_twentyFourV_53
      · exact prime_twentyFourV_441374291
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 4491424785217) ^ 2245712392608 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (7 : ZMod 4491424785217) ^ 1497141595072 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (7 : ZMod 4491424785217) ^ 84743863872 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (7 : ZMod 4491424785217) ^ 10176 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide

private theorem prime_twentyFourV_702451380642795339781 : Nat.Prime 702451380642795339781 := by
  apply lucas_primality 702451380642795339781 (2 : ZMod 702451380642795339781)
  · rw [← twentyFourVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (5, 1), (7, 1), (372377, 1), (4491424785217, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (5, 1), (7, 1), (372377, 1), (4491424785217, 1)] : List FactorBlock).map factorBlockValue).prod = 702451380642795339781 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyFourV_2
      · exact prime_twentyFourV_3
      · exact prime_twentyFourV_5
      · exact prime_twentyFourV_7
      · exact prime_twentyFourV_372377
      · exact prime_twentyFourV_4491424785217
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 702451380642795339781) ^ 351225690321397669890 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (2 : ZMod 702451380642795339781) ^ 234150460214265113260 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (2 : ZMod 702451380642795339781) ^ 140490276128559067956 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (2 : ZMod 702451380642795339781) ^ 100350197234685048540 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (2 : ZMod 702451380642795339781) ^ 1886398409791140 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (2 : ZMod 702451380642795339781) ^ 156398340 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide

private theorem prime_twentyFourV_247262885986263959602913 : Nat.Prime 247262885986263959602913 := by
  apply lucas_primality 247262885986263959602913 (3 : ZMod 247262885986263959602913)
  · rw [← twentyFourVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 5), (11, 1), (702451380642795339781, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 5), (11, 1), (702451380642795339781, 1)] : List FactorBlock).map factorBlockValue).prod = 247262885986263959602913 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twentyFourV_2
      · exact prime_twentyFourV_11
      · exact prime_twentyFourV_702451380642795339781
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 247262885986263959602913) ^ 123631442993131979801456 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (3 : ZMod 247262885986263959602913) ^ 22478444180569450872992 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (3 : ZMod 247262885986263959602913) ^ 352 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide

private theorem prime_twentyFourV_157 : Nat.Prime 157 := by norm_num
private theorem prime_twentyFourV_4315799 : Nat.Prime 4315799 := by norm_num
private theorem prime_twentyFourV_7041049 : Nat.Prime 7041049 := by norm_num
private theorem prime_twentyFourV_569 : Nat.Prime 569 := by norm_num
private theorem prime_twentyFourV_25331881 : Nat.Prime 25331881 := by
  apply lucas_primality 25331881 (17 : ZMod 25331881)
  · rw [← twentyFourVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (3, 1), (5, 1), (7, 1), (53, 1), (569, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (3, 1), (5, 1), (7, 1), (53, 1), (569, 1)] : List FactorBlock).map factorBlockValue).prod = 25331881 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyFourV_2
      · exact prime_twentyFourV_3
      · exact prime_twentyFourV_5
      · exact prime_twentyFourV_7
      · exact prime_twentyFourV_53
      · exact prime_twentyFourV_569
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (17 : ZMod 25331881) ^ 12665940 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (17 : ZMod 25331881) ^ 8443960 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (17 : ZMod 25331881) ^ 5066376 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (17 : ZMod 25331881) ^ 3618840 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (17 : ZMod 25331881) ^ 477960 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (17 : ZMod 25331881) ^ 44520 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide

private theorem prime_twentyFourV_10892708831 : Nat.Prime 10892708831 := by
  apply lucas_primality 10892708831 (7 : ZMod 10892708831)
  · rw [← twentyFourVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 1), (43, 1), (25331881, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 1), (43, 1), (25331881, 1)] : List FactorBlock).map factorBlockValue).prod = 10892708831 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyFourV_2
      · exact prime_twentyFourV_5
      · exact prime_twentyFourV_43
      · exact prime_twentyFourV_25331881
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 10892708831) ^ 5446354415 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (7 : ZMod 10892708831) ^ 2178541766 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (7 : ZMod 10892708831) ^ 253318810 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (7 : ZMod 10892708831) ^ 430 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide

private theorem prime_twentyFourV_1982473007243 : Nat.Prime 1982473007243 := by
  apply lucas_primality 1982473007243 (2 : ZMod 1982473007243)
  · rw [← twentyFourVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (7, 1), (13, 1), (10892708831, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (7, 1), (13, 1), (10892708831, 1)] : List FactorBlock).map factorBlockValue).prod = 1982473007243 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyFourV_2
      · exact prime_twentyFourV_7
      · exact prime_twentyFourV_13
      · exact prime_twentyFourV_10892708831
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1982473007243) ^ 991236503621 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (2 : ZMod 1982473007243) ^ 283210429606 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (2 : ZMod 1982473007243) ^ 152497923634 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (2 : ZMod 1982473007243) ^ 182 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide

private theorem prime_twentyFourV_115903 : Nat.Prime 115903 := by norm_num
private theorem prime_twentyFourV_9833 : Nat.Prime 9833 := by norm_num
private theorem prime_twentyFourV_32244294937 : Nat.Prime 32244294937 := by
  apply lucas_primality 32244294937 (10 : ZMod 32244294937)
  · rw [← twentyFourVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (3, 1), (7, 1), (131, 1), (149, 1), (9833, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (3, 1), (7, 1), (131, 1), (149, 1), (9833, 1)] : List FactorBlock).map factorBlockValue).prod = 32244294937 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyFourV_2
      · exact prime_twentyFourV_3
      · exact prime_twentyFourV_7
      · exact prime_twentyFourV_131
      · exact prime_twentyFourV_149
      · exact prime_twentyFourV_9833
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 32244294937) ^ 16122147468 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (10 : ZMod 32244294937) ^ 10748098312 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (10 : ZMod 32244294937) ^ 4606327848 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (10 : ZMod 32244294937) ^ 246139656 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (10 : ZMod 32244294937) ^ 216404664 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (10 : ZMod 32244294937) ^ 3279192 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide

private theorem prime_twentyFourV_457 : Nat.Prime 457 := by norm_num
private theorem prime_twentyFourV_1433 : Nat.Prime 1433 := by norm_num
private theorem prime_twentyFourV_8783 : Nat.Prime 8783 := by norm_num
private theorem prime_twentyFourV_1898100541591 : Nat.Prime 1898100541591 := by
  apply lucas_primality 1898100541591 (3 : ZMod 1898100541591)
  · rw [← twentyFourVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (5, 1), (11, 1), (457, 1), (1433, 1), (8783, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (5, 1), (11, 1), (457, 1), (1433, 1), (8783, 1)] : List FactorBlock).map factorBlockValue).prod = 1898100541591 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyFourV_2
      · exact prime_twentyFourV_3
      · exact prime_twentyFourV_5
      · exact prime_twentyFourV_11
      · exact prime_twentyFourV_457
      · exact prime_twentyFourV_1433
      · exact prime_twentyFourV_8783
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1898100541591) ^ 949050270795 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (3 : ZMod 1898100541591) ^ 632700180530 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (3 : ZMod 1898100541591) ^ 379620108318 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (3 : ZMod 1898100541591) ^ 172554594690 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (3 : ZMod 1898100541591) ^ 4153392870 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (3 : ZMod 1898100541591) ^ 1324564230 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (3 : ZMod 1898100541591) ^ 216110730 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide

private theorem prime_twentyFourV_4951 : Nat.Prime 4951 := by norm_num
private theorem prime_twentyFourV_228023 : Nat.Prime 228023 := by norm_num
private theorem prime_twentyFourV_1805911 : Nat.Prime 1805911 := by norm_num
private theorem prime_twentyFourV_67 : Nat.Prime 67 := by norm_num
private theorem prime_twentyFourV_877 : Nat.Prime 877 := by norm_num
private theorem prime_twentyFourV_971 : Nat.Prime 971 := by norm_num
private theorem prime_twentyFourV_16089506899 : Nat.Prime 16089506899 := by
  apply lucas_primality 16089506899 (7 : ZMod 16089506899)
  · rw [← twentyFourVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (47, 1), (67, 1), (877, 1), (971, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (47, 1), (67, 1), (877, 1), (971, 1)] : List FactorBlock).map factorBlockValue).prod = 16089506899 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyFourV_2
      · exact prime_twentyFourV_3
      · exact prime_twentyFourV_47
      · exact prime_twentyFourV_67
      · exact prime_twentyFourV_877
      · exact prime_twentyFourV_971
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 16089506899) ^ 8044753449 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (7 : ZMod 16089506899) ^ 5363168966 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (7 : ZMod 16089506899) ^ 342329934 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (7 : ZMod 16089506899) ^ 240141894 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (7 : ZMod 16089506899) ^ 18346074 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (7 : ZMod 16089506899) ^ 16570038 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide

private theorem prime_twentyFourV_401 : Nat.Prime 401 := by norm_num
private theorem prime_twentyFourV_11069 : Nat.Prime 11069 := by norm_num
private theorem prime_twentyFourV_53269 : Nat.Prime 53269 := by norm_num
private theorem prime_twentyFourV_384973 : Nat.Prime 384973 := by norm_num
private theorem prime_twentyFourV_1901 : Nat.Prime 1901 := by norm_num
private theorem prime_twentyFourV_18979 : Nat.Prime 18979 := by norm_num
private theorem prime_twentyFourV_72158159 : Nat.Prime 72158159 := by
  apply lucas_primality 72158159 (13 : ZMod 72158159)
  · rw [← twentyFourVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (1901, 1), (18979, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (1901, 1), (18979, 1)] : List FactorBlock).map factorBlockValue).prod = 72158159 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twentyFourV_2
      · exact prime_twentyFourV_1901
      · exact prime_twentyFourV_18979
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (13 : ZMod 72158159) ^ 36079079 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (13 : ZMod 72158159) ^ 37958 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (13 : ZMod 72158159) ^ 3802 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide

private theorem prime_twentyFourV_20000838920189041 : Nat.Prime 20000838920189041 := by
  apply lucas_primality 20000838920189041 (7 : ZMod 20000838920189041)
  · rw [← twentyFourVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 4), (3, 2), (5, 1), (384973, 1), (72158159, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 4), (3, 2), (5, 1), (384973, 1), (72158159, 1)] : List FactorBlock).map factorBlockValue).prod = 20000838920189041 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyFourV_2
      · exact prime_twentyFourV_3
      · exact prime_twentyFourV_5
      · exact prime_twentyFourV_384973
      · exact prime_twentyFourV_72158159
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 20000838920189041) ^ 10000419460094520 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (7 : ZMod 20000838920189041) ^ 6666946306729680 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (7 : ZMod 20000838920189041) ^ 4000167784037808 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (7 : ZMod 20000838920189041) ^ 51953874480 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (7 : ZMod 20000838920189041) ^ 277180560 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide

private theorem prime_twentyFourV_9067 : Nat.Prime 9067 := by norm_num
private theorem prime_twentyFourV_32143 : Nat.Prime 32143 := by norm_num
private theorem prime_twentyFourV_3542327 : Nat.Prime 3542327 := by norm_num
private theorem prime_twentyFourV_20551 : Nat.Prime 20551 := by norm_num
private theorem prime_twentyFourV_319489 : Nat.Prime 319489 := by norm_num
private theorem prime_twentyFourV_3926359426523 : Nat.Prime 3926359426523 := by
  apply lucas_primality 3926359426523 (2 : ZMod 3926359426523)
  · rw [← twentyFourVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (13, 1), (23, 1), (20551, 1), (319489, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (13, 1), (23, 1), (20551, 1), (319489, 1)] : List FactorBlock).map factorBlockValue).prod = 3926359426523 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyFourV_2
      · exact prime_twentyFourV_13
      · exact prime_twentyFourV_23
      · exact prime_twentyFourV_20551
      · exact prime_twentyFourV_319489
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 3926359426523) ^ 1963179713261 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (2 : ZMod 3926359426523) ^ 302027648194 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (2 : ZMod 3926359426523) ^ 170711279414 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (2 : ZMod 3926359426523) ^ 191054422 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (2 : ZMod 3926359426523) ^ 12289498 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide

private theorem prime_twentyFourV_114593 : Nat.Prime 114593 := by norm_num
private theorem prime_twentyFourV_42857783 : Nat.Prime 42857783 := by
  apply lucas_primality 42857783 (5 : ZMod 42857783)
  · rw [← twentyFourVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (11, 1), (17, 1), (114593, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (11, 1), (17, 1), (114593, 1)] : List FactorBlock).map factorBlockValue).prod = 42857783 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyFourV_2
      · exact prime_twentyFourV_11
      · exact prime_twentyFourV_17
      · exact prime_twentyFourV_114593
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 42857783) ^ 21428891 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (5 : ZMod 42857783) ^ 3896162 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (5 : ZMod 42857783) ^ 2521046 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (5 : ZMod 42857783) ^ 374 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide

private theorem prime_twentyFourV_30429025931 : Nat.Prime 30429025931 := by
  apply lucas_primality 30429025931 (2 : ZMod 30429025931)
  · rw [← twentyFourVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 1), (71, 1), (42857783, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 1), (71, 1), (42857783, 1)] : List FactorBlock).map factorBlockValue).prod = 30429025931 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyFourV_2
      · exact prime_twentyFourV_5
      · exact prime_twentyFourV_71
      · exact prime_twentyFourV_42857783
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 30429025931) ^ 15214512965 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (2 : ZMod 30429025931) ^ 6085805186 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (2 : ZMod 30429025931) ^ 428577830 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (2 : ZMod 30429025931) ^ 710 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide

private theorem prime_twentyFourV_81047 : Nat.Prime 81047 := by norm_num
private theorem prime_twentyFourV_14999741 : Nat.Prime 14999741 := by norm_num
private theorem prime_twentyFourV_11655978276633277 : Nat.Prime 11655978276633277 := by
  apply lucas_primality 11655978276633277 (2 : ZMod 11655978276633277)
  · rw [← twentyFourVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (17, 1), (47, 1), (81047, 1), (14999741, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (17, 1), (47, 1), (81047, 1), (14999741, 1)] : List FactorBlock).map factorBlockValue).prod = 11655978276633277 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyFourV_2
      · exact prime_twentyFourV_3
      · exact prime_twentyFourV_17
      · exact prime_twentyFourV_47
      · exact prime_twentyFourV_81047
      · exact prime_twentyFourV_14999741
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 11655978276633277) ^ 5827989138316638 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (2 : ZMod 11655978276633277) ^ 3885326092211092 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (2 : ZMod 11655978276633277) ^ 685645780978428 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (2 : ZMod 11655978276633277) ^ 247999537800708 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (2 : ZMod 11655978276633277) ^ 143817516708 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (2 : ZMod 11655978276633277) ^ 777078636 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide

private theorem prime_twentyFourV_116559782766332771 : Nat.Prime 116559782766332771 := by
  apply lucas_primality 116559782766332771 (2 : ZMod 116559782766332771)
  · rw [← twentyFourVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 1), (11655978276633277, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 1), (11655978276633277, 1)] : List FactorBlock).map factorBlockValue).prod = 116559782766332771 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twentyFourV_2
      · exact prime_twentyFourV_5
      · exact prime_twentyFourV_11655978276633277
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 116559782766332771) ^ 58279891383166385 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (2 : ZMod 116559782766332771) ^ 23311956553266554 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (2 : ZMod 116559782766332771) ^ 10 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide

private theorem prime_twentyFourV_503 : Nat.Prime 503 := by norm_num
private theorem prime_twentyFourV_28183 : Nat.Prime 28183 := by norm_num
private theorem prime_twentyFourV_15040590709 : Nat.Prime 15040590709 := by
  apply lucas_primality 15040590709 (14 : ZMod 15040590709)
  · rw [← twentyFourVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (11, 1), (13, 1), (311, 1), (28183, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (11, 1), (13, 1), (311, 1), (28183, 1)] : List FactorBlock).map factorBlockValue).prod = 15040590709 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyFourV_2
      · exact prime_twentyFourV_3
      · exact prime_twentyFourV_11
      · exact prime_twentyFourV_13
      · exact prime_twentyFourV_311
      · exact prime_twentyFourV_28183
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (14 : ZMod 15040590709) ^ 7520295354 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (14 : ZMod 15040590709) ^ 5013530236 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (14 : ZMod 15040590709) ^ 1367326428 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (14 : ZMod 15040590709) ^ 1156968516 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (14 : ZMod 15040590709) ^ 48362028 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (14 : ZMod 15040590709) ^ 533676 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide

private theorem prime_twentyFourV_4787 : Nat.Prime 4787 := by norm_num
private theorem prime_twentyFourV_8839 : Nat.Prime 8839 := by norm_num
private theorem prime_twentyFourV_4924417 : Nat.Prime 4924417 := by norm_num
private theorem prime_twentyFourV_416726749916363 : Nat.Prime 416726749916363 := by
  apply lucas_primality 416726749916363 (2 : ZMod 416726749916363)
  · rw [← twentyFourVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (4787, 1), (8839, 1), (4924417, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (4787, 1), (8839, 1), (4924417, 1)] : List FactorBlock).map factorBlockValue).prod = 416726749916363 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyFourV_2
      · exact prime_twentyFourV_4787
      · exact prime_twentyFourV_8839
      · exact prime_twentyFourV_4924417
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 416726749916363) ^ 208363374958181 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (2 : ZMod 416726749916363) ^ 87053843726 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (2 : ZMod 416726749916363) ^ 47146368358 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (2 : ZMod 416726749916363) ^ 84624586 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide

private theorem prime_twentyFourV_277 : Nat.Prime 277 := by norm_num
private theorem prime_twentyFourV_1965553 : Nat.Prime 1965553 := by norm_num
private theorem prime_twentyFourV_66828803 : Nat.Prime 66828803 := by
  apply lucas_primality 66828803 (2 : ZMod 66828803)
  · rw [← twentyFourVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (17, 1), (1965553, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (17, 1), (1965553, 1)] : List FactorBlock).map factorBlockValue).prod = 66828803 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twentyFourV_2
      · exact prime_twentyFourV_17
      · exact prime_twentyFourV_1965553
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 66828803) ^ 33414401 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (2 : ZMod 66828803) ^ 3931106 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (2 : ZMod 66828803) ^ 34 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide

private theorem prime_twentyFourV_111069470587 : Nat.Prime 111069470587 := by
  apply lucas_primality 111069470587 (11 : ZMod 111069470587)
  · rw [← twentyFourVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (277, 1), (66828803, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (277, 1), (66828803, 1)] : List FactorBlock).map factorBlockValue).prod = 111069470587 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyFourV_2
      · exact prime_twentyFourV_3
      · exact prime_twentyFourV_277
      · exact prime_twentyFourV_66828803
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 111069470587) ^ 55534735293 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (11 : ZMod 111069470587) ^ 37023156862 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (11 : ZMod 111069470587) ^ 400972818 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (11 : ZMod 111069470587) ^ 1662 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide

private theorem prime_twentyFourV_6442029294047 : Nat.Prime 6442029294047 := by
  apply lucas_primality 6442029294047 (5 : ZMod 6442029294047)
  · rw [← twentyFourVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (29, 1), (111069470587, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (29, 1), (111069470587, 1)] : List FactorBlock).map factorBlockValue).prod = 6442029294047 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twentyFourV_2
      · exact prime_twentyFourV_29
      · exact prime_twentyFourV_111069470587
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 6442029294047) ^ 3221014647023 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (5 : ZMod 6442029294047) ^ 222138941174 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (5 : ZMod 6442029294047) ^ 58 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide

private theorem prime_twentyFourV_14081 : Nat.Prime 14081 := by norm_num
private theorem prime_twentyFourV_4603 : Nat.Prime 4603 := by norm_num
private theorem prime_twentyFourV_8369 : Nat.Prime 8369 := by norm_num
private theorem prime_twentyFourV_539315099 : Nat.Prime 539315099 := by
  apply lucas_primality 539315099 (2 : ZMod 539315099)
  · rw [← twentyFourVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (7, 1), (4603, 1), (8369, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (7, 1), (4603, 1), (8369, 1)] : List FactorBlock).map factorBlockValue).prod = 539315099 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyFourV_2
      · exact prime_twentyFourV_7
      · exact prime_twentyFourV_4603
      · exact prime_twentyFourV_8369
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 539315099) ^ 269657549 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (2 : ZMod 539315099) ^ 77045014 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (2 : ZMod 539315099) ^ 117166 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (2 : ZMod 539315099) ^ 64442 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide

private theorem prime_twentyFourV_440457562723103 : Nat.Prime 440457562723103 := by
  apply lucas_primality 440457562723103 (5 : ZMod 440457562723103)
  · rw [← twentyFourVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (29, 1), (14081, 1), (539315099, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (29, 1), (14081, 1), (539315099, 1)] : List FactorBlock).map factorBlockValue).prod = 440457562723103 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyFourV_2
      · exact prime_twentyFourV_29
      · exact prime_twentyFourV_14081
      · exact prime_twentyFourV_539315099
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 440457562723103) ^ 220228781361551 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (5 : ZMod 440457562723103) ^ 15188191818038 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (5 : ZMod 440457562723103) ^ 31280275742 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (5 : ZMod 440457562723103) ^ 816698 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide

private theorem prime_twentyFourV_113 : Nat.Prime 113 := by norm_num
private theorem prime_twentyFourV_637519 : Nat.Prime 637519 := by norm_num
private theorem prime_twentyFourV_670673 : Nat.Prime 670673 := by norm_num
private theorem prime_twentyFourV_239 : Nat.Prime 239 := by norm_num
private theorem prime_twentyFourV_131367307 : Nat.Prime 131367307 := by
  apply lucas_primality 131367307 (3 : ZMod 131367307)
  · rw [← twentyFourVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (7, 1), (23, 1), (239, 1), (569, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (7, 1), (23, 1), (239, 1), (569, 1)] : List FactorBlock).map factorBlockValue).prod = 131367307 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyFourV_2
      · exact prime_twentyFourV_3
      · exact prime_twentyFourV_7
      · exact prime_twentyFourV_23
      · exact prime_twentyFourV_239
      · exact prime_twentyFourV_569
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 131367307) ^ 65683653 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (3 : ZMod 131367307) ^ 43789102 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (3 : ZMod 131367307) ^ 18766758 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (3 : ZMod 131367307) ^ 5711622 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (3 : ZMod 131367307) ^ 549654 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (3 : ZMod 131367307) ^ 230874 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide

private theorem prime_twentyFourV_53388987237871 : Nat.Prime 53388987237871 := by
  apply lucas_primality 53388987237871 (15 : ZMod 53388987237871)
  · rw [← twentyFourVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (5, 1), (19, 1), (23, 1), (31, 1), (131367307, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (5, 1), (19, 1), (23, 1), (31, 1), (131367307, 1)] : List FactorBlock).map factorBlockValue).prod = 53388987237871 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyFourV_2
      · exact prime_twentyFourV_3
      · exact prime_twentyFourV_5
      · exact prime_twentyFourV_19
      · exact prime_twentyFourV_23
      · exact prime_twentyFourV_31
      · exact prime_twentyFourV_131367307
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (15 : ZMod 53388987237871) ^ 26694493618935 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (15 : ZMod 53388987237871) ^ 17796329079290 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (15 : ZMod 53388987237871) ^ 10677797447574 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (15 : ZMod 53388987237871) ^ 2809946696730 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (15 : ZMod 53388987237871) ^ 2321260314690 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (15 : ZMod 53388987237871) ^ 1722225394770 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (15 : ZMod 53388987237871) ^ 406410 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide

private theorem prime_twentyFourV_210193 : Nat.Prime 210193 := by norm_num
private theorem prime_twentyFourV_439 : Nat.Prime 439 := by norm_num
private theorem prime_twentyFourV_853 : Nat.Prime 853 := by norm_num
private theorem prime_twentyFourV_151 : Nat.Prime 151 := by norm_num
private theorem prime_twentyFourV_479 : Nat.Prime 479 := by norm_num
private theorem prime_twentyFourV_6343 : Nat.Prime 6343 := by norm_num
private theorem prime_twentyFourV_44960719007 : Nat.Prime 44960719007 := by
  apply lucas_primality 44960719007 (5 : ZMod 44960719007)
  · rw [← twentyFourVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (7, 2), (151, 1), (479, 1), (6343, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (7, 2), (151, 1), (479, 1), (6343, 1)] : List FactorBlock).map factorBlockValue).prod = 44960719007 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyFourV_2
      · exact prime_twentyFourV_7
      · exact prime_twentyFourV_151
      · exact prime_twentyFourV_479
      · exact prime_twentyFourV_6343
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 44960719007) ^ 22480359503 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (5 : ZMod 44960719007) ^ 6422959858 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (5 : ZMod 44960719007) ^ 297753106 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (5 : ZMod 44960719007) ^ 93863714 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (5 : ZMod 44960719007) ^ 7088242 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide

private theorem prime_twentyFourV_1348821570211 : Nat.Prime 1348821570211 := by
  apply lucas_primality 1348821570211 (2 : ZMod 1348821570211)
  · rw [← twentyFourVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (5, 1), (44960719007, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (5, 1), (44960719007, 1)] : List FactorBlock).map factorBlockValue).prod = 1348821570211 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyFourV_2
      · exact prime_twentyFourV_3
      · exact prime_twentyFourV_5
      · exact prime_twentyFourV_44960719007
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1348821570211) ^ 674410785105 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (2 : ZMod 1348821570211) ^ 449607190070 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (2 : ZMod 1348821570211) ^ 269764314042 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (2 : ZMod 1348821570211) ^ 30 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide

private theorem prime_twentyFourV_8081426670915240593 : Nat.Prime 8081426670915240593 := by
  apply lucas_primality 8081426670915240593 (3 : ZMod 8081426670915240593)
  · rw [← twentyFourVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 4), (439, 1), (853, 1), (1348821570211, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 4), (439, 1), (853, 1), (1348821570211, 1)] : List FactorBlock).map factorBlockValue).prod = 8081426670915240593 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyFourV_2
      · exact prime_twentyFourV_439
      · exact prime_twentyFourV_853
      · exact prime_twentyFourV_1348821570211
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 8081426670915240593) ^ 4040713335457620296 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (3 : ZMod 8081426670915240593) ^ 18408716790239728 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (3 : ZMod 8081426670915240593) ^ 9474122709162064 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (3 : ZMod 8081426670915240593) ^ 5991472 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide

private theorem prime_twentyFourV_11249345925914014905457 : Nat.Prime 11249345925914014905457 := by
  apply lucas_primality 11249345925914014905457 (5 : ZMod 11249345925914014905457)
  · rw [← twentyFourVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 4), (3, 1), (29, 1), (8081426670915240593, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 4), (3, 1), (29, 1), (8081426670915240593, 1)] : List FactorBlock).map factorBlockValue).prod = 11249345925914014905457 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyFourV_2
      · exact prime_twentyFourV_3
      · exact prime_twentyFourV_29
      · exact prime_twentyFourV_8081426670915240593
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 11249345925914014905457) ^ 5624672962957007452728 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (5 : ZMod 11249345925914014905457) ^ 3749781975304671635152 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (5 : ZMod 11249345925914014905457) ^ 387908480203931548464 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (5 : ZMod 11249345925914014905457) ^ 1392 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide

private theorem prime_twentyFourV_175141 : Nat.Prime 175141 := by norm_num
private theorem prime_twentyFourV_183439 : Nat.Prime 183439 := by norm_num
private theorem prime_twentyFourV_1934663 : Nat.Prime 1934663 := by norm_num
private theorem prime_twentyFourV_13093 : Nat.Prime 13093 := by norm_num
private theorem prime_twentyFourV_51577 : Nat.Prime 51577 := by norm_num
private theorem prime_twentyFourV_35115478373 : Nat.Prime 35115478373 := by
  apply lucas_primality 35115478373 (3 : ZMod 35115478373)
  · rw [← twentyFourVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (13, 1), (13093, 1), (51577, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (13, 1), (13093, 1), (51577, 1)] : List FactorBlock).map factorBlockValue).prod = 35115478373 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyFourV_2
      · exact prime_twentyFourV_13
      · exact prime_twentyFourV_13093
      · exact prime_twentyFourV_51577
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 35115478373) ^ 17557739186 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (3 : ZMod 35115478373) ^ 2701190644 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (3 : ZMod 35115478373) ^ 2682004 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (3 : ZMod 35115478373) ^ 680836 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide

private theorem prime_twentyFourV_8596663 : Nat.Prime 8596663 := by norm_num
private theorem prime_twentyFourV_12269 : Nat.Prime 12269 := by norm_num
private theorem prime_twentyFourV_20538307 : Nat.Prime 20538307 := by
  apply lucas_primality 20538307 (2 : ZMod 20538307)
  · rw [← twentyFourVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 3), (31, 1), (12269, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 3), (31, 1), (12269, 1)] : List FactorBlock).map factorBlockValue).prod = 20538307 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyFourV_2
      · exact prime_twentyFourV_3
      · exact prime_twentyFourV_31
      · exact prime_twentyFourV_12269
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 20538307) ^ 10269153 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (2 : ZMod 20538307) ^ 6846102 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (2 : ZMod 20538307) ^ 662526 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (2 : ZMod 20538307) ^ 1674 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide

private theorem prime_twentyFourV_409 : Nat.Prime 409 := by norm_num
private theorem prime_twentyFourV_827 : Nat.Prime 827 := by norm_num
private theorem prime_twentyFourV_219857951 : Nat.Prime 219857951 := by
  apply lucas_primality 219857951 (17 : ZMod 219857951)
  · rw [← twentyFourVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 2), (13, 1), (409, 1), (827, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 2), (13, 1), (409, 1), (827, 1)] : List FactorBlock).map factorBlockValue).prod = 219857951 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyFourV_2
      · exact prime_twentyFourV_5
      · exact prime_twentyFourV_13
      · exact prime_twentyFourV_409
      · exact prime_twentyFourV_827
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (17 : ZMod 219857951) ^ 109928975 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (17 : ZMod 219857951) ^ 43971590 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (17 : ZMod 219857951) ^ 16912150 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (17 : ZMod 219857951) ^ 537550 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (17 : ZMod 219857951) ^ 265850 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide

private theorem prime_twentyFourV_85243 : Nat.Prime 85243 := by norm_num
private theorem prime_twentyFourV_18480383 : Nat.Prime 18480383 := by norm_num
private theorem prime_twentyFourV_775189 : Nat.Prime 775189 := by norm_num
private theorem prime_twentyFourV_23255671 : Nat.Prime 23255671 := by
  apply lucas_primality 23255671 (6 : ZMod 23255671)
  · rw [← twentyFourVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (5, 1), (775189, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (5, 1), (775189, 1)] : List FactorBlock).map factorBlockValue).prod = 23255671 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyFourV_2
      · exact prime_twentyFourV_3
      · exact prime_twentyFourV_5
      · exact prime_twentyFourV_775189
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 23255671) ^ 11627835 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (6 : ZMod 23255671) ^ 7751890 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (6 : ZMod 23255671) ^ 4651134 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (6 : ZMod 23255671) ^ 30 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide

private theorem prime_twentyFourV_50821 : Nat.Prime 50821 := by norm_num
private theorem prime_twentyFourV_25817069 : Nat.Prime 25817069 := by
  apply lucas_primality 25817069 (2 : ZMod 25817069)
  · rw [← twentyFourVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (127, 1), (50821, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (127, 1), (50821, 1)] : List FactorBlock).map factorBlockValue).prod = 25817069 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twentyFourV_2
      · exact prime_twentyFourV_127
      · exact prime_twentyFourV_50821
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 25817069) ^ 12908534 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (2 : ZMod 25817069) ^ 203284 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (2 : ZMod 25817069) ^ 508 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide

private theorem prime_twentyFourV_51634139 : Nat.Prime 51634139 := by
  apply lucas_primality 51634139 (2 : ZMod 51634139)
  · rw [← twentyFourVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (25817069, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (25817069, 1)] : List FactorBlock).map factorBlockValue).prod = 51634139 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_twentyFourV_2
      · exact prime_twentyFourV_25817069
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 51634139) ^ 25817069 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (2 : ZMod 51634139) ^ 2 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide

private theorem prime_twentyFourV_8233 : Nat.Prime 8233 := by norm_num
private theorem prime_twentyFourV_93811 : Nat.Prime 93811 := by norm_num
private theorem prime_twentyFourV_8274073 : Nat.Prime 8274073 := by norm_num
private theorem prime_twentyFourV_1429 : Nat.Prime 1429 := by norm_num
private theorem prime_twentyFourV_217223 : Nat.Prime 217223 := by norm_num
private theorem prime_twentyFourV_277508030299 : Nat.Prime 277508030299 := by
  apply lucas_primality 277508030299 (3 : ZMod 277508030299)
  · rw [← twentyFourVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (149, 1), (1429, 1), (217223, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (149, 1), (1429, 1), (217223, 1)] : List FactorBlock).map factorBlockValue).prod = 277508030299 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyFourV_2
      · exact prime_twentyFourV_3
      · exact prime_twentyFourV_149
      · exact prime_twentyFourV_1429
      · exact prime_twentyFourV_217223
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 277508030299) ^ 138754015149 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (3 : ZMod 277508030299) ^ 92502676766 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (3 : ZMod 277508030299) ^ 1862470002 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (3 : ZMod 277508030299) ^ 194197362 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (3 : ZMod 277508030299) ^ 1277526 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide

private theorem prime_twentyFourV_163 : Nat.Prime 163 := by norm_num
private theorem prime_twentyFourV_257 : Nat.Prime 257 := by norm_num
private theorem prime_twentyFourV_1705633957 : Nat.Prime 1705633957 := by
  apply lucas_primality 1705633957 (5 : ZMod 1705633957)
  · rw [← twentyFourVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 3), (13, 1), (29, 1), (163, 1), (257, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 3), (13, 1), (29, 1), (163, 1), (257, 1)] : List FactorBlock).map factorBlockValue).prod = 1705633957 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyFourV_2
      · exact prime_twentyFourV_3
      · exact prime_twentyFourV_13
      · exact prime_twentyFourV_29
      · exact prime_twentyFourV_163
      · exact prime_twentyFourV_257
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 1705633957) ^ 852816978 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (5 : ZMod 1705633957) ^ 568544652 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (5 : ZMod 1705633957) ^ 131202612 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (5 : ZMod 1705633957) ^ 58814964 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (5 : ZMod 1705633957) ^ 10464012 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (5 : ZMod 1705633957) ^ 6636708 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide

private theorem prime_twentyFourV_21247 : Nat.Prime 21247 := by norm_num
private theorem prime_twentyFourV_3427799 : Nat.Prime 3427799 := by norm_num
private theorem prime_twentyFourV_1131173671 : Nat.Prime 1131173671 := by
  apply lucas_primality 1131173671 (3 : ZMod 1131173671)
  · rw [← twentyFourVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (5, 1), (11, 1), (3427799, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (5, 1), (11, 1), (3427799, 1)] : List FactorBlock).map factorBlockValue).prod = 1131173671 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyFourV_2
      · exact prime_twentyFourV_3
      · exact prime_twentyFourV_5
      · exact prime_twentyFourV_11
      · exact prime_twentyFourV_3427799
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1131173671) ^ 565586835 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (3 : ZMod 1131173671) ^ 377057890 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (3 : ZMod 1131173671) ^ 226234734 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (3 : ZMod 1131173671) ^ 102833970 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (3 : ZMod 1131173671) ^ 330 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide

private theorem prime_twentyFourV_978570257152699693 : Nat.Prime 978570257152699693 := by
  apply lucas_primality 978570257152699693 (5 : ZMod 978570257152699693)
  · rw [← twentyFourVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 3), (13, 1), (29, 1), (21247, 1), (1131173671, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 3), (13, 1), (29, 1), (21247, 1), (1131173671, 1)] : List FactorBlock).map factorBlockValue).prod = 978570257152699693 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyFourV_2
      · exact prime_twentyFourV_3
      · exact prime_twentyFourV_13
      · exact prime_twentyFourV_29
      · exact prime_twentyFourV_21247
      · exact prime_twentyFourV_1131173671
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 978570257152699693) ^ 489285128576349846 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (5 : ZMod 978570257152699693) ^ 326190085717566564 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (5 : ZMod 978570257152699693) ^ 75274635165592284 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (5 : ZMod 978570257152699693) ^ 33743801970782748 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (5 : ZMod 978570257152699693) ^ 46056867188436 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (5 : ZMod 978570257152699693) ^ 865092852 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide

private theorem prime_twentyFourV_1576355845470429690015148801 : Nat.Prime 1576355845470429690015148801 := by
  apply lucas_primality 1576355845470429690015148801 (101 : ZMod 1576355845470429690015148801)
  · rw [← twentyFourVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 8), (3, 2), (5, 2), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 8), (3, 2), (5, 2), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod = 1576355845470429690015148801 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyFourV_2
      · exact prime_twentyFourV_3
      · exact prime_twentyFourV_5
      · exact prime_twentyFourV_7
      · exact prime_twentyFourV_11
      · exact prime_twentyFourV_13
      · exact prime_twentyFourV_17
      · exact prime_twentyFourV_19
      · exact prime_twentyFourV_23
      · exact prime_twentyFourV_29
      · exact prime_twentyFourV_31
      · exact prime_twentyFourV_37
      · exact prime_twentyFourV_41
      · exact prime_twentyFourV_43
      · exact prime_twentyFourV_47
      · exact prime_twentyFourV_53
      · exact prime_twentyFourV_59
      · exact prime_twentyFourV_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (101 : ZMod 1576355845470429690015148801) ^ 788177922735214845007574400 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (101 : ZMod 1576355845470429690015148801) ^ 525451948490143230005049600 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (101 : ZMod 1576355845470429690015148801) ^ 315271169094085938003029760 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (101 : ZMod 1576355845470429690015148801) ^ 225193692210061384287878400 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (101 : ZMod 1576355845470429690015148801) ^ 143305076860948153637740800 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (101 : ZMod 1576355845470429690015148801) ^ 121258141959263822308857600 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (101 : ZMod 1576355845470429690015148801) ^ 92726814439437040589126400 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (101 : ZMod 1576355845470429690015148801) ^ 82966097130022615263955200 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (101 : ZMod 1576355845470429690015148801) ^ 68537210672627377826745600 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (101 : ZMod 1576355845470429690015148801) ^ 54357098119669989310867200 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (101 : ZMod 1576355845470429690015148801) ^ 50850188563562248065004800 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (101 : ZMod 1576355845470429690015148801) ^ 42604212039741342973382400 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (101 : ZMod 1576355845470429690015148801) ^ 38447703548059260732076800 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (101 : ZMod 1576355845470429690015148801) ^ 36659438266754178837561600 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (101 : ZMod 1576355845470429690015148801) ^ 33539486073838929574790400 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (101 : ZMod 1576355845470429690015148801) ^ 29742563122083579056889600 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (101 : ZMod 1576355845470429690015148801) ^ 26717895685939486271443200 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (101 : ZMod 1576355845470429690015148801) ^ 25841899106072617869100800 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide

private theorem prime_twentyFourV_1979 : Nat.Prime 1979 := by norm_num
private theorem prime_twentyFourV_17581 : Nat.Prime 17581 := by norm_num
private theorem prime_twentyFourV_2183231 : Nat.Prime 2183231 := by norm_num
private theorem prime_twentyFourV_2131 : Nat.Prime 2131 := by norm_num
private theorem prime_twentyFourV_2897 : Nat.Prime 2897 := by norm_num
private theorem prime_twentyFourV_9939346271 : Nat.Prime 9939346271 := by
  apply lucas_primality 9939346271 (14 : ZMod 9939346271)
  · rw [← twentyFourVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 1), (7, 1), (23, 1), (2131, 1), (2897, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 1), (7, 1), (23, 1), (2131, 1), (2897, 1)] : List FactorBlock).map factorBlockValue).prod = 9939346271 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyFourV_2
      · exact prime_twentyFourV_5
      · exact prime_twentyFourV_7
      · exact prime_twentyFourV_23
      · exact prime_twentyFourV_2131
      · exact prime_twentyFourV_2897
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (14 : ZMod 9939346271) ^ 4969673135 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (14 : ZMod 9939346271) ^ 1987869254 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (14 : ZMod 9939346271) ^ 1419906610 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (14 : ZMod 9939346271) ^ 432145490 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (14 : ZMod 9939346271) ^ 4664170 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (14 : ZMod 9939346271) ^ 3430910 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide

private theorem prime_twentyFourV_754618367023955065564019 : Nat.Prime 754618367023955065564019 := by
  apply lucas_primality 754618367023955065564019 (2 : ZMod 754618367023955065564019)
  · rw [← twentyFourVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (23, 1), (43, 1), (17581, 1), (2183231, 1), (9939346271, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (23, 1), (43, 1), (17581, 1), (2183231, 1), (9939346271, 1)] : List FactorBlock).map factorBlockValue).prod = 754618367023955065564019 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyFourV_2
      · exact prime_twentyFourV_23
      · exact prime_twentyFourV_43
      · exact prime_twentyFourV_17581
      · exact prime_twentyFourV_2183231
      · exact prime_twentyFourV_9939346271
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 754618367023955065564019) ^ 377309183511977532782009 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (2 : ZMod 754618367023955065564019) ^ 32809494218432828937566 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (2 : ZMod 754618367023955065564019) ^ 17549264349394303850326 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (2 : ZMod 754618367023955065564019) ^ 42922380241394406778 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (2 : ZMod 754618367023955065564019) ^ 345642933351512078 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (2 : ZMod 754618367023955065564019) ^ 75922333969358 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide

private theorem prime_twentyFourV_1049 : Nat.Prime 1049 := by norm_num
private theorem prime_twentyFourV_139537 : Nat.Prime 139537 := by norm_num
private theorem prime_twentyFourV_5879 : Nat.Prime 5879 := by norm_num
private theorem prime_twentyFourV_175593973 : Nat.Prime 175593973 := by
  apply lucas_primality 175593973 (5 : ZMod 175593973)
  · rw [← twentyFourVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (19, 1), (131, 1), (5879, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (19, 1), (131, 1), (5879, 1)] : List FactorBlock).map factorBlockValue).prod = 175593973 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyFourV_2
      · exact prime_twentyFourV_3
      · exact prime_twentyFourV_19
      · exact prime_twentyFourV_131
      · exact prime_twentyFourV_5879
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 175593973) ^ 87796986 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (5 : ZMod 175593973) ^ 58531324 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (5 : ZMod 175593973) ^ 9241788 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (5 : ZMod 175593973) ^ 1340412 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (5 : ZMod 175593973) ^ 29868 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide

private theorem prime_twentyFourV_372958561 : Nat.Prime 372958561 := by
  apply lucas_primality 372958561 (11 : ZMod 372958561)
  · rw [← twentyFourVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 5), (3, 3), (5, 1), (13, 1), (29, 1), (229, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 5), (3, 3), (5, 1), (13, 1), (29, 1), (229, 1)] : List FactorBlock).map factorBlockValue).prod = 372958561 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyFourV_2
      · exact prime_twentyFourV_3
      · exact prime_twentyFourV_5
      · exact prime_twentyFourV_13
      · exact prime_twentyFourV_29
      · exact prime_twentyFourV_229
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 372958561) ^ 186479280 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (11 : ZMod 372958561) ^ 124319520 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (11 : ZMod 372958561) ^ 74591712 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (11 : ZMod 372958561) ^ 28689120 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (11 : ZMod 372958561) ^ 12860640 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (11 : ZMod 372958561) ^ 1628640 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide

private theorem prime_twentyFourV_55197867029 : Nat.Prime 55197867029 := by
  apply lucas_primality 55197867029 (2 : ZMod 55197867029)
  · rw [← twentyFourVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (37, 1), (372958561, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (37, 1), (372958561, 1)] : List FactorBlock).map factorBlockValue).prod = 55197867029 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twentyFourV_2
      · exact prime_twentyFourV_37
      · exact prime_twentyFourV_372958561
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 55197867029) ^ 27598933514 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (2 : ZMod 55197867029) ^ 1491834244 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (2 : ZMod 55197867029) ^ 148 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide

private theorem prime_twentyFourV_79 : Nat.Prime 79 := by norm_num
private theorem prime_twentyFourV_101 : Nat.Prime 101 := by norm_num
private theorem prime_twentyFourV_2521 : Nat.Prime 2521 := by norm_num
private theorem prime_twentyFourV_3253 : Nat.Prime 3253 := by norm_num
private theorem prime_twentyFourV_1656564227 : Nat.Prime 1656564227 := by
  apply lucas_primality 1656564227 (2 : ZMod 1656564227)
  · rw [← twentyFourVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (101, 1), (2521, 1), (3253, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (101, 1), (2521, 1), (3253, 1)] : List FactorBlock).map factorBlockValue).prod = 1656564227 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyFourV_2
      · exact prime_twentyFourV_101
      · exact prime_twentyFourV_2521
      · exact prime_twentyFourV_3253
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1656564227) ^ 828282113 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (2 : ZMod 1656564227) ^ 16401626 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (2 : ZMod 1656564227) ^ 657106 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (2 : ZMod 1656564227) ^ 509242 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide

private theorem prime_twentyFourV_1272241326337 : Nat.Prime 1272241326337 := by
  apply lucas_primality 1272241326337 (5 : ZMod 1272241326337)
  · rw [← twentyFourVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 8), (3, 1), (1656564227, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 8), (3, 1), (1656564227, 1)] : List FactorBlock).map factorBlockValue).prod = 1272241326337 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twentyFourV_2
      · exact prime_twentyFourV_3
      · exact prime_twentyFourV_1656564227
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 1272241326337) ^ 636120663168 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (5 : ZMod 1272241326337) ^ 424080442112 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (5 : ZMod 1272241326337) ^ 768 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide

private theorem prime_twentyFourV_293 : Nat.Prime 293 := by norm_num
private theorem prime_twentyFourV_7549 : Nat.Prime 7549 := by norm_num
private theorem prime_twentyFourV_18089 : Nat.Prime 18089 := by norm_num
private theorem prime_twentyFourV_7647016217 : Nat.Prime 7647016217 := by
  apply lucas_primality 7647016217 (3 : ZMod 7647016217)
  · rw [← twentyFourVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (7, 1), (7549, 1), (18089, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (7, 1), (7549, 1), (18089, 1)] : List FactorBlock).map factorBlockValue).prod = 7647016217 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyFourV_2
      · exact prime_twentyFourV_7
      · exact prime_twentyFourV_7549
      · exact prime_twentyFourV_18089
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 7647016217) ^ 3823508108 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (3 : ZMod 7647016217) ^ 1092430888 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (3 : ZMod 7647016217) ^ 1012984 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (3 : ZMod 7647016217) ^ 422744 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide

private theorem prime_twentyFourV_13443454509487 : Nat.Prime 13443454509487 := by
  apply lucas_primality 13443454509487 (3 : ZMod 13443454509487)
  · rw [← twentyFourVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (293, 1), (7647016217, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (293, 1), (7647016217, 1)] : List FactorBlock).map factorBlockValue).prod = 13443454509487 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyFourV_2
      · exact prime_twentyFourV_3
      · exact prime_twentyFourV_293
      · exact prime_twentyFourV_7647016217
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 13443454509487) ^ 6721727254743 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (3 : ZMod 13443454509487) ^ 4481151503162 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (3 : ZMod 13443454509487) ^ 45882097302 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (3 : ZMod 13443454509487) ^ 1758 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide

private theorem prime_twentyFourV_137251 : Nat.Prime 137251 := by norm_num
private theorem prime_twentyFourV_1976731 : Nat.Prime 1976731 := by norm_num
private theorem prime_twentyFourV_2112239 : Nat.Prime 2112239 := by norm_num
private theorem prime_twentyFourV_9396985754191469517451 : Nat.Prime 9396985754191469517451 := by
  apply lucas_primality 9396985754191469517451 (2 : ZMod 9396985754191469517451)
  · rw [← twentyFourVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 2), (5, 2), (61, 1), (163, 1), (503, 1), (1976731, 1), (2112239, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 2), (5, 2), (61, 1), (163, 1), (503, 1), (1976731, 1), (2112239, 1)] : List FactorBlock).map factorBlockValue).prod = 9396985754191469517451 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyFourV_2
      · exact prime_twentyFourV_3
      · exact prime_twentyFourV_5
      · exact prime_twentyFourV_61
      · exact prime_twentyFourV_163
      · exact prime_twentyFourV_503
      · exact prime_twentyFourV_1976731
      · exact prime_twentyFourV_2112239
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 9396985754191469517451) ^ 4698492877095734758725 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (2 : ZMod 9396985754191469517451) ^ 3132328584730489839150 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (2 : ZMod 9396985754191469517451) ^ 1879397150838293903490 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (2 : ZMod 9396985754191469517451) ^ 154048946790024090450 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (2 : ZMod 9396985754191469517451) ^ 57650219350867911150 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (2 : ZMod 9396985754191469517451) ^ 18681880227020814150 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (2 : ZMod 9396985754191469517451) ^ 4753800974533950 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (2 : ZMod 9396985754191469517451) ^ 4448826933974550 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide

private theorem prime_twentyFourV_14489 : Nat.Prime 14489 := by norm_num
private theorem prime_twentyFourV_527381 : Nat.Prime 527381 := by norm_num
private theorem prime_twentyFourV_587 : Nat.Prime 587 := by norm_num
private theorem prime_twentyFourV_7704943 : Nat.Prime 7704943 := by norm_num
private theorem prime_twentyFourV_263805968283449 : Nat.Prime 263805968283449 := by
  apply lucas_primality 263805968283449 (3 : ZMod 263805968283449)
  · rw [← twentyFourVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (23, 1), (317, 1), (587, 1), (7704943, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (23, 1), (317, 1), (587, 1), (7704943, 1)] : List FactorBlock).map factorBlockValue).prod = 263805968283449 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyFourV_2
      · exact prime_twentyFourV_23
      · exact prime_twentyFourV_317
      · exact prime_twentyFourV_587
      · exact prime_twentyFourV_7704943
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 263805968283449) ^ 131902984141724 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (3 : ZMod 263805968283449) ^ 11469824707976 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (3 : ZMod 263805968283449) ^ 832195483544 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (3 : ZMod 263805968283449) ^ 449413915304 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (3 : ZMod 263805968283449) ^ 34238536 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide

private theorem prime_twentyFourV_161449252589470789 : Nat.Prime 161449252589470789 := by
  apply lucas_primality 161449252589470789 (7 : ZMod 161449252589470789)
  · rw [← twentyFourVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 2), (17, 1), (263805968283449, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 2), (17, 1), (263805968283449, 1)] : List FactorBlock).map factorBlockValue).prod = 161449252589470789 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyFourV_2
      · exact prime_twentyFourV_3
      · exact prime_twentyFourV_17
      · exact prime_twentyFourV_263805968283449
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 161449252589470789) ^ 80724626294735394 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (7 : ZMod 161449252589470789) ^ 53816417529823596 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (7 : ZMod 161449252589470789) ^ 9497014858204164 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (7 : ZMod 161449252589470789) ^ 612 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide

private theorem prime_twentyFourV_5009 : Nat.Prime 5009 := by norm_num
private theorem prime_twentyFourV_107 : Nat.Prime 107 := by norm_num
private theorem prime_twentyFourV_61717 : Nat.Prime 61717 := by norm_num
private theorem prime_twentyFourV_35279 : Nat.Prime 35279 := by norm_num
private theorem prime_twentyFourV_7190123 : Nat.Prime 7190123 := by norm_num
private theorem prime_twentyFourV_1521962095903 : Nat.Prime 1521962095903 := by
  apply lucas_primality 1521962095903 (3 : ZMod 1521962095903)
  · rw [← twentyFourVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (35279, 1), (7190123, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (35279, 1), (7190123, 1)] : List FactorBlock).map factorBlockValue).prod = 1521962095903 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyFourV_2
      · exact prime_twentyFourV_3
      · exact prime_twentyFourV_35279
      · exact prime_twentyFourV_7190123
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1521962095903) ^ 760981047951 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (3 : ZMod 1521962095903) ^ 507320698634 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (3 : ZMod 1521962095903) ^ 43140738 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (3 : ZMod 1521962095903) ^ 211674 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide

private theorem prime_twentyFourV_563585608037072707 : Nat.Prime 563585608037072707 := by
  apply lucas_primality 563585608037072707 (3 : ZMod 563585608037072707)
  · rw [← twentyFourVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (61717, 1), (1521962095903, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (61717, 1), (1521962095903, 1)] : List FactorBlock).map factorBlockValue).prod = 563585608037072707 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyFourV_2
      · exact prime_twentyFourV_3
      · exact prime_twentyFourV_61717
      · exact prime_twentyFourV_1521962095903
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 563585608037072707) ^ 281792804018536353 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (3 : ZMod 563585608037072707) ^ 187861869345690902 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (3 : ZMod 563585608037072707) ^ 9131772575418 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (3 : ZMod 563585608037072707) ^ 370302 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide

private theorem prime_twentyFourV_2291539082278737626663 : Nat.Prime 2291539082278737626663 := by
  apply lucas_primality 2291539082278737626663 (10 : ZMod 2291539082278737626663)
  · rw [← twentyFourVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (19, 1), (107, 1), (563585608037072707, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (19, 1), (107, 1), (563585608037072707, 1)] : List FactorBlock).map factorBlockValue).prod = 2291539082278737626663 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyFourV_2
      · exact prime_twentyFourV_19
      · exact prime_twentyFourV_107
      · exact prime_twentyFourV_563585608037072707
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (10 : ZMod 2291539082278737626663) ^ 1145769541139368813331 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (10 : ZMod 2291539082278737626663) ^ 120607320119933559298 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (10 : ZMod 2291539082278737626663) ^ 21416253105408762866 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (10 : ZMod 2291539082278737626663) ^ 4066 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide

private theorem prime_twentyFourV_172093 : Nat.Prime 172093 := by norm_num
private theorem prime_twentyFourV_313 : Nat.Prime 313 := by norm_num
private theorem prime_twentyFourV_487 : Nat.Prime 487 := by norm_num
private theorem prime_twentyFourV_39511 : Nat.Prime 39511 := by norm_num
private theorem prime_twentyFourV_2270447 : Nat.Prime 2270447 := by norm_num
private theorem prime_twentyFourV_1802764560956033 : Nat.Prime 1802764560956033 := by
  apply lucas_primality 1802764560956033 (3 : ZMod 1802764560956033)
  · rw [← twentyFourVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 7), (157, 1), (39511, 1), (2270447, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 7), (157, 1), (39511, 1), (2270447, 1)] : List FactorBlock).map factorBlockValue).prod = 1802764560956033 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyFourV_2
      · exact prime_twentyFourV_157
      · exact prime_twentyFourV_39511
      · exact prime_twentyFourV_2270447
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1802764560956033) ^ 901382280478016 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (3 : ZMod 1802764560956033) ^ 11482576821376 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (3 : ZMod 1802764560956033) ^ 45626902912 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (3 : ZMod 1802764560956033) ^ 794013056 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide

private theorem prime_twentyFourV_1755892682371176143 : Nat.Prime 1755892682371176143 := by
  apply lucas_primality 1755892682371176143 (7 : ZMod 1755892682371176143)
  · rw [← twentyFourVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (487, 1), (1802764560956033, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (487, 1), (1802764560956033, 1)] : List FactorBlock).map factorBlockValue).prod = 1755892682371176143 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twentyFourV_2
      · exact prime_twentyFourV_487
      · exact prime_twentyFourV_1802764560956033
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 1755892682371176143) ^ 877946341185588071 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (7 : ZMod 1755892682371176143) ^ 3605529121912066 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (7 : ZMod 1755892682371176143) ^ 974 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide

private theorem prime_twentyFourV_6595132914986137593109 : Nat.Prime 6595132914986137593109 := by
  apply lucas_primality 6595132914986137593109 (2 : ZMod 6595132914986137593109)
  · rw [← twentyFourVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (313, 1), (1755892682371176143, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (313, 1), (1755892682371176143, 1)] : List FactorBlock).map factorBlockValue).prod = 6595132914986137593109 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyFourV_2
      · exact prime_twentyFourV_3
      · exact prime_twentyFourV_313
      · exact prime_twentyFourV_1755892682371176143
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 6595132914986137593109) ^ 3297566457493068796554 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (2 : ZMod 6595132914986137593109) ^ 2198377638328712531036 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (2 : ZMod 6595132914986137593109) ^ 21070712188454113716 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (2 : ZMod 6595132914986137593109) ^ 3756 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide

private theorem prime_twentyFourV_431 : Nat.Prime 431 := by norm_num
private theorem prime_twentyFourV_11719 : Nat.Prime 11719 := by norm_num
private theorem prime_twentyFourV_1228273 : Nat.Prime 1228273 := by norm_num
private theorem prime_twentyFourV_9574219 : Nat.Prime 9574219 := by norm_num
private theorem prime_twentyFourV_18373307 : Nat.Prime 18373307 := by norm_num
private theorem prime_twentyFourV_227 : Nat.Prime 227 := by norm_num
private theorem prime_twentyFourV_509 : Nat.Prime 509 := by norm_num
private theorem prime_twentyFourV_106363 : Nat.Prime 106363 := by norm_num
private theorem prime_twentyFourV_6701 : Nat.Prime 6701 := by norm_num
private theorem prime_twentyFourV_23959559521 : Nat.Prime 23959559521 := by
  apply lucas_primality 23959559521 (11 : ZMod 23959559521)
  · rw [← twentyFourVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 5), (3, 2), (5, 1), (13, 1), (191, 1), (6701, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 5), (3, 2), (5, 1), (13, 1), (191, 1), (6701, 1)] : List FactorBlock).map factorBlockValue).prod = 23959559521 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyFourV_2
      · exact prime_twentyFourV_3
      · exact prime_twentyFourV_5
      · exact prime_twentyFourV_13
      · exact prime_twentyFourV_191
      · exact prime_twentyFourV_6701
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 23959559521) ^ 11979779760 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (11 : ZMod 23959559521) ^ 7986519840 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (11 : ZMod 23959559521) ^ 4791911904 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (11 : ZMod 23959559521) ^ 1843043040 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (11 : ZMod 23959559521) ^ 125442720 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (11 : ZMod 23959559521) ^ 3575520 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide

private theorem prime_twentyFourV_85512338798115589 : Nat.Prime 85512338798115589 := by
  apply lucas_primality 85512338798115589 (6 : ZMod 85512338798115589)
  · rw [← twentyFourVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (59, 1), (71, 2), (23959559521, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (59, 1), (71, 2), (23959559521, 1)] : List FactorBlock).map factorBlockValue).prod = 85512338798115589 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyFourV_2
      · exact prime_twentyFourV_3
      · exact prime_twentyFourV_59
      · exact prime_twentyFourV_71
      · exact prime_twentyFourV_23959559521
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 85512338798115589) ^ 42756169399057794 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (6 : ZMod 85512338798115589) ^ 28504112932705196 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (6 : ZMod 85512338798115589) ^ 1449361674544332 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (6 : ZMod 85512338798115589) ^ 1204399138001628 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (6 : ZMod 85512338798115589) ^ 3569028 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide

private theorem prime_twentyFourV_331 : Nat.Prime 331 := by norm_num
private theorem prime_twentyFourV_7129 : Nat.Prime 7129 := by norm_num
private theorem prime_twentyFourV_199 : Nat.Prime 199 := by norm_num
private theorem prime_twentyFourV_5449 : Nat.Prime 5449 := by norm_num
private theorem prime_twentyFourV_8089 : Nat.Prime 8089 := by norm_num
private theorem prime_twentyFourV_4121269 : Nat.Prime 4121269 := by norm_num
private theorem prime_twentyFourV_123638071 : Nat.Prime 123638071 := by
  apply lucas_primality 123638071 (7 : ZMod 123638071)
  · rw [← twentyFourVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (5, 1), (4121269, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (5, 1), (4121269, 1)] : List FactorBlock).map factorBlockValue).prod = 123638071 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyFourV_2
      · exact prime_twentyFourV_3
      · exact prime_twentyFourV_5
      · exact prime_twentyFourV_4121269
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 123638071) ^ 61819035 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (7 : ZMod 123638071) ^ 41212690 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (7 : ZMod 123638071) ^ 24727614 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (7 : ZMod 123638071) ^ 30 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide

private theorem prime_twentyFourV_741828427 : Nat.Prime 741828427 := by
  apply lucas_primality 741828427 (2 : ZMod 741828427)
  · rw [← twentyFourVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (123638071, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (123638071, 1)] : List FactorBlock).map factorBlockValue).prod = 741828427 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twentyFourV_2
      · exact prime_twentyFourV_3
      · exact prime_twentyFourV_123638071
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 741828427) ^ 370914213 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (2 : ZMod 741828427) ^ 247276142 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (2 : ZMod 741828427) ^ 6 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide

private theorem prime_twentyFourV_429449525106920937499 : Nat.Prime 429449525106920937499 := by
  apply lucas_primality 429449525106920937499 (2 : ZMod 429449525106920937499)
  · rw [← twentyFourVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (11, 1), (199, 1), (5449, 1), (8089, 1), (741828427, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (11, 1), (199, 1), (5449, 1), (8089, 1), (741828427, 1)] : List FactorBlock).map factorBlockValue).prod = 429449525106920937499 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyFourV_2
      · exact prime_twentyFourV_3
      · exact prime_twentyFourV_11
      · exact prime_twentyFourV_199
      · exact prime_twentyFourV_5449
      · exact prime_twentyFourV_8089
      · exact prime_twentyFourV_741828427
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 429449525106920937499) ^ 214724762553460468749 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (2 : ZMod 429449525106920937499) ^ 143149841702306979166 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (2 : ZMod 429449525106920937499) ^ 39040865918810994318 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (2 : ZMod 429449525106920937499) ^ 2158037814607642902 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (2 : ZMod 429449525106920937499) ^ 78812539017603402 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (2 : ZMod 429449525106920937499) ^ 53090558178627882 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (2 : ZMod 429449525106920937499) ^ 578906805774 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide

private theorem prime_twentyFourV_1069 : Nat.Prime 1069 := by norm_num
private theorem prime_twentyFourV_34591 : Nat.Prime 34591 := by norm_num
private theorem prime_twentyFourV_1856137 : Nat.Prime 1856137 := by norm_num
private theorem prime_twentyFourV_2137 : Nat.Prime 2137 := by norm_num
private theorem prime_twentyFourV_315103 : Nat.Prime 315103 := by norm_num
private theorem prime_twentyFourV_6733751111 : Nat.Prime 6733751111 := by
  apply lucas_primality 6733751111 (19 : ZMod 6733751111)
  · rw [← twentyFourVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 1), (2137, 1), (315103, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 1), (2137, 1), (315103, 1)] : List FactorBlock).map factorBlockValue).prod = 6733751111 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyFourV_2
      · exact prime_twentyFourV_5
      · exact prime_twentyFourV_2137
      · exact prime_twentyFourV_315103
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (19 : ZMod 6733751111) ^ 3366875555 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (19 : ZMod 6733751111) ^ 1346750222 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (19 : ZMod 6733751111) ^ 3151030 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (19 : ZMod 6733751111) ^ 21370 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide

private theorem prime_twentyFourV_1013 : Nat.Prime 1013 := by norm_num
private theorem prime_twentyFourV_7220867 : Nat.Prime 7220867 := by norm_num
private theorem prime_twentyFourV_144417341 : Nat.Prime 144417341 := by
  apply lucas_primality 144417341 (2 : ZMod 144417341)
  · rw [← twentyFourVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (5, 1), (7220867, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (5, 1), (7220867, 1)] : List FactorBlock).map factorBlockValue).prod = 144417341 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twentyFourV_2
      · exact prime_twentyFourV_5
      · exact prime_twentyFourV_7220867
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 144417341) ^ 72208670 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (2 : ZMod 144417341) ^ 28883468 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (2 : ZMod 144417341) ^ 20 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide

private theorem prime_twentyFourV_89 : Nat.Prime 89 := by norm_num
private theorem prime_twentyFourV_277100209 : Nat.Prime 277100209 := by
  apply lucas_primality 277100209 (17 : ZMod 277100209)
  · rw [← twentyFourVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 4), (3, 2), (7, 1), (11, 1), (67, 1), (373, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 4), (3, 2), (7, 1), (11, 1), (67, 1), (373, 1)] : List FactorBlock).map factorBlockValue).prod = 277100209 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyFourV_2
      · exact prime_twentyFourV_3
      · exact prime_twentyFourV_7
      · exact prime_twentyFourV_11
      · exact prime_twentyFourV_67
      · exact prime_twentyFourV_373
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (17 : ZMod 277100209) ^ 138550104 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (17 : ZMod 277100209) ^ 92366736 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (17 : ZMod 277100209) ^ 39585744 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (17 : ZMod 277100209) ^ 25190928 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (17 : ZMod 277100209) ^ 4135824 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (17 : ZMod 277100209) ^ 742896 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide

private theorem prime_twentyFourV_60421700572451 : Nat.Prime 60421700572451 := by
  apply lucas_primality 60421700572451 (2 : ZMod 60421700572451)
  · rw [← twentyFourVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 2), (7, 2), (89, 1), (277100209, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 2), (7, 2), (89, 1), (277100209, 1)] : List FactorBlock).map factorBlockValue).prod = 60421700572451 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyFourV_2
      · exact prime_twentyFourV_5
      · exact prime_twentyFourV_7
      · exact prime_twentyFourV_89
      · exact prime_twentyFourV_277100209
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 60421700572451) ^ 30210850286225 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (2 : ZMod 60421700572451) ^ 12084340114490 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (2 : ZMod 60421700572451) ^ 8631671510350 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (2 : ZMod 60421700572451) ^ 678895512050 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (2 : ZMod 60421700572451) ^ 218050 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide

private theorem prime_twentyFourV_53173 : Nat.Prime 53173 := by norm_num
private theorem prime_twentyFourV_82763 : Nat.Prime 82763 := by norm_num
private theorem prime_twentyFourV_12444181 : Nat.Prime 12444181 := by norm_num
private theorem prime_twentyFourV_13799 : Nat.Prime 13799 := by norm_num
private theorem prime_twentyFourV_14771 : Nat.Prime 14771 := by norm_num
private theorem prime_twentyFourV_16713652379 : Nat.Prime 16713652379 := by
  apply lucas_primality 16713652379 (2 : ZMod 16713652379)
  · rw [← twentyFourVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (41, 1), (13799, 1), (14771, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (41, 1), (13799, 1), (14771, 1)] : List FactorBlock).map factorBlockValue).prod = 16713652379 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyFourV_2
      · exact prime_twentyFourV_41
      · exact prime_twentyFourV_13799
      · exact prime_twentyFourV_14771
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 16713652379) ^ 8356826189 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (2 : ZMod 16713652379) ^ 407650058 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (2 : ZMod 16713652379) ^ 1211222 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (2 : ZMod 16713652379) ^ 1131518 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide

private theorem prime_twentyFourV_769 : Nat.Prime 769 := by norm_num
private theorem prime_twentyFourV_2143 : Nat.Prime 2143 := by norm_num
private theorem prime_twentyFourV_8597 : Nat.Prime 8597 := by norm_num
private theorem prime_twentyFourV_9792301 : Nat.Prime 9792301 := by norm_num
private theorem prime_twentyFourV_223 : Nat.Prime 223 := by norm_num
private theorem prime_twentyFourV_161017 : Nat.Prime 161017 := by norm_num
private theorem prime_twentyFourV_6391408799 : Nat.Prime 6391408799 := by
  apply lucas_primality 6391408799 (23 : ZMod 6391408799)
  · rw [← twentyFourVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (89, 1), (223, 1), (161017, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (89, 1), (223, 1), (161017, 1)] : List FactorBlock).map factorBlockValue).prod = 6391408799 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyFourV_2
      · exact prime_twentyFourV_89
      · exact prime_twentyFourV_223
      · exact prime_twentyFourV_161017
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (23 : ZMod 6391408799) ^ 3195704399 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (23 : ZMod 6391408799) ^ 71813582 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (23 : ZMod 6391408799) ^ 28661026 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (23 : ZMod 6391408799) ^ 39694 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide

private theorem prime_twentyFourV_85313 : Nat.Prime 85313 := by norm_num
private theorem prime_twentyFourV_102593 : Nat.Prime 102593 := by norm_num
private theorem prime_twentyFourV_219959393 : Nat.Prime 219959393 := by
  apply lucas_primality 219959393 (3 : ZMod 219959393)
  · rw [← twentyFourVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 5), (67, 1), (102593, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 5), (67, 1), (102593, 1)] : List FactorBlock).map factorBlockValue).prod = 219959393 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twentyFourV_2
      · exact prime_twentyFourV_67
      · exact prime_twentyFourV_102593
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 219959393) ^ 109979696 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (3 : ZMod 219959393) ^ 3282976 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (3 : ZMod 219959393) ^ 2144 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide

private theorem prime_twentyFourV_595201 : Nat.Prime 595201 := by norm_num
private theorem prime_twentyFourV_289267687 : Nat.Prime 289267687 := by
  apply lucas_primality 289267687 (5 : ZMod 289267687)
  · rw [← twentyFourVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 5), (595201, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 5), (595201, 1)] : List FactorBlock).map factorBlockValue).prod = 289267687 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twentyFourV_2
      · exact prime_twentyFourV_3
      · exact prime_twentyFourV_595201
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 289267687) ^ 144633843 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (5 : ZMod 289267687) ^ 96422562 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (5 : ZMod 289267687) ^ 486 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide

private theorem prime_twentyFourV_159097227851 : Nat.Prime 159097227851 := by
  apply lucas_primality 159097227851 (6 : ZMod 159097227851)
  · rw [← twentyFourVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 2), (11, 1), (289267687, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 2), (11, 1), (289267687, 1)] : List FactorBlock).map factorBlockValue).prod = 159097227851 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyFourV_2
      · exact prime_twentyFourV_5
      · exact prime_twentyFourV_11
      · exact prime_twentyFourV_289267687
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 159097227851) ^ 79548613925 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (6 : ZMod 159097227851) ^ 31819445570 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (6 : ZMod 159097227851) ^ 14463384350 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (6 : ZMod 159097227851) ^ 550 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide

private theorem prime_twentyFourV_45820001621089 : Nat.Prime 45820001621089 := by
  apply lucas_primality 45820001621089 (13 : ZMod 45820001621089)
  · rw [← twentyFourVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 5), (3, 2), (159097227851, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 5), (3, 2), (159097227851, 1)] : List FactorBlock).map factorBlockValue).prod = 45820001621089 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twentyFourV_2
      · exact prime_twentyFourV_3
      · exact prime_twentyFourV_159097227851
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (13 : ZMod 45820001621089) ^ 22910000810544 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (13 : ZMod 45820001621089) ^ 15273333873696 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (13 : ZMod 45820001621089) ^ 288 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide

private theorem prime_twentyFourV_607 : Nat.Prime 607 := by norm_num
private theorem prime_twentyFourV_8526929 : Nat.Prime 8526929 := by norm_num
private theorem prime_twentyFourV_324023303 : Nat.Prime 324023303 := by
  apply lucas_primality 324023303 (5 : ZMod 324023303)
  · rw [← twentyFourVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (19, 1), (8526929, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (19, 1), (8526929, 1)] : List FactorBlock).map factorBlockValue).prod = 324023303 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twentyFourV_2
      · exact prime_twentyFourV_19
      · exact prime_twentyFourV_8526929
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 324023303) ^ 162011651 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (5 : ZMod 324023303) ^ 17053858 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (5 : ZMod 324023303) ^ 38 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide

private theorem prime_twentyFourV_4817 : Nat.Prime 4817 := by norm_num
private theorem prime_twentyFourV_1109 : Nat.Prime 1109 := by norm_num
private theorem prime_twentyFourV_710369951 : Nat.Prime 710369951 := by
  apply lucas_primality 710369951 (7 : ZMod 710369951)
  · rw [← twentyFourVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 2), (23, 1), (557, 1), (1109, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 2), (23, 1), (557, 1), (1109, 1)] : List FactorBlock).map factorBlockValue).prod = 710369951 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyFourV_2
      · exact prime_twentyFourV_5
      · exact prime_twentyFourV_23
      · exact prime_twentyFourV_557
      · exact prime_twentyFourV_1109
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 710369951) ^ 355184975 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (7 : ZMod 710369951) ^ 142073990 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (7 : ZMod 710369951) ^ 30885650 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (7 : ZMod 710369951) ^ 1275350 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (7 : ZMod 710369951) ^ 640550 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide

private theorem prime_twentyFourV_4243096546919081 : Nat.Prime 4243096546919081 := by
  apply lucas_primality 4243096546919081 (3 : ZMod 4243096546919081)
  · rw [← twentyFourVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (5, 1), (31, 1), (4817, 1), (710369951, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (5, 1), (31, 1), (4817, 1), (710369951, 1)] : List FactorBlock).map factorBlockValue).prod = 4243096546919081 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyFourV_2
      · exact prime_twentyFourV_5
      · exact prime_twentyFourV_31
      · exact prime_twentyFourV_4817
      · exact prime_twentyFourV_710369951
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 4243096546919081) ^ 2121548273459540 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (3 : ZMod 4243096546919081) ^ 848619309383816 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (3 : ZMod 4243096546919081) ^ 136874082158680 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (3 : ZMod 4243096546919081) ^ 880858739240 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (3 : ZMod 4243096546919081) ^ 5973080 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide

private theorem prime_twentyFourV_7703 : Nat.Prime 7703 := by norm_num
private theorem prime_twentyFourV_10800222241 : Nat.Prime 10800222241 := by
  apply lucas_primality 10800222241 (11 : ZMod 10800222241)
  · rw [← twentyFourVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 5), (3, 1), (5, 1), (23, 1), (127, 1), (7703, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 5), (3, 1), (5, 1), (23, 1), (127, 1), (7703, 1)] : List FactorBlock).map factorBlockValue).prod = 10800222241 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyFourV_2
      · exact prime_twentyFourV_3
      · exact prime_twentyFourV_5
      · exact prime_twentyFourV_23
      · exact prime_twentyFourV_127
      · exact prime_twentyFourV_7703
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 10800222241) ^ 5400111120 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (11 : ZMod 10800222241) ^ 3600074080 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (11 : ZMod 10800222241) ^ 2160044448 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (11 : ZMod 10800222241) ^ 469574880 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (11 : ZMod 10800222241) ^ 85041120 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (11 : ZMod 10800222241) ^ 1402080 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide

private theorem prime_twentyFourV_1814437336489 : Nat.Prime 1814437336489 := by
  apply lucas_primality 1814437336489 (11 : ZMod 1814437336489)
  · rw [← twentyFourVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (3, 1), (7, 1), (10800222241, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (3, 1), (7, 1), (10800222241, 1)] : List FactorBlock).map factorBlockValue).prod = 1814437336489 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyFourV_2
      · exact prime_twentyFourV_3
      · exact prime_twentyFourV_7
      · exact prime_twentyFourV_10800222241
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 1814437336489) ^ 907218668244 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (11 : ZMod 1814437336489) ^ 604812445496 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (11 : ZMod 1814437336489) ^ 259205333784 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (11 : ZMod 1814437336489) ^ 168 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide

private theorem prime_twentyFourV_139 : Nat.Prime 139 := by norm_num
private theorem prime_twentyFourV_13121 : Nat.Prime 13121 := by norm_num
private theorem prime_twentyFourV_1458229 : Nat.Prime 1458229 := by norm_num
private theorem prime_twentyFourV_446803687100569 : Nat.Prime 446803687100569 := by
  apply lucas_primality 446803687100569 (11 : ZMod 446803687100569)
  · rw [← twentyFourVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (3, 1), (7, 1), (139, 1), (13121, 1), (1458229, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (3, 1), (7, 1), (139, 1), (13121, 1), (1458229, 1)] : List FactorBlock).map factorBlockValue).prod = 446803687100569 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyFourV_2
      · exact prime_twentyFourV_3
      · exact prime_twentyFourV_7
      · exact prime_twentyFourV_139
      · exact prime_twentyFourV_13121
      · exact prime_twentyFourV_1458229
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 446803687100569) ^ 223401843550284 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (11 : ZMod 446803687100569) ^ 148934562366856 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (11 : ZMod 446803687100569) ^ 63829098157224 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (11 : ZMod 446803687100569) ^ 3214415015112 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (11 : ZMod 446803687100569) ^ 34052563608 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (11 : ZMod 446803687100569) ^ 306401592 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide

private theorem prime_twentyFourV_421 : Nat.Prime 421 := by norm_num
private theorem prime_twentyFourV_2072201 : Nat.Prime 2072201 := by norm_num
private theorem prime_twentyFourV_2567179 : Nat.Prime 2567179 := by norm_num
private theorem prime_twentyFourV_383 : Nat.Prime 383 := by norm_num
private theorem prime_twentyFourV_811 : Nat.Prime 811 := by norm_num
private theorem prime_twentyFourV_237308333 : Nat.Prime 237308333 := by
  apply lucas_primality 237308333 (2 : ZMod 237308333)
  · rw [← twentyFourVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (191, 1), (383, 1), (811, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (191, 1), (383, 1), (811, 1)] : List FactorBlock).map factorBlockValue).prod = 237308333 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyFourV_2
      · exact prime_twentyFourV_191
      · exact prime_twentyFourV_383
      · exact prime_twentyFourV_811
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 237308333) ^ 118654166 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (2 : ZMod 237308333) ^ 1242452 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (2 : ZMod 237308333) ^ 619604 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (2 : ZMod 237308333) ^ 292612 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide

private theorem prime_twentyFourV_4079 : Nat.Prime 4079 := by norm_num
private theorem prime_twentyFourV_992263 : Nat.Prime 992263 := by norm_num
private theorem prime_twentyFourV_222197 : Nat.Prime 222197 := by norm_num
private theorem prime_twentyFourV_276413069 : Nat.Prime 276413069 := by
  apply lucas_primality 276413069 (2 : ZMod 276413069)
  · rw [← twentyFourVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (311, 1), (222197, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (311, 1), (222197, 1)] : List FactorBlock).map factorBlockValue).prod = 276413069 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twentyFourV_2
      · exact prime_twentyFourV_311
      · exact prime_twentyFourV_222197
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 276413069) ^ 138206534 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (2 : ZMod 276413069) ^ 888788 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (2 : ZMod 276413069) ^ 1244 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide

private theorem prime_twentyFourV_176303 : Nat.Prime 176303 := by norm_num
private theorem prime_twentyFourV_57122173 : Nat.Prime 57122173 := by
  apply lucas_primality 57122173 (5 : ZMod 57122173)
  · rw [← twentyFourVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 4), (176303, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 4), (176303, 1)] : List FactorBlock).map factorBlockValue).prod = 57122173 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twentyFourV_2
      · exact prime_twentyFourV_3
      · exact prime_twentyFourV_176303
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 57122173) ^ 28561086 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (5 : ZMod 57122173) ^ 19040724 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (5 : ZMod 57122173) ^ 324 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide

private theorem prime_twentyFourV_685466077 : Nat.Prime 685466077 := by
  apply lucas_primality 685466077 (6 : ZMod 685466077)
  · rw [← twentyFourVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (57122173, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (57122173, 1)] : List FactorBlock).map factorBlockValue).prod = 685466077 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twentyFourV_2
      · exact prime_twentyFourV_3
      · exact prime_twentyFourV_57122173
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (6 : ZMod 685466077) ^ 342733038 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (6 : ZMod 685466077) ^ 228488692 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (6 : ZMod 685466077) ^ 12 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide

private theorem prime_twentyFourV_119737 : Nat.Prime 119737 := by norm_num
private theorem prime_twentyFourV_211 : Nat.Prime 211 := by norm_num
private theorem prime_twentyFourV_8573 : Nat.Prime 8573 := by norm_num
private theorem prime_twentyFourV_21706837 : Nat.Prime 21706837 := by
  apply lucas_primality 21706837 (2 : ZMod 21706837)
  · rw [← twentyFourVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (211, 1), (8573, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (211, 1), (8573, 1)] : List FactorBlock).map factorBlockValue).prod = 21706837 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyFourV_2
      · exact prime_twentyFourV_3
      · exact prime_twentyFourV_211
      · exact prime_twentyFourV_8573
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 21706837) ^ 10853418 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (2 : ZMod 21706837) ^ 7235612 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (2 : ZMod 21706837) ^ 102876 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (2 : ZMod 21706837) ^ 2532 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide

private theorem prime_twentyFourV_14467279 : Nat.Prime 14467279 := by norm_num
private theorem prime_twentyFourV_752298509 : Nat.Prime 752298509 := by
  apply lucas_primality 752298509 (2 : ZMod 752298509)
  · rw [← twentyFourVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (13, 1), (14467279, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (13, 1), (14467279, 1)] : List FactorBlock).map factorBlockValue).prod = 752298509 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twentyFourV_2
      · exact prime_twentyFourV_13
      · exact prime_twentyFourV_14467279
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 752298509) ^ 376149254 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (2 : ZMod 752298509) ^ 57869116 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (2 : ZMod 752298509) ^ 52 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide

private theorem prime_twentyFourV_307 : Nat.Prime 307 := by norm_num
private theorem prime_twentyFourV_2011 : Nat.Prime 2011 := by norm_num
private theorem prime_twentyFourV_4203707 : Nat.Prime 4203707 := by norm_num
private theorem prime_twentyFourV_100888969 : Nat.Prime 100888969 := by
  apply lucas_primality 100888969 (7 : ZMod 100888969)
  · rw [← twentyFourVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (3, 1), (4203707, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (3, 1), (4203707, 1)] : List FactorBlock).map factorBlockValue).prod = 100888969 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twentyFourV_2
      · exact prime_twentyFourV_3
      · exact prime_twentyFourV_4203707
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 100888969) ^ 50444484 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (7 : ZMod 100888969) ^ 33629656 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (7 : ZMod 100888969) ^ 24 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide

private theorem prime_twentyFourV_397 : Nat.Prime 397 := by norm_num
private theorem prime_twentyFourV_674701 : Nat.Prime 674701 := by norm_num
private theorem prime_twentyFourV_11680677399577 : Nat.Prime 11680677399577 := by
  apply lucas_primality 11680677399577 (5 : ZMod 11680677399577)
  · rw [← twentyFourVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (3, 1), (23, 1), (79, 1), (397, 1), (674701, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (3, 1), (23, 1), (79, 1), (397, 1), (674701, 1)] : List FactorBlock).map factorBlockValue).prod = 11680677399577 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyFourV_2
      · exact prime_twentyFourV_3
      · exact prime_twentyFourV_23
      · exact prime_twentyFourV_79
      · exact prime_twentyFourV_397
      · exact prime_twentyFourV_674701
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 11680677399577) ^ 5840338699788 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (5 : ZMod 11680677399577) ^ 3893559133192 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (5 : ZMod 11680677399577) ^ 507855539112 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (5 : ZMod 11680677399577) ^ 147856675944 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (5 : ZMod 11680677399577) ^ 29422361208 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (5 : ZMod 11680677399577) ^ 17312376 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide

private theorem prime_twentyFourV_281 : Nat.Prime 281 := by norm_num
private theorem prime_twentyFourV_739 : Nat.Prime 739 := by norm_num
private theorem prime_twentyFourV_8443 : Nat.Prime 8443 := by norm_num
private theorem prime_twentyFourV_84294913 : Nat.Prime 84294913 := by
  apply lucas_primality 84294913 (14 : ZMod 84294913)
  · rw [← twentyFourVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 8), (3, 1), (13, 1), (8443, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 8), (3, 1), (13, 1), (8443, 1)] : List FactorBlock).map factorBlockValue).prod = 84294913 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyFourV_2
      · exact prime_twentyFourV_3
      · exact prime_twentyFourV_13
      · exact prime_twentyFourV_8443
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (14 : ZMod 84294913) ^ 42147456 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (14 : ZMod 84294913) ^ 28098304 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (14 : ZMod 84294913) ^ 6484224 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (14 : ZMod 84294913) ^ 9984 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide

private theorem prime_twentyFourV_3540386347 : Nat.Prime 3540386347 := by
  apply lucas_primality 3540386347 (11 : ZMod 3540386347)
  · rw [← twentyFourVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (7, 1), (84294913, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (7, 1), (84294913, 1)] : List FactorBlock).map factorBlockValue).prod = 3540386347 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyFourV_2
      · exact prime_twentyFourV_3
      · exact prime_twentyFourV_7
      · exact prime_twentyFourV_84294913
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 3540386347) ^ 1770193173 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (11 : ZMod 3540386347) ^ 1180128782 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (11 : ZMod 3540386347) ^ 505769478 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (11 : ZMod 3540386347) ^ 42 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide

private theorem prime_twentyFourV_1509031 : Nat.Prime 1509031 := by norm_num
private theorem prime_twentyFourV_9277522589 : Nat.Prime 9277522589 := by
  apply lucas_primality 9277522589 (2 : ZMod 9277522589)
  · rw [← twentyFourVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (29, 1), (53, 1), (1509031, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (29, 1), (53, 1), (1509031, 1)] : List FactorBlock).map factorBlockValue).prod = 9277522589 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyFourV_2
      · exact prime_twentyFourV_29
      · exact prime_twentyFourV_53
      · exact prime_twentyFourV_1509031
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 9277522589) ^ 4638761294 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (2 : ZMod 9277522589) ^ 319914572 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (2 : ZMod 9277522589) ^ 175047596 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (2 : ZMod 9277522589) ^ 6148 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide

private theorem prime_twentyFourV_964862349257 : Nat.Prime 964862349257 := by
  apply lucas_primality 964862349257 (5 : ZMod 964862349257)
  · rw [← twentyFourVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (13, 1), (9277522589, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (13, 1), (9277522589, 1)] : List FactorBlock).map factorBlockValue).prod = 964862349257 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twentyFourV_2
      · exact prime_twentyFourV_13
      · exact prime_twentyFourV_9277522589
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 964862349257) ^ 482431174628 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (5 : ZMod 964862349257) ^ 74220180712 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (5 : ZMod 964862349257) ^ 104 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide

private theorem prime_twentyFourV_653273 : Nat.Prime 653273 := by norm_num
private theorem prime_twentyFourV_757 : Nat.Prime 757 := by norm_num
private theorem prime_twentyFourV_967 : Nat.Prime 967 := by norm_num
private theorem prime_twentyFourV_61627 : Nat.Prime 61627 := by norm_num
private theorem prime_twentyFourV_5841559 : Nat.Prime 5841559 := by norm_num
private theorem prime_twentyFourV_2159986538959 : Nat.Prime 2159986538959 := by
  apply lucas_primality 2159986538959 (6 : ZMod 2159986538959)
  · rw [← twentyFourVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (61627, 1), (5841559, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (61627, 1), (5841559, 1)] : List FactorBlock).map factorBlockValue).prod = 2159986538959 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyFourV_2
      · exact prime_twentyFourV_3
      · exact prime_twentyFourV_61627
      · exact prime_twentyFourV_5841559
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 2159986538959) ^ 1079993269479 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (6 : ZMod 2159986538959) ^ 719995512986 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (6 : ZMod 2159986538959) ^ 35049354 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (6 : ZMod 2159986538959) ^ 369762 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide

private theorem prime_twentyFourV_15811511862622282211 : Nat.Prime 15811511862622282211 := by
  apply lucas_primality 15811511862622282211 (2 : ZMod 15811511862622282211)
  · rw [← twentyFourVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 1), (757, 1), (967, 1), (2159986538959, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 1), (757, 1), (967, 1), (2159986538959, 1)] : List FactorBlock).map factorBlockValue).prod = 15811511862622282211 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyFourV_2
      · exact prime_twentyFourV_5
      · exact prime_twentyFourV_757
      · exact prime_twentyFourV_967
      · exact prime_twentyFourV_2159986538959
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 15811511862622282211) ^ 7905755931311141105 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (2 : ZMod 15811511862622282211) ^ 3162302372524456442 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (2 : ZMod 15811511862622282211) ^ 20887069831733530 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (2 : ZMod 15811511862622282211) ^ 16351098099919630 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (2 : ZMod 15811511862622282211) ^ 7320190 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide

private theorem prime_twentyFourV_1087 : Nat.Prime 1087 := by norm_num
private theorem prime_twentyFourV_3061 : Nat.Prime 3061 := by norm_num
private theorem prime_twentyFourV_61379 : Nat.Prime 61379 := by norm_num
private theorem prime_twentyFourV_382747 : Nat.Prime 382747 := by norm_num
private theorem prime_twentyFourV_163987 : Nat.Prime 163987 := by norm_num
private theorem prime_twentyFourV_1440461809 : Nat.Prime 1440461809 := by
  apply lucas_primality 1440461809 (7 : ZMod 1440461809)
  · rw [← twentyFourVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 4), (3, 2), (61, 1), (163987, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 4), (3, 2), (61, 1), (163987, 1)] : List FactorBlock).map factorBlockValue).prod = 1440461809 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyFourV_2
      · exact prime_twentyFourV_3
      · exact prime_twentyFourV_61
      · exact prime_twentyFourV_163987
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 1440461809) ^ 720230904 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (7 : ZMod 1440461809) ^ 480153936 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (7 : ZMod 1440461809) ^ 23614128 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (7 : ZMod 1440461809) ^ 8784 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide

private theorem prime_twentyFourV_621509730110564998034623 : Nat.Prime 621509730110564998034623 := by
  apply lucas_primality 621509730110564998034623 (5 : ZMod 621509730110564998034623)
  · rw [← twentyFourVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (3061, 1), (61379, 1), (382747, 1), (1440461809, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (3061, 1), (61379, 1), (382747, 1), (1440461809, 1)] : List FactorBlock).map factorBlockValue).prod = 621509730110564998034623 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyFourV_2
      · exact prime_twentyFourV_3
      · exact prime_twentyFourV_3061
      · exact prime_twentyFourV_61379
      · exact prime_twentyFourV_382747
      · exact prime_twentyFourV_1440461809
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 621509730110564998034623) ^ 310754865055282499017311 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (5 : ZMod 621509730110564998034623) ^ 207169910036854999344874 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (5 : ZMod 621509730110564998034623) ^ 203041401538897418502 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (5 : ZMod 621509730110564998034623) ^ 10125771519747226218 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (5 : ZMod 621509730110564998034623) ^ 1623813459310105626 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (5 : ZMod 621509730110564998034623) ^ 431465607923358 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide

private theorem prime_twentyFourV_2441 : Nat.Prime 2441 := by norm_num
private theorem prime_twentyFourV_1127537 : Nat.Prime 1127537 := by norm_num
private theorem prime_twentyFourV_2422033 : Nat.Prime 2422033 := by norm_num
private theorem prime_twentyFourV_7307 : Nat.Prime 7307 := by norm_num
private theorem prime_twentyFourV_98987344441 : Nat.Prime 98987344441 := by
  apply lucas_primality 98987344441 (7 : ZMod 98987344441)
  · rw [← twentyFourVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (3, 1), (5, 1), (79, 1), (1429, 1), (7307, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (3, 1), (5, 1), (79, 1), (1429, 1), (7307, 1)] : List FactorBlock).map factorBlockValue).prod = 98987344441 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyFourV_2
      · exact prime_twentyFourV_3
      · exact prime_twentyFourV_5
      · exact prime_twentyFourV_79
      · exact prime_twentyFourV_1429
      · exact prime_twentyFourV_7307
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 98987344441) ^ 49493672220 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (7 : ZMod 98987344441) ^ 32995781480 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (7 : ZMod 98987344441) ^ 19797468888 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (7 : ZMod 98987344441) ^ 1253004360 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (7 : ZMod 98987344441) ^ 69270360 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (7 : ZMod 98987344441) ^ 13546920 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide

private theorem prime_twentyFourV_97327 : Nat.Prime 97327 := by norm_num
private theorem prime_twentyFourV_208223 : Nat.Prime 208223 := by norm_num
private theorem prime_twentyFourV_4129087 : Nat.Prime 4129087 := by norm_num
private theorem prime_twentyFourV_1997 : Nat.Prime 1997 := by norm_num
private theorem prime_twentyFourV_1929523 : Nat.Prime 1929523 := by norm_num
private theorem prime_twentyFourV_7706514863 : Nat.Prime 7706514863 := by
  apply lucas_primality 7706514863 (5 : ZMod 7706514863)
  · rw [← twentyFourVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (1997, 1), (1929523, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (1997, 1), (1929523, 1)] : List FactorBlock).map factorBlockValue).prod = 7706514863 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twentyFourV_2
      · exact prime_twentyFourV_1997
      · exact prime_twentyFourV_1929523
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 7706514863) ^ 3853257431 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (5 : ZMod 7706514863) ^ 3859046 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (5 : ZMod 7706514863) ^ 3994 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide

private theorem prime_twentyFourV_66569 : Nat.Prime 66569 := by norm_num
private theorem prime_twentyFourV_17737 : Nat.Prime 17737 := by norm_num
private theorem prime_twentyFourV_42001217 : Nat.Prime 42001217 := by
  apply lucas_primality 42001217 (3 : ZMod 42001217)
  · rw [← twentyFourVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 6), (37, 1), (17737, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 6), (37, 1), (17737, 1)] : List FactorBlock).map factorBlockValue).prod = 42001217 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twentyFourV_2
      · exact prime_twentyFourV_37
      · exact prime_twentyFourV_17737
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 42001217) ^ 21000608 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (3 : ZMod 42001217) ^ 1135168 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (3 : ZMod 42001217) ^ 2368 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide

private theorem prime_twentyFourV_1596046247 : Nat.Prime 1596046247 := by
  apply lucas_primality 1596046247 (5 : ZMod 1596046247)
  · rw [← twentyFourVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (19, 1), (42001217, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (19, 1), (42001217, 1)] : List FactorBlock).map factorBlockValue).prod = 1596046247 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twentyFourV_2
      · exact prime_twentyFourV_19
      · exact prime_twentyFourV_42001217
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 1596046247) ^ 798023123 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (5 : ZMod 1596046247) ^ 84002434 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (5 : ZMod 1596046247) ^ 38 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide

private theorem prime_twentyFourV_2221 : Nat.Prime 2221 := by norm_num
private theorem prime_twentyFourV_1427389 : Nat.Prime 1427389 := by norm_num
private theorem prime_twentyFourV_76085543257 : Nat.Prime 76085543257 := by
  apply lucas_primality 76085543257 (5 : ZMod 76085543257)
  · rw [← twentyFourVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (3, 1), (2221, 1), (1427389, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (3, 1), (2221, 1), (1427389, 1)] : List FactorBlock).map factorBlockValue).prod = 76085543257 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyFourV_2
      · exact prime_twentyFourV_3
      · exact prime_twentyFourV_2221
      · exact prime_twentyFourV_1427389
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 76085543257) ^ 38042771628 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (5 : ZMod 76085543257) ^ 25361847752 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (5 : ZMod 76085543257) ^ 34257336 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (5 : ZMod 76085543257) ^ 53304 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide

private theorem prime_twentyFourV_5934672374047 : Nat.Prime 5934672374047 := by
  apply lucas_primality 5934672374047 (3 : ZMod 5934672374047)
  · rw [← twentyFourVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (13, 1), (76085543257, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (13, 1), (76085543257, 1)] : List FactorBlock).map factorBlockValue).prod = 5934672374047 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyFourV_2
      · exact prime_twentyFourV_3
      · exact prime_twentyFourV_13
      · exact prime_twentyFourV_76085543257
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 5934672374047) ^ 2967336187023 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (3 : ZMod 5934672374047) ^ 1978224124682 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (3 : ZMod 5934672374047) ^ 456513259542 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (3 : ZMod 5934672374047) ^ 78 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide

private theorem prime_twentyFourV_449 : Nat.Prime 449 := by norm_num
private theorem prime_twentyFourV_128239 : Nat.Prime 128239 := by norm_num
private theorem prime_twentyFourV_4613533 : Nat.Prime 4613533 := by norm_num
private theorem prime_twentyFourV_73816529 : Nat.Prime 73816529 := by
  apply lucas_primality 73816529 (3 : ZMod 73816529)
  · rw [← twentyFourVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 4), (4613533, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 4), (4613533, 1)] : List FactorBlock).map factorBlockValue).prod = 73816529 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_twentyFourV_2
      · exact prime_twentyFourV_4613533
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 73816529) ^ 36908264 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (3 : ZMod 73816529) ^ 16 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide

private theorem prime_twentyFourV_3209 : Nat.Prime 3209 := by norm_num
private theorem prime_twentyFourV_40597 : Nat.Prime 40597 := by norm_num
private theorem prime_twentyFourV_260551547 : Nat.Prime 260551547 := by
  apply lucas_primality 260551547 (2 : ZMod 260551547)
  · rw [← twentyFourVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3209, 1), (40597, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3209, 1), (40597, 1)] : List FactorBlock).map factorBlockValue).prod = 260551547 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twentyFourV_2
      · exact prime_twentyFourV_3209
      · exact prime_twentyFourV_40597
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 260551547) ^ 130275773 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (2 : ZMod 260551547) ^ 81194 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (2 : ZMod 260551547) ^ 6418 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide

private theorem prime_twentyFourV_121151 : Nat.Prime 121151 := by norm_num
private theorem prime_twentyFourV_1238163221 : Nat.Prime 1238163221 := by
  apply lucas_primality 1238163221 (3 : ZMod 1238163221)
  · rw [← twentyFourVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (5, 1), (7, 1), (73, 1), (121151, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (5, 1), (7, 1), (73, 1), (121151, 1)] : List FactorBlock).map factorBlockValue).prod = 1238163221 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyFourV_2
      · exact prime_twentyFourV_5
      · exact prime_twentyFourV_7
      · exact prime_twentyFourV_73
      · exact prime_twentyFourV_121151
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1238163221) ^ 619081610 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (3 : ZMod 1238163221) ^ 247632644 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (3 : ZMod 1238163221) ^ 176880460 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (3 : ZMod 1238163221) ^ 16961140 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (3 : ZMod 1238163221) ^ 10220 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide

private theorem prime_twentyFourV_20563414774369 : Nat.Prime 20563414774369 := by
  apply lucas_primality 20563414774369 (17 : ZMod 20563414774369)
  · rw [← twentyFourVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 5), (3, 1), (173, 1), (1238163221, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 5), (3, 1), (173, 1), (1238163221, 1)] : List FactorBlock).map factorBlockValue).prod = 20563414774369 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyFourV_2
      · exact prime_twentyFourV_3
      · exact prime_twentyFourV_173
      · exact prime_twentyFourV_1238163221
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (17 : ZMod 20563414774369) ^ 10281707387184 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (17 : ZMod 20563414774369) ^ 6854471591456 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (17 : ZMod 20563414774369) ^ 118863669216 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (17 : ZMod 20563414774369) ^ 16608 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide

private theorem prime_twentyFourV_44351 : Nat.Prime 44351 := by norm_num
private theorem prime_twentyFourV_6895393 : Nat.Prime 6895393 := by norm_num
private theorem prime_twentyFourV_29358487194529 : Nat.Prime 29358487194529 := by
  apply lucas_primality 29358487194529 (7 : ZMod 29358487194529)
  · rw [← twentyFourVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 5), (3, 1), (44351, 1), (6895393, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 5), (3, 1), (44351, 1), (6895393, 1)] : List FactorBlock).map factorBlockValue).prod = 29358487194529 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyFourV_2
      · exact prime_twentyFourV_3
      · exact prime_twentyFourV_44351
      · exact prime_twentyFourV_6895393
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 29358487194529) ^ 14679243597264 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (7 : ZMod 29358487194529) ^ 9786162398176 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (7 : ZMod 29358487194529) ^ 661957728 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (7 : ZMod 29358487194529) ^ 4257696 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide

private theorem prime_twentyFourV_37309 : Nat.Prime 37309 := by norm_num
private theorem prime_twentyFourV_1222615931 : Nat.Prime 1222615931 := by
  apply lucas_primality 1222615931 (2 : ZMod 1222615931)
  · rw [← twentyFourVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 1), (29, 1), (113, 1), (37309, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 1), (29, 1), (113, 1), (37309, 1)] : List FactorBlock).map factorBlockValue).prod = 1222615931 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyFourV_2
      · exact prime_twentyFourV_5
      · exact prime_twentyFourV_29
      · exact prime_twentyFourV_113
      · exact prime_twentyFourV_37309
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1222615931) ^ 611307965 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (2 : ZMod 1222615931) ^ 244523186 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (2 : ZMod 1222615931) ^ 42159170 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (2 : ZMod 1222615931) ^ 10819610 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (2 : ZMod 1222615931) ^ 32770 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide

private theorem prime_twentyFourV_2531 : Nat.Prime 2531 := by norm_num
private theorem prime_twentyFourV_6763 : Nat.Prime 6763 := by norm_num
private theorem prime_twentyFourV_462094662389 : Nat.Prime 462094662389 := by
  apply lucas_primality 462094662389 (2 : ZMod 462094662389)
  · rw [← twentyFourVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (17, 1), (397, 1), (2531, 1), (6763, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (17, 1), (397, 1), (2531, 1), (6763, 1)] : List FactorBlock).map factorBlockValue).prod = 462094662389 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyFourV_2
      · exact prime_twentyFourV_17
      · exact prime_twentyFourV_397
      · exact prime_twentyFourV_2531
      · exact prime_twentyFourV_6763
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 462094662389) ^ 231047331194 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (2 : ZMod 462094662389) ^ 27182038964 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (2 : ZMod 462094662389) ^ 1163966404 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (2 : ZMod 462094662389) ^ 182573948 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (2 : ZMod 462094662389) ^ 68326876 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide

private theorem prime_twentyFourV_1667237541899513 : Nat.Prime 1667237541899513 := by
  apply lucas_primality 1667237541899513 (3 : ZMod 1667237541899513)
  · rw [← twentyFourVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (11, 1), (41, 1), (462094662389, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (11, 1), (41, 1), (462094662389, 1)] : List FactorBlock).map factorBlockValue).prod = 1667237541899513 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyFourV_2
      · exact prime_twentyFourV_11
      · exact prime_twentyFourV_41
      · exact prime_twentyFourV_462094662389
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1667237541899513) ^ 833618770949756 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (3 : ZMod 1667237541899513) ^ 151567049263592 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (3 : ZMod 1667237541899513) ^ 40664330290232 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (3 : ZMod 1667237541899513) ^ 3608 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide

private theorem prime_twentyFourV_483498887150858771 : Nat.Prime 483498887150858771 := by
  apply lucas_primality 483498887150858771 (2 : ZMod 483498887150858771)
  · rw [← twentyFourVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 1), (29, 1), (1667237541899513, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 1), (29, 1), (1667237541899513, 1)] : List FactorBlock).map factorBlockValue).prod = 483498887150858771 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyFourV_2
      · exact prime_twentyFourV_5
      · exact prime_twentyFourV_29
      · exact prime_twentyFourV_1667237541899513
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 483498887150858771) ^ 241749443575429385 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (2 : ZMod 483498887150858771) ^ 96699777430171754 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (2 : ZMod 483498887150858771) ^ 16672375418995130 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (2 : ZMod 483498887150858771) ^ 290 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide

private theorem prime_twentyFourV_8209 : Nat.Prime 8209 := by norm_num
private theorem prime_twentyFourV_63793 : Nat.Prime 63793 := by norm_num
private theorem prime_twentyFourV_14407 : Nat.Prime 14407 := by norm_num
private theorem prime_twentyFourV_23137643 : Nat.Prime 23137643 := by
  apply lucas_primality 23137643 (2 : ZMod 23137643)
  · rw [← twentyFourVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (11, 1), (73, 1), (14407, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (11, 1), (73, 1), (14407, 1)] : List FactorBlock).map factorBlockValue).prod = 23137643 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyFourV_2
      · exact prime_twentyFourV_11
      · exact prime_twentyFourV_73
      · exact prime_twentyFourV_14407
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 23137643) ^ 11568821 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (2 : ZMod 23137643) ^ 2103422 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (2 : ZMod 23137643) ^ 316954 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (2 : ZMod 23137643) ^ 1606 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide

private theorem prime_twentyFourV_971781007 : Nat.Prime 971781007 := by
  apply lucas_primality 971781007 (3 : ZMod 971781007)
  · rw [← twentyFourVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (7, 1), (23137643, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (7, 1), (23137643, 1)] : List FactorBlock).map factorBlockValue).prod = 971781007 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyFourV_2
      · exact prime_twentyFourV_3
      · exact prime_twentyFourV_7
      · exact prime_twentyFourV_23137643
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 971781007) ^ 485890503 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (3 : ZMod 971781007) ^ 323927002 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (3 : ZMod 971781007) ^ 138825858 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (3 : ZMod 971781007) ^ 42 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide

private theorem prime_twentyFourV_2081 : Nat.Prime 2081 := by norm_num
private theorem prime_twentyFourV_1137886639 : Nat.Prime 1137886639 := by
  apply lucas_primality 1137886639 (3 : ZMod 1137886639)
  · rw [← twentyFourVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (7, 1), (47, 1), (277, 1), (2081, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (7, 1), (47, 1), (277, 1), (2081, 1)] : List FactorBlock).map factorBlockValue).prod = 1137886639 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyFourV_2
      · exact prime_twentyFourV_3
      · exact prime_twentyFourV_7
      · exact prime_twentyFourV_47
      · exact prime_twentyFourV_277
      · exact prime_twentyFourV_2081
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1137886639) ^ 568943319 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (3 : ZMod 1137886639) ^ 379295546 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (3 : ZMod 1137886639) ^ 162555234 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (3 : ZMod 1137886639) ^ 24210354 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (3 : ZMod 1137886639) ^ 4107894 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (3 : ZMod 1137886639) ^ 546798 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide

private theorem prime_twentyFourV_65129 : Nat.Prime 65129 := by norm_num
private theorem prime_twentyFourV_182467 : Nat.Prime 182467 := by norm_num
private theorem prime_twentyFourV_2207 : Nat.Prime 2207 := by norm_num
private theorem prime_twentyFourV_5400053 : Nat.Prime 5400053 := by norm_num
private theorem prime_twentyFourV_170545391855011 : Nat.Prime 170545391855011 := by
  apply lucas_primality 170545391855011 (2 : ZMod 170545391855011)
  · rw [← twentyFourVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 3), (5, 1), (53, 1), (2207, 1), (5400053, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 3), (5, 1), (53, 1), (2207, 1), (5400053, 1)] : List FactorBlock).map factorBlockValue).prod = 170545391855011 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyFourV_2
      · exact prime_twentyFourV_3
      · exact prime_twentyFourV_5
      · exact prime_twentyFourV_53
      · exact prime_twentyFourV_2207
      · exact prime_twentyFourV_5400053
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 170545391855011) ^ 85272695927505 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (2 : ZMod 170545391855011) ^ 56848463951670 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (2 : ZMod 170545391855011) ^ 34109078371002 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (2 : ZMod 170545391855011) ^ 3217837582170 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (2 : ZMod 170545391855011) ^ 77274758430 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (2 : ZMod 170545391855011) ^ 31582170 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide

private theorem prime_twentyFourV_8713293684370321798361 : Nat.Prime 8713293684370321798361 := by
  apply lucas_primality 8713293684370321798361 (3 : ZMod 8713293684370321798361)
  · rw [← twentyFourVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (5, 1), (7, 1), (182467, 1), (170545391855011, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (5, 1), (7, 1), (182467, 1), (170545391855011, 1)] : List FactorBlock).map factorBlockValue).prod = 8713293684370321798361 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyFourV_2
      · exact prime_twentyFourV_5
      · exact prime_twentyFourV_7
      · exact prime_twentyFourV_182467
      · exact prime_twentyFourV_170545391855011
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 8713293684370321798361) ^ 4356646842185160899180 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (3 : ZMod 8713293684370321798361) ^ 1742658736874064359672 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (3 : ZMod 8713293684370321798361) ^ 1244756240624331685480 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (3 : ZMod 8713293684370321798361) ^ 47752709719403080 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (3 : ZMod 8713293684370321798361) ^ 51090760 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide

private theorem prime_twentyFourV_709 : Nat.Prime 709 := by norm_num
private theorem prime_twentyFourV_58337 : Nat.Prime 58337 := by norm_num
private theorem prime_twentyFourV_347 : Nat.Prime 347 := by norm_num
private theorem prime_twentyFourV_12251 : Nat.Prime 12251 := by norm_num
private theorem prime_twentyFourV_5479 : Nat.Prime 5479 := by norm_num
private theorem prime_twentyFourV_644549 : Nat.Prime 644549 := by norm_num
private theorem prime_twentyFourV_7062967943 : Nat.Prime 7062967943 := by
  apply lucas_primality 7062967943 (5 : ZMod 7062967943)
  · rw [← twentyFourVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5479, 1), (644549, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5479, 1), (644549, 1)] : List FactorBlock).map factorBlockValue).prod = 7062967943 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twentyFourV_2
      · exact prime_twentyFourV_5479
      · exact prime_twentyFourV_644549
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 7062967943) ^ 3531483971 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (5 : ZMod 7062967943) ^ 1289098 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (5 : ZMod 7062967943) ^ 10958 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide

private theorem prime_twentyFourV_9691183070205617 : Nat.Prime 9691183070205617 := by
  apply lucas_primality 9691183070205617 (3 : ZMod 9691183070205617)
  · rw [← twentyFourVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 4), (7, 1), (12251, 1), (7062967943, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 4), (7, 1), (12251, 1), (7062967943, 1)] : List FactorBlock).map factorBlockValue).prod = 9691183070205617 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyFourV_2
      · exact prime_twentyFourV_7
      · exact prime_twentyFourV_12251
      · exact prime_twentyFourV_7062967943
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 9691183070205617) ^ 4845591535102808 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (3 : ZMod 9691183070205617) ^ 1384454724315088 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (3 : ZMod 9691183070205617) ^ 791052409616 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (3 : ZMod 9691183070205617) ^ 1372112 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide

private theorem prime_twentyFourV_13451362101445396397 : Nat.Prime 13451362101445396397 := by
  apply lucas_primality 13451362101445396397 (2 : ZMod 13451362101445396397)
  · rw [← twentyFourVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (347, 1), (9691183070205617, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (347, 1), (9691183070205617, 1)] : List FactorBlock).map factorBlockValue).prod = 13451362101445396397 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twentyFourV_2
      · exact prime_twentyFourV_347
      · exact prime_twentyFourV_9691183070205617
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 13451362101445396397) ^ 6725681050722698198 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (2 : ZMod 13451362101445396397) ^ 38764732280822468 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (2 : ZMod 13451362101445396397) ^ 1388 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide

private theorem prime_twentyFourV_545661638816687200389859201 : Nat.Prime 545661638816687200389859201 := by
  apply lucas_primality 545661638816687200389859201 (13 : ZMod 545661638816687200389859201)
  · rw [← twentyFourVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 7), (3, 4), (5, 2), (7, 2), (11, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 7), (3, 4), (5, 2), (7, 2), (11, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod = 545661638816687200389859201 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyFourV_2
      · exact prime_twentyFourV_3
      · exact prime_twentyFourV_5
      · exact prime_twentyFourV_7
      · exact prime_twentyFourV_11
      · exact prime_twentyFourV_17
      · exact prime_twentyFourV_19
      · exact prime_twentyFourV_23
      · exact prime_twentyFourV_29
      · exact prime_twentyFourV_31
      · exact prime_twentyFourV_37
      · exact prime_twentyFourV_41
      · exact prime_twentyFourV_43
      · exact prime_twentyFourV_47
      · exact prime_twentyFourV_53
      · exact prime_twentyFourV_59
      · exact prime_twentyFourV_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 545661638816687200389859201) ^ 272830819408343600194929600 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (13 : ZMod 545661638816687200389859201) ^ 181887212938895733463286400 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (13 : ZMod 545661638816687200389859201) ^ 109132327763337440077971840 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (13 : ZMod 545661638816687200389859201) ^ 77951662688098171484265600 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (13 : ZMod 545661638816687200389859201) ^ 49605603528789745489987200 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (13 : ZMod 545661638816687200389859201) ^ 32097743459805129434697600 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (13 : ZMod 545661638816687200389859201) ^ 28719033621930905283676800 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (13 : ZMod 545661638816687200389859201) ^ 23724419078986400016950400 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (13 : ZMod 545661638816687200389859201) ^ 18815918579885765530684800 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (13 : ZMod 545661638816687200389859201) ^ 17601988348925393560963200 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (13 : ZMod 545661638816687200389859201) ^ 14747611859910464875401600 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (13 : ZMod 545661638816687200389859201) ^ 13308820458943590253411200 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (13 : ZMod 545661638816687200389859201) ^ 12689805553876446520694400 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (13 : ZMod 545661638816687200389859201) ^ 11609822102482706391273600 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (13 : ZMod 545661638816687200389859201) ^ 10295502619182777365846400 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (13 : ZMod 545661638816687200389859201) ^ 9248502352825206786268800 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (13 : ZMod 545661638816687200389859201) ^ 8945272767486675416227200 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide

private theorem prime_twentyFourV_834131 : Nat.Prime 834131 := by norm_num
private theorem prime_twentyFourV_330315877 : Nat.Prime 330315877 := by
  apply lucas_primality 330315877 (2 : ZMod 330315877)
  · rw [← twentyFourVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 2), (11, 1), (834131, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 2), (11, 1), (834131, 1)] : List FactorBlock).map factorBlockValue).prod = 330315877 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyFourV_2
      · exact prime_twentyFourV_3
      · exact prime_twentyFourV_11
      · exact prime_twentyFourV_834131
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 330315877) ^ 165157938 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (2 : ZMod 330315877) ^ 110105292 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (2 : ZMod 330315877) ^ 30028716 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (2 : ZMod 330315877) ^ 396 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide

private theorem prime_twentyFourV_885246550361 : Nat.Prime 885246550361 := by
  apply lucas_primality 885246550361 (6 : ZMod 885246550361)
  · rw [← twentyFourVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (5, 1), (67, 1), (330315877, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (5, 1), (67, 1), (330315877, 1)] : List FactorBlock).map factorBlockValue).prod = 885246550361 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyFourV_2
      · exact prime_twentyFourV_5
      · exact prime_twentyFourV_67
      · exact prime_twentyFourV_330315877
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 885246550361) ^ 442623275180 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (6 : ZMod 885246550361) ^ 177049310072 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (6 : ZMod 885246550361) ^ 13212635080 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (6 : ZMod 885246550361) ^ 2680 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide

private theorem prime_twentyFourV_1753 : Nat.Prime 1753 := by norm_num
private theorem prime_twentyFourV_491773 : Nat.Prime 491773 := by norm_num
private theorem prime_twentyFourV_191381331319 : Nat.Prime 191381331319 := by
  apply lucas_primality 191381331319 (6 : ZMod 191381331319)
  · rw [← twentyFourVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (37, 1), (1753, 1), (491773, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (37, 1), (1753, 1), (491773, 1)] : List FactorBlock).map factorBlockValue).prod = 191381331319 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyFourV_2
      · exact prime_twentyFourV_3
      · exact prime_twentyFourV_37
      · exact prime_twentyFourV_1753
      · exact prime_twentyFourV_491773
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 191381331319) ^ 95690665659 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (6 : ZMod 191381331319) ^ 63793777106 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (6 : ZMod 191381331319) ^ 5172468414 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (6 : ZMod 191381331319) ^ 109173606 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (6 : ZMod 191381331319) ^ 389166 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide

private theorem prime_twentyFourV_604765006968041 : Nat.Prime 604765006968041 := by
  apply lucas_primality 604765006968041 (3 : ZMod 604765006968041)
  · rw [← twentyFourVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (5, 1), (79, 1), (191381331319, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (5, 1), (79, 1), (191381331319, 1)] : List FactorBlock).map factorBlockValue).prod = 604765006968041 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyFourV_2
      · exact prime_twentyFourV_5
      · exact prime_twentyFourV_79
      · exact prime_twentyFourV_191381331319
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 604765006968041) ^ 302382503484020 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (3 : ZMod 604765006968041) ^ 120953001393608 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (3 : ZMod 604765006968041) ^ 7655253252760 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (3 : ZMod 604765006968041) ^ 3160 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide

private theorem prime_twentyFourV_525451948490143230005049601 : Nat.Prime 525451948490143230005049601 := by
  apply lucas_primality 525451948490143230005049601 (179 : ZMod 525451948490143230005049601)
  · rw [← twentyFourVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 8), (3, 1), (5, 2), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 8), (3, 1), (5, 2), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod = 525451948490143230005049601 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyFourV_2
      · exact prime_twentyFourV_3
      · exact prime_twentyFourV_5
      · exact prime_twentyFourV_7
      · exact prime_twentyFourV_11
      · exact prime_twentyFourV_13
      · exact prime_twentyFourV_17
      · exact prime_twentyFourV_19
      · exact prime_twentyFourV_23
      · exact prime_twentyFourV_29
      · exact prime_twentyFourV_31
      · exact prime_twentyFourV_37
      · exact prime_twentyFourV_41
      · exact prime_twentyFourV_43
      · exact prime_twentyFourV_47
      · exact prime_twentyFourV_53
      · exact prime_twentyFourV_59
      · exact prime_twentyFourV_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (179 : ZMod 525451948490143230005049601) ^ 262725974245071615002524800 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (179 : ZMod 525451948490143230005049601) ^ 175150649496714410001683200 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (179 : ZMod 525451948490143230005049601) ^ 105090389698028646001009920 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (179 : ZMod 525451948490143230005049601) ^ 75064564070020461429292800 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (179 : ZMod 525451948490143230005049601) ^ 47768358953649384545913600 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (179 : ZMod 525451948490143230005049601) ^ 40419380653087940769619200 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (179 : ZMod 525451948490143230005049601) ^ 30908938146479013529708800 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (179 : ZMod 525451948490143230005049601) ^ 27655365710007538421318400 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (179 : ZMod 525451948490143230005049601) ^ 22845736890875792608915200 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (179 : ZMod 525451948490143230005049601) ^ 18119032706556663103622400 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (179 : ZMod 525451948490143230005049601) ^ 16950062854520749355001600 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (179 : ZMod 525451948490143230005049601) ^ 14201404013247114324460800 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (179 : ZMod 525451948490143230005049601) ^ 12815901182686420244025600 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (179 : ZMod 525451948490143230005049601) ^ 12219812755584726279187200 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (179 : ZMod 525451948490143230005049601) ^ 11179828691279643191596800 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (179 : ZMod 525451948490143230005049601) ^ 9914187707361193018963200 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (179 : ZMod 525451948490143230005049601) ^ 8905965228646495423814400 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (179 : ZMod 525451948490143230005049601) ^ 8613966368690872623033600 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide

private theorem prime_twentyFourV_193 : Nat.Prime 193 := by norm_num
private theorem prime_twentyFourV_12301 : Nat.Prime 12301 := by norm_num
private theorem prime_twentyFourV_599 : Nat.Prime 599 := by norm_num
private theorem prime_twentyFourV_8623 : Nat.Prime 8623 := by norm_num
private theorem prime_twentyFourV_26693 : Nat.Prime 26693 := by norm_num
private theorem prime_twentyFourV_41086472758979 : Nat.Prime 41086472758979 := by
  apply lucas_primality 41086472758979 (2 : ZMod 41086472758979)
  · rw [← twentyFourVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (149, 1), (599, 1), (8623, 1), (26693, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (149, 1), (599, 1), (8623, 1), (26693, 1)] : List FactorBlock).map factorBlockValue).prod = 41086472758979 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyFourV_2
      · exact prime_twentyFourV_149
      · exact prime_twentyFourV_599
      · exact prime_twentyFourV_8623
      · exact prime_twentyFourV_26693
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 41086472758979) ^ 20543236379489 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (2 : ZMod 41086472758979) ^ 275748139322 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (2 : ZMod 41086472758979) ^ 68591774222 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (2 : ZMod 41086472758979) ^ 4764753886 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (2 : ZMod 41086472758979) ^ 1539222746 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide

private theorem prime_twentyFourV_1010809402816401359 : Nat.Prime 1010809402816401359 := by
  apply lucas_primality 1010809402816401359 (13 : ZMod 1010809402816401359)
  · rw [← twentyFourVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (12301, 1), (41086472758979, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (12301, 1), (41086472758979, 1)] : List FactorBlock).map factorBlockValue).prod = 1010809402816401359 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twentyFourV_2
      · exact prime_twentyFourV_12301
      · exact prime_twentyFourV_41086472758979
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (13 : ZMod 1010809402816401359) ^ 505404701408200679 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (13 : ZMod 1010809402816401359) ^ 82172945517958 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (13 : ZMod 1010809402816401359) ^ 24602 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide

private theorem prime_twentyFourV_517267 : Nat.Prime 517267 := by norm_num
private theorem prime_twentyFourV_40346827 : Nat.Prime 40346827 := by
  apply lucas_primality 40346827 (2 : ZMod 40346827)
  · rw [← twentyFourVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (13, 1), (517267, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (13, 1), (517267, 1)] : List FactorBlock).map factorBlockValue).prod = 40346827 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyFourV_2
      · exact prime_twentyFourV_3
      · exact prime_twentyFourV_13
      · exact prime_twentyFourV_517267
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 40346827) ^ 20173413 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (2 : ZMod 40346827) ^ 13448942 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (2 : ZMod 40346827) ^ 3103602 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (2 : ZMod 40346827) ^ 78 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide

private theorem prime_twentyFourV_4159 : Nat.Prime 4159 := by norm_num
private theorem prime_twentyFourV_16453 : Nat.Prime 16453 := by norm_num
private theorem prime_twentyFourV_910838081 : Nat.Prime 910838081 := by
  apply lucas_primality 910838081 (3 : ZMod 910838081)
  · rw [← twentyFourVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 6), (5, 1), (173, 1), (16453, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 6), (5, 1), (173, 1), (16453, 1)] : List FactorBlock).map factorBlockValue).prod = 910838081 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyFourV_2
      · exact prime_twentyFourV_5
      · exact prime_twentyFourV_173
      · exact prime_twentyFourV_16453
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 910838081) ^ 455419040 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (3 : ZMod 910838081) ^ 182167616 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (3 : ZMod 910838081) ^ 5264960 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (3 : ZMod 910838081) ^ 55360 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide

private theorem prime_twentyFourV_75763511577581 : Nat.Prime 75763511577581 := by
  apply lucas_primality 75763511577581 (3 : ZMod 75763511577581)
  · rw [← twentyFourVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (5, 1), (4159, 1), (910838081, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (5, 1), (4159, 1), (910838081, 1)] : List FactorBlock).map factorBlockValue).prod = 75763511577581 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyFourV_2
      · exact prime_twentyFourV_5
      · exact prime_twentyFourV_4159
      · exact prime_twentyFourV_910838081
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 75763511577581) ^ 37881755788790 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (3 : ZMod 75763511577581) ^ 15152702315516 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (3 : ZMod 75763511577581) ^ 18216761620 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (3 : ZMod 75763511577581) ^ 83180 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide

private theorem prime_twentyFourV_17274080639688469 : Nat.Prime 17274080639688469 := by
  apply lucas_primality 17274080639688469 (2 : ZMod 17274080639688469)
  · rw [← twentyFourVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (19, 1), (75763511577581, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (19, 1), (75763511577581, 1)] : List FactorBlock).map factorBlockValue).prod = 17274080639688469 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyFourV_2
      · exact prime_twentyFourV_3
      · exact prime_twentyFourV_19
      · exact prime_twentyFourV_75763511577581
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 17274080639688469) ^ 8637040319844234 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (2 : ZMod 17274080639688469) ^ 5758026879896156 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (2 : ZMod 17274080639688469) ^ 909162138930972 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (2 : ZMod 17274080639688469) ^ 228 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide

private theorem prime_twentyFourV_677 : Nat.Prime 677 := by norm_num
private theorem prime_twentyFourV_17417 : Nat.Prime 17417 := by norm_num
private theorem prime_twentyFourV_144038591 : Nat.Prime 144038591 := by
  apply lucas_primality 144038591 (7 : ZMod 144038591)
  · rw [← twentyFourVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 1), (827, 1), (17417, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 1), (827, 1), (17417, 1)] : List FactorBlock).map factorBlockValue).prod = 144038591 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyFourV_2
      · exact prime_twentyFourV_5
      · exact prime_twentyFourV_827
      · exact prime_twentyFourV_17417
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 144038591) ^ 72019295 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (7 : ZMod 144038591) ^ 28807718 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (7 : ZMod 144038591) ^ 174170 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (7 : ZMod 144038591) ^ 8270 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide

private theorem prime_twentyFourV_390056504429 : Nat.Prime 390056504429 := by
  apply lucas_primality 390056504429 (2 : ZMod 390056504429)
  · rw [← twentyFourVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (677, 1), (144038591, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (677, 1), (144038591, 1)] : List FactorBlock).map factorBlockValue).prod = 390056504429 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twentyFourV_2
      · exact prime_twentyFourV_677
      · exact prime_twentyFourV_144038591
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 390056504429) ^ 195028252214 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (2 : ZMod 390056504429) ^ 576154364 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (2 : ZMod 390056504429) ^ 2708 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide

private theorem prime_twentyFourV_293081 : Nat.Prime 293081 := by norm_num
private theorem prime_twentyFourV_2126213 : Nat.Prime 2126213 := by norm_num
private theorem prime_twentyFourV_1088621057 : Nat.Prime 1088621057 := by
  apply lucas_primality 1088621057 (3 : ZMod 1088621057)
  · rw [← twentyFourVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 9), (2126213, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 9), (2126213, 1)] : List FactorBlock).map factorBlockValue).prod = 1088621057 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_twentyFourV_2
      · exact prime_twentyFourV_2126213
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 1088621057) ^ 544310528 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (3 : ZMod 1088621057) ^ 512 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide

private theorem prime_twentyFourV_1276216592026469 : Nat.Prime 1276216592026469 := by
  apply lucas_primality 1276216592026469 (2 : ZMod 1276216592026469)
  · rw [← twentyFourVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (293081, 1), (1088621057, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (293081, 1), (1088621057, 1)] : List FactorBlock).map factorBlockValue).prod = 1276216592026469 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twentyFourV_2
      · exact prime_twentyFourV_293081
      · exact prime_twentyFourV_1088621057
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 1276216592026469) ^ 638108296013234 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (2 : ZMod 1276216592026469) ^ 4354484228 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (2 : ZMod 1276216592026469) ^ 1172324 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide

private theorem prime_twentyFourV_16831 : Nat.Prime 16831 := by norm_num
private theorem prime_twentyFourV_57427 : Nat.Prime 57427 := by norm_num
private theorem prime_twentyFourV_389 : Nat.Prime 389 := by norm_num
private theorem prime_twentyFourV_10976629 : Nat.Prime 10976629 := by norm_num
private theorem prime_twentyFourV_205745933977 : Nat.Prime 205745933977 := by
  apply lucas_primality 205745933977 (5 : ZMod 205745933977)
  · rw [← twentyFourVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (3, 1), (11, 1), (71, 1), (10976629, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (3, 1), (11, 1), (71, 1), (10976629, 1)] : List FactorBlock).map factorBlockValue).prod = 205745933977 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyFourV_2
      · exact prime_twentyFourV_3
      · exact prime_twentyFourV_11
      · exact prime_twentyFourV_71
      · exact prime_twentyFourV_10976629
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 205745933977) ^ 102872966988 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (5 : ZMod 205745933977) ^ 68581977992 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (5 : ZMod 205745933977) ^ 18704175816 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (5 : ZMod 205745933977) ^ 2897830056 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (5 : ZMod 205745933977) ^ 18744 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide

private theorem prime_twentyFourV_506142404437043173 : Nat.Prime 506142404437043173 := by
  apply lucas_primality 506142404437043173 (5 : ZMod 506142404437043173)
  · rw [← twentyFourVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (17, 1), (31, 1), (389, 1), (205745933977, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (17, 1), (31, 1), (389, 1), (205745933977, 1)] : List FactorBlock).map factorBlockValue).prod = 506142404437043173 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyFourV_2
      · exact prime_twentyFourV_3
      · exact prime_twentyFourV_17
      · exact prime_twentyFourV_31
      · exact prime_twentyFourV_389
      · exact prime_twentyFourV_205745933977
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 506142404437043173) ^ 253071202218521586 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (5 : ZMod 506142404437043173) ^ 168714134812347724 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (5 : ZMod 506142404437043173) ^ 29773082613943716 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (5 : ZMod 506142404437043173) ^ 16327174336678812 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (5 : ZMod 506142404437043173) ^ 1301137286470548 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (5 : ZMod 506142404437043173) ^ 2460036 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide

private theorem prime_twentyFourV_2297 : Nat.Prime 2297 := by norm_num
private theorem prime_twentyFourV_630577 : Nat.Prime 630577 := by norm_num
private theorem prime_twentyFourV_76631 : Nat.Prime 76631 := by norm_num
private theorem prime_twentyFourV_468499 : Nat.Prime 468499 := by norm_num
private theorem prime_twentyFourV_1156039 : Nat.Prime 1156039 := by norm_num
private theorem prime_twentyFourV_332028706727135129 : Nat.Prime 332028706727135129 := by
  apply lucas_primality 332028706727135129 (3 : ZMod 332028706727135129)
  · rw [← twentyFourVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (76631, 1), (468499, 1), (1156039, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (76631, 1), (468499, 1), (1156039, 1)] : List FactorBlock).map factorBlockValue).prod = 332028706727135129 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyFourV_2
      · exact prime_twentyFourV_76631
      · exact prime_twentyFourV_468499
      · exact prime_twentyFourV_1156039
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 332028706727135129) ^ 166014353363567564 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (3 : ZMod 332028706727135129) ^ 4332824923688 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (3 : ZMod 332028706727135129) ^ 708707396872 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (3 : ZMod 332028706727135129) ^ 287212374952 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide

private theorem prime_twentyFourV_4327 : Nat.Prime 4327 := by norm_num
private theorem prime_twentyFourV_1214459 : Nat.Prime 1214459 := by norm_num
private theorem prime_twentyFourV_983 : Nat.Prime 983 := by norm_num
private theorem prime_twentyFourV_6079 : Nat.Prime 6079 := by norm_num
private theorem prime_twentyFourV_35853943 : Nat.Prime 35853943 := by
  apply lucas_primality 35853943 (3 : ZMod 35853943)
  · rw [← twentyFourVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (983, 1), (6079, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (983, 1), (6079, 1)] : List FactorBlock).map factorBlockValue).prod = 35853943 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyFourV_2
      · exact prime_twentyFourV_3
      · exact prime_twentyFourV_983
      · exact prime_twentyFourV_6079
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 35853943) ^ 17926971 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (3 : ZMod 35853943) ^ 11951314 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (3 : ZMod 35853943) ^ 36474 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (3 : ZMod 35853943) ^ 5898 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide

private theorem prime_twentyFourV_376537177183483 : Nat.Prime 376537177183483 := by
  apply lucas_primality 376537177183483 (2 : ZMod 376537177183483)
  · rw [← twentyFourVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 7), (7, 4), (35853943, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 7), (7, 4), (35853943, 1)] : List FactorBlock).map factorBlockValue).prod = 376537177183483 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyFourV_2
      · exact prime_twentyFourV_3
      · exact prime_twentyFourV_7
      · exact prime_twentyFourV_35853943
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 376537177183483) ^ 188268588591741 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (2 : ZMod 376537177183483) ^ 125512392394494 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (2 : ZMod 376537177183483) ^ 53791025311926 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (2 : ZMod 376537177183483) ^ 10501974 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide

private theorem prime_twentyFourV_3842989 : Nat.Prime 3842989 := by norm_num
private theorem prime_twentyFourV_356509 : Nat.Prime 356509 := by norm_num
private theorem prime_twentyFourV_367917289 : Nat.Prime 367917289 := by
  apply lucas_primality 367917289 (14 : ZMod 367917289)
  · rw [← twentyFourVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (3, 1), (43, 1), (356509, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (3, 1), (43, 1), (356509, 1)] : List FactorBlock).map factorBlockValue).prod = 367917289 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyFourV_2
      · exact prime_twentyFourV_3
      · exact prime_twentyFourV_43
      · exact prime_twentyFourV_356509
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (14 : ZMod 367917289) ^ 183958644 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (14 : ZMod 367917289) ^ 122639096 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (14 : ZMod 367917289) ^ 8556216 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (14 : ZMod 367917289) ^ 1032 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide

private theorem prime_twentyFourV_831529 : Nat.Prime 831529 := by norm_num
private theorem prime_twentyFourV_783300319 : Nat.Prime 783300319 := by
  apply lucas_primality 783300319 (6 : ZMod 783300319)
  · rw [← twentyFourVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (157, 1), (831529, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (157, 1), (831529, 1)] : List FactorBlock).map factorBlockValue).prod = 783300319 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyFourV_2
      · exact prime_twentyFourV_3
      · exact prime_twentyFourV_157
      · exact prime_twentyFourV_831529
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 783300319) ^ 391650159 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (6 : ZMod 783300319) ^ 261100106 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (6 : ZMod 783300319) ^ 4989174 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (6 : ZMod 783300319) ^ 942 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide

private theorem prime_twentyFourV_328986133981 : Nat.Prime 328986133981 := by
  apply lucas_primality 328986133981 (37 : ZMod 328986133981)
  · rw [← twentyFourVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (5, 1), (7, 1), (783300319, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (5, 1), (7, 1), (783300319, 1)] : List FactorBlock).map factorBlockValue).prod = 328986133981 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyFourV_2
      · exact prime_twentyFourV_3
      · exact prime_twentyFourV_5
      · exact prime_twentyFourV_7
      · exact prime_twentyFourV_783300319
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (37 : ZMod 328986133981) ^ 164493066990 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (37 : ZMod 328986133981) ^ 109662044660 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (37 : ZMod 328986133981) ^ 65797226796 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (37 : ZMod 328986133981) ^ 46998019140 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (37 : ZMod 328986133981) ^ 420 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide

private theorem prime_twentyFourV_97 : Nat.Prime 97 := by norm_num
private theorem prime_twentyFourV_44983 : Nat.Prime 44983 := by norm_num
private theorem prime_twentyFourV_62011 : Nat.Prime 62011 := by norm_num
private theorem prime_twentyFourV_367 : Nat.Prime 367 := by norm_num
private theorem prime_twentyFourV_15787 : Nat.Prime 15787 := by norm_num
private theorem prime_twentyFourV_69525949 : Nat.Prime 69525949 := by
  apply lucas_primality 69525949 (2 : ZMod 69525949)
  · rw [← twentyFourVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (367, 1), (15787, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (367, 1), (15787, 1)] : List FactorBlock).map factorBlockValue).prod = 69525949 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyFourV_2
      · exact prime_twentyFourV_3
      · exact prime_twentyFourV_367
      · exact prime_twentyFourV_15787
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 69525949) ^ 34762974 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (2 : ZMod 69525949) ^ 23175316 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (2 : ZMod 69525949) ^ 189444 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (2 : ZMod 69525949) ^ 4404 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide

private theorem prime_twentyFourV_6118283513 : Nat.Prime 6118283513 := by
  apply lucas_primality 6118283513 (3 : ZMod 6118283513)
  · rw [← twentyFourVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (11, 1), (69525949, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (11, 1), (69525949, 1)] : List FactorBlock).map factorBlockValue).prod = 6118283513 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twentyFourV_2
      · exact prime_twentyFourV_11
      · exact prime_twentyFourV_69525949
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 6118283513) ^ 3059141756 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (3 : ZMod 6118283513) ^ 556207592 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (3 : ZMod 6118283513) ^ 88 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide

private theorem prime_twentyFourV_104885372978717557351 : Nat.Prime 104885372978717557351 := by
  apply lucas_primality 104885372978717557351 (6 : ZMod 104885372978717557351)
  · rw [← twentyFourVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (5, 2), (19, 1), (97, 1), (62011, 1), (6118283513, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (5, 2), (19, 1), (97, 1), (62011, 1), (6118283513, 1)] : List FactorBlock).map factorBlockValue).prod = 104885372978717557351 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyFourV_2
      · exact prime_twentyFourV_3
      · exact prime_twentyFourV_5
      · exact prime_twentyFourV_19
      · exact prime_twentyFourV_97
      · exact prime_twentyFourV_62011
      · exact prime_twentyFourV_6118283513
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 104885372978717557351) ^ 52442686489358778675 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (6 : ZMod 104885372978717557351) ^ 34961790992905852450 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (6 : ZMod 104885372978717557351) ^ 20977074595743511470 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (6 : ZMod 104885372978717557351) ^ 5520282788353555650 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (6 : ZMod 104885372978717557351) ^ 1081292504935232550 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (6 : ZMod 104885372978717557351) ^ 1691399477168850 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (6 : ZMod 104885372978717557351) ^ 17142940950 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide

private theorem prime_twentyFourV_450387384420122768575756801 : Nat.Prime 450387384420122768575756801 := by
  apply lucas_primality 450387384420122768575756801 (101 : ZMod 450387384420122768575756801)
  · rw [← twentyFourVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 9), (3, 2), (5, 2), (7, 1), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 9), (3, 2), (5, 2), (7, 1), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod = 450387384420122768575756801 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyFourV_2
      · exact prime_twentyFourV_3
      · exact prime_twentyFourV_5
      · exact prime_twentyFourV_7
      · exact prime_twentyFourV_11
      · exact prime_twentyFourV_13
      · exact prime_twentyFourV_17
      · exact prime_twentyFourV_19
      · exact prime_twentyFourV_23
      · exact prime_twentyFourV_29
      · exact prime_twentyFourV_31
      · exact prime_twentyFourV_37
      · exact prime_twentyFourV_41
      · exact prime_twentyFourV_43
      · exact prime_twentyFourV_47
      · exact prime_twentyFourV_53
      · exact prime_twentyFourV_59
      · exact prime_twentyFourV_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (101 : ZMod 450387384420122768575756801) ^ 225193692210061384287878400 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (101 : ZMod 450387384420122768575756801) ^ 150129128140040922858585600 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (101 : ZMod 450387384420122768575756801) ^ 90077476884024553715151360 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (101 : ZMod 450387384420122768575756801) ^ 64341054917160395510822400 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (101 : ZMod 450387384420122768575756801) ^ 40944307674556615325068800 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (101 : ZMod 450387384420122768575756801) ^ 34645183416932520659673600 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (101 : ZMod 450387384420122768575756801) ^ 26493375554124868739750400 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (101 : ZMod 450387384420122768575756801) ^ 23704599180006461503987200 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (101 : ZMod 450387384420122768575756801) ^ 19582060192179250807641600 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (101 : ZMod 450387384420122768575756801) ^ 15530599462762854088819200 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (101 : ZMod 450387384420122768575756801) ^ 14528625303874928018572800 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (101 : ZMod 450387384420122768575756801) ^ 12172632011354669420966400 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (101 : ZMod 450387384420122768575756801) ^ 10985058156588360209164800 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (101 : ZMod 450387384420122768575756801) ^ 10474125219072622525017600 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (101 : ZMod 450387384420122768575756801) ^ 9582710306811122735654400 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (101 : ZMod 450387384420122768575756801) ^ 8497875177738165444825600 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (101 : ZMod 450387384420122768575756801) ^ 7633684481696996077555200 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (101 : ZMod 450387384420122768575756801) ^ 7383399744592176534028800 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide

private theorem prime_twentyFourV_55249 : Nat.Prime 55249 := by norm_num
private theorem prime_twentyFourV_157429 : Nat.Prime 157429 := by norm_num
private theorem prime_twentyFourV_773027 : Nat.Prime 773027 := by norm_num
private theorem prime_twentyFourV_17678041 : Nat.Prime 17678041 := by norm_num
private theorem prime_twentyFourV_176780411 : Nat.Prime 176780411 := by
  apply lucas_primality 176780411 (2 : ZMod 176780411)
  · rw [← twentyFourVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 1), (17678041, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 1), (17678041, 1)] : List FactorBlock).map factorBlockValue).prod = 176780411 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twentyFourV_2
      · exact prime_twentyFourV_5
      · exact prime_twentyFourV_17678041
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 176780411) ^ 88390205 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (2 : ZMod 176780411) ^ 35356082 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (2 : ZMod 176780411) ^ 10 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide

private theorem prime_twentyFourV_436529311053349760311887361 : Nat.Prime 436529311053349760311887361 := by
  apply lucas_primality 436529311053349760311887361 (26 : ZMod 436529311053349760311887361)
  · rw [← twentyFourVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 9), (3, 4), (5, 1), (7, 2), (11, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 9), (3, 4), (5, 1), (7, 2), (11, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod = 436529311053349760311887361 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyFourV_2
      · exact prime_twentyFourV_3
      · exact prime_twentyFourV_5
      · exact prime_twentyFourV_7
      · exact prime_twentyFourV_11
      · exact prime_twentyFourV_17
      · exact prime_twentyFourV_19
      · exact prime_twentyFourV_23
      · exact prime_twentyFourV_29
      · exact prime_twentyFourV_31
      · exact prime_twentyFourV_37
      · exact prime_twentyFourV_41
      · exact prime_twentyFourV_43
      · exact prime_twentyFourV_47
      · exact prime_twentyFourV_53
      · exact prime_twentyFourV_59
      · exact prime_twentyFourV_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (26 : ZMod 436529311053349760311887361) ^ 218264655526674880155943680 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (26 : ZMod 436529311053349760311887361) ^ 145509770351116586770629120 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (26 : ZMod 436529311053349760311887361) ^ 87305862210669952062377472 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (26 : ZMod 436529311053349760311887361) ^ 62361330150478537187412480 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (26 : ZMod 436529311053349760311887361) ^ 39684482823031796391989760 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (26 : ZMod 436529311053349760311887361) ^ 25678194767844103547758080 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (26 : ZMod 436529311053349760311887361) ^ 22975226897544724226941440 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (26 : ZMod 436529311053349760311887361) ^ 18979535263189120013560320 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (26 : ZMod 436529311053349760311887361) ^ 15052734863908612424547840 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (26 : ZMod 436529311053349760311887361) ^ 14081590679140314848770560 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (26 : ZMod 436529311053349760311887361) ^ 11798089487928371900321280 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (26 : ZMod 436529311053349760311887361) ^ 10647056367154872202728960 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (26 : ZMod 436529311053349760311887361) ^ 10151844443101157216555520 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (26 : ZMod 436529311053349760311887361) ^ 9287857681986165113018880 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (26 : ZMod 436529311053349760311887361) ^ 8236402095346221892677120 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (26 : ZMod 436529311053349760311887361) ^ 7398801882260165429015040 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (26 : ZMod 436529311053349760311887361) ^ 7156218213989340332981760 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide

private theorem prime_twentyFourV_5573 : Nat.Prime 5573 := by norm_num
private theorem prime_twentyFourV_12097 : Nat.Prime 12097 := by norm_num
private theorem prime_twentyFourV_133260553 : Nat.Prime 133260553 := by
  apply lucas_primality 133260553 (7 : ZMod 133260553)
  · rw [← twentyFourVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (3, 4), (17, 1), (12097, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (3, 4), (17, 1), (12097, 1)] : List FactorBlock).map factorBlockValue).prod = 133260553 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyFourV_2
      · exact prime_twentyFourV_3
      · exact prime_twentyFourV_17
      · exact prime_twentyFourV_12097
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 133260553) ^ 66630276 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (7 : ZMod 133260553) ^ 44420184 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (7 : ZMod 133260553) ^ 7838856 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (7 : ZMod 133260553) ^ 11016 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide

private theorem prime_twentyFourV_3198253273 : Nat.Prime 3198253273 := by
  apply lucas_primality 3198253273 (7 : ZMod 3198253273)
  · rw [← twentyFourVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (3, 1), (133260553, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (3, 1), (133260553, 1)] : List FactorBlock).map factorBlockValue).prod = 3198253273 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twentyFourV_2
      · exact prime_twentyFourV_3
      · exact prime_twentyFourV_133260553
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 3198253273) ^ 1599126636 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (7 : ZMod 3198253273) ^ 1066084424 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (7 : ZMod 3198253273) ^ 24 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide

private theorem prime_twentyFourV_9739 : Nat.Prime 9739 := by norm_num
private theorem prime_twentyFourV_60427 : Nat.Prime 60427 := by norm_num
private theorem prime_twentyFourV_2192745608479 : Nat.Prime 2192745608479 := by
  apply lucas_primality 2192745608479 (6 : ZMod 2192745608479)
  · rw [← twentyFourVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 4), (23, 1), (9739, 1), (60427, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 4), (23, 1), (9739, 1), (60427, 1)] : List FactorBlock).map factorBlockValue).prod = 2192745608479 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyFourV_2
      · exact prime_twentyFourV_3
      · exact prime_twentyFourV_23
      · exact prime_twentyFourV_9739
      · exact prime_twentyFourV_60427
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 2192745608479) ^ 1096372804239 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (6 : ZMod 2192745608479) ^ 730915202826 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (6 : ZMod 2192745608479) ^ 95336765586 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (6 : ZMod 2192745608479) ^ 225151002 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (6 : ZMod 2192745608479) ^ 36287514 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide

private theorem prime_twentyFourV_399639510119263865074263077 : Nat.Prime 399639510119263865074263077 := by
  apply lucas_primality 399639510119263865074263077 (2 : ZMod 399639510119263865074263077)
  · rw [← twentyFourVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (11633, 1), (8588487709947216218393, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (11633, 1), (8588487709947216218393, 1)] : List FactorBlock).map factorBlockValue).prod = 399639510119263865074263077 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twentyFourV_2
      · exact prime_twentyFourV_11633
      · exact prime_twentyFourV_8588487709947216218393
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 399639510119263865074263077) ^ 199819755059631932537131538 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (2 : ZMod 399639510119263865074263077) ^ 34353950839788864873572 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (2 : ZMod 399639510119263865074263077) ^ 46532 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide

private theorem prime_twentyFourV_1567 : Nat.Prime 1567 := by norm_num
private theorem prime_twentyFourV_4969 : Nat.Prime 4969 := by norm_num
private theorem prime_twentyFourV_10103311 : Nat.Prime 10103311 := by norm_num
private theorem prime_twentyFourV_32429 : Nat.Prime 32429 := by norm_num
private theorem prime_twentyFourV_38287 : Nat.Prime 38287 := by norm_num
private theorem prime_twentyFourV_7449654739 : Nat.Prime 7449654739 := by
  apply lucas_primality 7449654739 (2 : ZMod 7449654739)
  · rw [← twentyFourVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (32429, 1), (38287, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (32429, 1), (38287, 1)] : List FactorBlock).map factorBlockValue).prod = 7449654739 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyFourV_2
      · exact prime_twentyFourV_3
      · exact prime_twentyFourV_32429
      · exact prime_twentyFourV_38287
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 7449654739) ^ 3724827369 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (2 : ZMod 7449654739) ^ 2483218246 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (2 : ZMod 7449654739) ^ 229722 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (2 : ZMod 7449654739) ^ 194574 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide

private theorem prime_twentyFourV_29798618957 : Nat.Prime 29798618957 := by
  apply lucas_primality 29798618957 (2 : ZMod 29798618957)
  · rw [← twentyFourVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (7449654739, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (7449654739, 1)] : List FactorBlock).map factorBlockValue).prod = 29798618957 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_twentyFourV_2
      · exact prime_twentyFourV_7449654739
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 29798618957) ^ 14899309478 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (2 : ZMod 29798618957) ^ 4 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide

private theorem prime_twentyFourV_2991981134619696139127 : Nat.Prime 2991981134619696139127 := by
  apply lucas_primality 2991981134619696139127 (5 : ZMod 2991981134619696139127)
  · rw [← twentyFourVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (4969, 1), (10103311, 1), (29798618957, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (4969, 1), (10103311, 1), (29798618957, 1)] : List FactorBlock).map factorBlockValue).prod = 2991981134619696139127 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyFourV_2
      · exact prime_twentyFourV_4969
      · exact prime_twentyFourV_10103311
      · exact prime_twentyFourV_29798618957
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 2991981134619696139127) ^ 1495990567309848069563 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (5 : ZMod 2991981134619696139127) ^ 602129429386133254 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (5 : ZMod 2991981134619696139127) ^ 296138675194666 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (5 : ZMod 2991981134619696139127) ^ 100406704718 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide

private theorem prime_twentyFourV_137 : Nat.Prime 137 := by norm_num
private theorem prime_twentyFourV_656023 : Nat.Prime 656023 := by norm_num
private theorem prime_twentyFourV_224359867 : Nat.Prime 224359867 := by
  apply lucas_primality 224359867 (2 : ZMod 224359867)
  · rw [← twentyFourVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 2), (19, 1), (656023, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 2), (19, 1), (656023, 1)] : List FactorBlock).map factorBlockValue).prod = 224359867 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyFourV_2
      · exact prime_twentyFourV_3
      · exact prime_twentyFourV_19
      · exact prime_twentyFourV_656023
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 224359867) ^ 112179933 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (2 : ZMod 224359867) ^ 74786622 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (2 : ZMod 224359867) ^ 11808414 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (2 : ZMod 224359867) ^ 342 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide

private theorem prime_twentyFourV_103393 : Nat.Prime 103393 := by norm_num
private theorem prime_twentyFourV_15857351 : Nat.Prime 15857351 := by norm_num
private theorem prime_twentyFourV_98372345516581 : Nat.Prime 98372345516581 := by
  apply lucas_primality 98372345516581 (2 : ZMod 98372345516581)
  · rw [← twentyFourVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (5, 1), (103393, 1), (15857351, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (5, 1), (103393, 1), (15857351, 1)] : List FactorBlock).map factorBlockValue).prod = 98372345516581 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyFourV_2
      · exact prime_twentyFourV_3
      · exact prime_twentyFourV_5
      · exact prime_twentyFourV_103393
      · exact prime_twentyFourV_15857351
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 98372345516581) ^ 49186172758290 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (2 : ZMod 98372345516581) ^ 32790781838860 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (2 : ZMod 98372345516581) ^ 19674469103316 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (2 : ZMod 98372345516581) ^ 951441060 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (2 : ZMod 98372345516581) ^ 6203580 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide

private theorem prime_twentyFourV_3001629664494629685842873 : Nat.Prime 3001629664494629685842873 := by
  apply lucas_primality 3001629664494629685842873 (3 : ZMod 3001629664494629685842873)
  · rw [← twentyFourVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (17, 1), (224359867, 1), (98372345516581, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (17, 1), (224359867, 1), (98372345516581, 1)] : List FactorBlock).map factorBlockValue).prod = 3001629664494629685842873 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyFourV_2
      · exact prime_twentyFourV_17
      · exact prime_twentyFourV_224359867
      · exact prime_twentyFourV_98372345516581
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 3001629664494629685842873) ^ 1500814832247314842921436 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (3 : ZMod 3001629664494629685842873) ^ 176566450852625275637816 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (3 : ZMod 3001629664494629685842873) ^ 13378638990255016 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (3 : ZMod 3001629664494629685842873) ^ 30512941912 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide

private theorem prime_twentyFourV_10103 : Nat.Prime 10103 := by norm_num
private theorem prime_twentyFourV_743 : Nat.Prime 743 := by norm_num
private theorem prime_twentyFourV_937 : Nat.Prime 937 := by norm_num
private theorem prime_twentyFourV_7487 : Nat.Prime 7487 := by norm_num
private theorem prime_twentyFourV_1466551 : Nat.Prime 1466551 := by norm_num
private theorem prime_twentyFourV_2624309 : Nat.Prime 2624309 := by norm_num
private theorem prime_twentyFourV_40121611994270067476807 : Nat.Prime 40121611994270067476807 := by
  apply lucas_primality 40121611994270067476807 (5 : ZMod 40121611994270067476807)
  · rw [← twentyFourVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (743, 1), (937, 1), (7487, 1), (1466551, 1), (2624309, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (743, 1), (937, 1), (7487, 1), (1466551, 1), (2624309, 1)] : List FactorBlock).map factorBlockValue).prod = 40121611994270067476807 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyFourV_2
      · exact prime_twentyFourV_743
      · exact prime_twentyFourV_937
      · exact prime_twentyFourV_7487
      · exact prime_twentyFourV_1466551
      · exact prime_twentyFourV_2624309
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 40121611994270067476807) ^ 20060805997135033738403 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (5 : ZMod 40121611994270067476807) ^ 53999477785020279242 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (5 : ZMod 40121611994270067476807) ^ 42819223046179367638 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (5 : ZMod 40121611994270067476807) ^ 5358836916558042938 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (5 : ZMod 40121611994270067476807) ^ 27357802077302506 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (5 : ZMod 40121611994270067476807) ^ 15288448118826734 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide

private theorem prime_twentyFourV_2385211 : Nat.Prime 2385211 := by norm_num
private theorem prime_twentyFourV_17041 : Nat.Prime 17041 := by norm_num
private theorem prime_twentyFourV_144659 : Nat.Prime 144659 := by norm_num
private theorem prime_twentyFourV_16713460740778861 : Nat.Prime 16713460740778861 := by
  apply lucas_primality 16713460740778861 (6 : ZMod 16713460740778861)
  · rw [← twentyFourVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (5, 1), (17, 3), (23, 1), (17041, 1), (144659, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (5, 1), (17, 3), (23, 1), (17041, 1), (144659, 1)] : List FactorBlock).map factorBlockValue).prod = 16713460740778861 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyFourV_2
      · exact prime_twentyFourV_3
      · exact prime_twentyFourV_5
      · exact prime_twentyFourV_17
      · exact prime_twentyFourV_23
      · exact prime_twentyFourV_17041
      · exact prime_twentyFourV_144659
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 16713460740778861) ^ 8356730370389430 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (6 : ZMod 16713460740778861) ^ 5571153580259620 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (6 : ZMod 16713460740778861) ^ 3342692148155772 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (6 : ZMod 16713460740778861) ^ 983144749457580 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (6 : ZMod 16713460740778861) ^ 726672206120820 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (6 : ZMod 16713460740778861) ^ 980779340460 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (6 : ZMod 16713460740778861) ^ 115536957540 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide

private theorem prime_twentyFourV_1370503780743866603 : Nat.Prime 1370503780743866603 := by
  apply lucas_primality 1370503780743866603 (2 : ZMod 1370503780743866603)
  · rw [← twentyFourVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (41, 1), (16713460740778861, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (41, 1), (16713460740778861, 1)] : List FactorBlock).map factorBlockValue).prod = 1370503780743866603 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twentyFourV_2
      · exact prime_twentyFourV_41
      · exact prime_twentyFourV_16713460740778861
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 1370503780743866603) ^ 685251890371933301 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (2 : ZMod 1370503780743866603) ^ 33426921481557722 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (2 : ZMod 1370503780743866603) ^ 82 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide

private theorem prime_twentyFourV_19187052930414132443 : Nat.Prime 19187052930414132443 := by
  apply lucas_primality 19187052930414132443 (2 : ZMod 19187052930414132443)
  · rw [← twentyFourVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (7, 1), (1370503780743866603, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (7, 1), (1370503780743866603, 1)] : List FactorBlock).map factorBlockValue).prod = 19187052930414132443 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twentyFourV_2
      · exact prime_twentyFourV_7
      · exact prime_twentyFourV_1370503780743866603
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 19187052930414132443) ^ 9593526465207066221 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (2 : ZMod 19187052930414132443) ^ 2741007561487733206 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (2 : ZMod 19187052930414132443) ^ 14 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide

private theorem prime_twentyFourV_11895972816856762114661 : Nat.Prime 11895972816856762114661 := by
  apply lucas_primality 11895972816856762114661 (2 : ZMod 11895972816856762114661)
  · rw [← twentyFourVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (5, 1), (31, 1), (19187052930414132443, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (5, 1), (31, 1), (19187052930414132443, 1)] : List FactorBlock).map factorBlockValue).prod = 11895972816856762114661 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyFourV_2
      · exact prime_twentyFourV_5
      · exact prime_twentyFourV_31
      · exact prime_twentyFourV_19187052930414132443
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 11895972816856762114661) ^ 5947986408428381057330 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (2 : ZMod 11895972816856762114661) ^ 2379194563371352422932 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (2 : ZMod 11895972816856762114661) ^ 383741058608282648860 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (2 : ZMod 11895972816856762114661) ^ 620 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide

private theorem prime_twentyFourV_394088961367607422503787201 : Nat.Prime 394088961367607422503787201 := by
  apply lucas_primality 394088961367607422503787201 (103 : ZMod 394088961367607422503787201)
  · rw [← twentyFourVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 6), (3, 2), (5, 2), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 6), (3, 2), (5, 2), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod = 394088961367607422503787201 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyFourV_2
      · exact prime_twentyFourV_3
      · exact prime_twentyFourV_5
      · exact prime_twentyFourV_7
      · exact prime_twentyFourV_11
      · exact prime_twentyFourV_13
      · exact prime_twentyFourV_17
      · exact prime_twentyFourV_19
      · exact prime_twentyFourV_23
      · exact prime_twentyFourV_29
      · exact prime_twentyFourV_31
      · exact prime_twentyFourV_37
      · exact prime_twentyFourV_41
      · exact prime_twentyFourV_43
      · exact prime_twentyFourV_47
      · exact prime_twentyFourV_53
      · exact prime_twentyFourV_59
      · exact prime_twentyFourV_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (103 : ZMod 394088961367607422503787201) ^ 197044480683803711251893600 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 131362987122535807501262400 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 78817792273521484500757440 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 56298423052515346071969600 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 35826269215237038409435200 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 30314535489815955577214400 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 23181703609859260147281600 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 20741524282505653815988800 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 17134302668156844456686400 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 13589274529917497327716800 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 12712547140890562016251200 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 10651053009935335743345600 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 9611925887014815183019200 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 9164859566688544709390400 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 8384871518459732393697600 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 7435640780520894764222400 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 6679473921484871567860800 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 6460474776518154467275200 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide

private theorem prime_twentyFourV_15271 : Nat.Prime 15271 := by norm_num
private theorem prime_twentyFourV_1861 : Nat.Prime 1861 := by norm_num
private theorem prime_twentyFourV_119677 : Nat.Prime 119677 := by norm_num
private theorem prime_twentyFourV_890875589 : Nat.Prime 890875589 := by
  apply lucas_primality 890875589 (2 : ZMod 890875589)
  · rw [← twentyFourVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (1861, 1), (119677, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (1861, 1), (119677, 1)] : List FactorBlock).map factorBlockValue).prod = 890875589 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twentyFourV_2
      · exact prime_twentyFourV_1861
      · exact prime_twentyFourV_119677
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 890875589) ^ 445437794 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (2 : ZMod 890875589) ^ 478708 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (2 : ZMod 890875589) ^ 7444 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide

private theorem prime_twentyFourV_8191 : Nat.Prime 8191 := by norm_num
private theorem prime_twentyFourV_31333 : Nat.Prime 31333 := by norm_num
private theorem prime_twentyFourV_59542475897 : Nat.Prime 59542475897 := by
  apply lucas_primality 59542475897 (3 : ZMod 59542475897)
  · rw [← twentyFourVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (29, 1), (8191, 1), (31333, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (29, 1), (8191, 1), (31333, 1)] : List FactorBlock).map factorBlockValue).prod = 59542475897 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyFourV_2
      · exact prime_twentyFourV_29
      · exact prime_twentyFourV_8191
      · exact prime_twentyFourV_31333
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 59542475897) ^ 29771237948 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (3 : ZMod 59542475897) ^ 2053188824 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (3 : ZMod 59542475897) ^ 7269256 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (3 : ZMod 59542475897) ^ 1900312 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide

private theorem prime_twentyFourV_13367324447885060939917 : Nat.Prime 13367324447885060939917 := by
  apply lucas_primality 13367324447885060939917 (2 : ZMod 13367324447885060939917)
  · rw [← twentyFourVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 2), (7, 1), (890875589, 1), (59542475897, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 2), (7, 1), (890875589, 1), (59542475897, 1)] : List FactorBlock).map factorBlockValue).prod = 13367324447885060939917 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyFourV_2
      · exact prime_twentyFourV_3
      · exact prime_twentyFourV_7
      · exact prime_twentyFourV_890875589
      · exact prime_twentyFourV_59542475897
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 13367324447885060939917) ^ 6683662223942530469958 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (2 : ZMod 13367324447885060939917) ^ 4455774815961686979972 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (2 : ZMod 13367324447885060939917) ^ 1909617778269294419988 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (2 : ZMod 13367324447885060939917) ^ 15004703926044 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (2 : ZMod 13367324447885060939917) ^ 224500648428 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide

private theorem prime_twentyFourV_10124467 : Nat.Prime 10124467 := by norm_num
private theorem prime_twentyFourV_263 : Nat.Prime 263 := by norm_num
private theorem prime_twentyFourV_16361 : Nat.Prime 16361 := by norm_num
private theorem prime_twentyFourV_68639 : Nat.Prime 68639 := by norm_num
private theorem prime_twentyFourV_1606701713 : Nat.Prime 1606701713 := by
  apply lucas_primality 1606701713 (5 : ZMod 1606701713)
  · rw [← twentyFourVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 4), (7, 1), (11, 1), (19, 1), (68639, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 4), (7, 1), (11, 1), (19, 1), (68639, 1)] : List FactorBlock).map factorBlockValue).prod = 1606701713 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyFourV_2
      · exact prime_twentyFourV_7
      · exact prime_twentyFourV_11
      · exact prime_twentyFourV_19
      · exact prime_twentyFourV_68639
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 1606701713) ^ 803350856 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (5 : ZMod 1606701713) ^ 229528816 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (5 : ZMod 1606701713) ^ 146063792 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (5 : ZMod 1606701713) ^ 84563248 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (5 : ZMod 1606701713) ^ 23408 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide

private theorem prime_twentyFourV_37872404380168564603 : Nat.Prime 37872404380168564603 := by
  apply lucas_primality 37872404380168564603 (2 : ZMod 37872404380168564603)
  · rw [← twentyFourVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (11, 1), (83, 1), (263, 1), (16361, 1), (1606701713, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (11, 1), (83, 1), (263, 1), (16361, 1), (1606701713, 1)] : List FactorBlock).map factorBlockValue).prod = 37872404380168564603 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyFourV_2
      · exact prime_twentyFourV_3
      · exact prime_twentyFourV_11
      · exact prime_twentyFourV_83
      · exact prime_twentyFourV_263
      · exact prime_twentyFourV_16361
      · exact prime_twentyFourV_1606701713
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 37872404380168564603) ^ 18936202190084282301 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (2 : ZMod 37872404380168564603) ^ 12624134793389521534 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (2 : ZMod 37872404380168564603) ^ 3442945852742596782 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (2 : ZMod 37872404380168564603) ^ 456294028676729694 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (2 : ZMod 37872404380168564603) ^ 144001537567180854 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (2 : ZMod 37872404380168564603) ^ 2314797651743082 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (2 : ZMod 37872404380168564603) ^ 23571521754 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide

private theorem prime_twentyFourV_863 : Nat.Prime 863 := by norm_num
private theorem prime_twentyFourV_221461 : Nat.Prime 221461 := by norm_num
private theorem prime_twentyFourV_77954273 : Nat.Prime 77954273 := by
  apply lucas_primality 77954273 (3 : ZMod 77954273)
  · rw [← twentyFourVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 5), (11, 1), (221461, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 5), (11, 1), (221461, 1)] : List FactorBlock).map factorBlockValue).prod = 77954273 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twentyFourV_2
      · exact prime_twentyFourV_11
      · exact prime_twentyFourV_221461
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 77954273) ^ 38977136 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (3 : ZMod 77954273) ^ 7086752 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (3 : ZMod 77954273) ^ 352 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide

private theorem prime_twentyFourV_935451277 : Nat.Prime 935451277 := by
  apply lucas_primality 935451277 (5 : ZMod 935451277)
  · rw [← twentyFourVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (77954273, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (77954273, 1)] : List FactorBlock).map factorBlockValue).prod = 935451277 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twentyFourV_2
      · exact prime_twentyFourV_3
      · exact prime_twentyFourV_77954273
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 935451277) ^ 467725638 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (5 : ZMod 935451277) ^ 311817092 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (5 : ZMod 935451277) ^ 12 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide

private theorem prime_twentyFourV_887 : Nat.Prime 887 := by norm_num
private theorem prime_twentyFourV_120049 : Nat.Prime 120049 := by norm_num
private theorem prime_twentyFourV_2129669261 : Nat.Prime 2129669261 := by
  apply lucas_primality 2129669261 (2 : ZMod 2129669261)
  · rw [← twentyFourVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (5, 1), (887, 1), (120049, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (5, 1), (887, 1), (120049, 1)] : List FactorBlock).map factorBlockValue).prod = 2129669261 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyFourV_2
      · exact prime_twentyFourV_5
      · exact prime_twentyFourV_887
      · exact prime_twentyFourV_120049
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 2129669261) ^ 1064834630 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (2 : ZMod 2129669261) ^ 425933852 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (2 : ZMod 2129669261) ^ 2400980 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (2 : ZMod 2129669261) ^ 17740 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide

private theorem prime_twentyFourV_2321014741796951690819851 : Nat.Prime 2321014741796951690819851 := by
  apply lucas_primality 2321014741796951690819851 (10 : ZMod 2321014741796951690819851)
  · rw [← twentyFourVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 3), (5, 2), (863, 1), (935451277, 1), (2129669261, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 3), (5, 2), (863, 1), (935451277, 1), (2129669261, 1)] : List FactorBlock).map factorBlockValue).prod = 2321014741796951690819851 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyFourV_2
      · exact prime_twentyFourV_3
      · exact prime_twentyFourV_5
      · exact prime_twentyFourV_863
      · exact prime_twentyFourV_935451277
      · exact prime_twentyFourV_2129669261
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 2321014741796951690819851) ^ 1160507370898475845409925 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (10 : ZMod 2321014741796951690819851) ^ 773671580598983896939950 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (10 : ZMod 2321014741796951690819851) ^ 464202948359390338163970 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (10 : ZMod 2321014741796951690819851) ^ 2689472470216630000950 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (10 : ZMod 2321014741796951690819851) ^ 2481171172528050 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (10 : ZMod 2321014741796951690819851) ^ 1089847510268850 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide

private theorem prime_twentyFourV_2712337 : Nat.Prime 2712337 := by norm_num
private theorem prime_twentyFourV_2442113 : Nat.Prime 2442113 := by norm_num
private theorem prime_twentyFourV_21683 : Nat.Prime 21683 := by norm_num
private theorem prime_twentyFourV_106750482823 : Nat.Prime 106750482823 := by
  apply lucas_primality 106750482823 (3 : ZMod 106750482823)
  · rw [← twentyFourVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 3), (17, 1), (31, 1), (173, 1), (21683, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 3), (17, 1), (31, 1), (173, 1), (21683, 1)] : List FactorBlock).map factorBlockValue).prod = 106750482823 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyFourV_2
      · exact prime_twentyFourV_3
      · exact prime_twentyFourV_17
      · exact prime_twentyFourV_31
      · exact prime_twentyFourV_173
      · exact prime_twentyFourV_21683
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 106750482823) ^ 53375241411 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (3 : ZMod 106750482823) ^ 35583494274 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (3 : ZMod 106750482823) ^ 6279440166 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (3 : ZMod 106750482823) ^ 3443563962 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (3 : ZMod 106750482823) ^ 617054814 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (3 : ZMod 106750482823) ^ 4923234 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide

private theorem prime_twentyFourV_137647879701195599473 : Nat.Prime 137647879701195599473 := by
  apply lucas_primality 137647879701195599473 (5 : ZMod 137647879701195599473)
  · rw [← twentyFourVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 4), (3, 1), (11, 1), (2442113, 1), (106750482823, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 4), (3, 1), (11, 1), (2442113, 1), (106750482823, 1)] : List FactorBlock).map factorBlockValue).prod = 137647879701195599473 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyFourV_2
      · exact prime_twentyFourV_3
      · exact prime_twentyFourV_11
      · exact prime_twentyFourV_2442113
      · exact prime_twentyFourV_106750482823
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 137647879701195599473) ^ 68823939850597799736 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (5 : ZMod 137647879701195599473) ^ 45882626567065199824 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (5 : ZMod 137647879701195599473) ^ 12513443609199599952 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (5 : ZMod 137647879701195599473) ^ 56364254930544 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (5 : ZMod 137647879701195599473) ^ 1289435664 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide

private theorem prime_twentyFourV_1283 : Nat.Prime 1283 := by norm_num
private theorem prime_twentyFourV_7577 : Nat.Prime 7577 := by norm_num
private theorem prime_twentyFourV_13331 : Nat.Prime 13331 := by norm_num
private theorem prime_twentyFourV_1867 : Nat.Prime 1867 := by norm_num
private theorem prime_twentyFourV_7417 : Nat.Prime 7417 := by norm_num
private theorem prime_twentyFourV_82799 : Nat.Prime 82799 := by norm_num
private theorem prime_twentyFourV_2843474706519281 : Nat.Prime 2843474706519281 := by
  apply lucas_primality 2843474706519281 (11 : ZMod 2843474706519281)
  · rw [← twentyFourVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 4), (5, 1), (31, 1), (1867, 1), (7417, 1), (82799, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 4), (5, 1), (31, 1), (1867, 1), (7417, 1), (82799, 1)] : List FactorBlock).map factorBlockValue).prod = 2843474706519281 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyFourV_2
      · exact prime_twentyFourV_5
      · exact prime_twentyFourV_31
      · exact prime_twentyFourV_1867
      · exact prime_twentyFourV_7417
      · exact prime_twentyFourV_82799
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 2843474706519281) ^ 1421737353259640 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (11 : ZMod 2843474706519281) ^ 568694941303856 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (11 : ZMod 2843474706519281) ^ 91724990532880 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (11 : ZMod 2843474706519281) ^ 1523018053840 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (11 : ZMod 2843474706519281) ^ 383372617840 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (11 : ZMod 2843474706519281) ^ 34341896720 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide

private theorem prime_twentyFourV_251 : Nat.Prime 251 := by norm_num
private theorem prime_twentyFourV_1321 : Nat.Prime 1321 := by norm_num
private theorem prime_twentyFourV_1787 : Nat.Prime 1787 := by norm_num
private theorem prime_twentyFourV_1255074433 : Nat.Prime 1255074433 := by
  apply lucas_primality 1255074433 (10 : ZMod 1255074433)
  · rw [← twentyFourVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 7), (3, 1), (31, 1), (59, 1), (1787, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 7), (3, 1), (31, 1), (59, 1), (1787, 1)] : List FactorBlock).map factorBlockValue).prod = 1255074433 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyFourV_2
      · exact prime_twentyFourV_3
      · exact prime_twentyFourV_31
      · exact prime_twentyFourV_59
      · exact prime_twentyFourV_1787
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 1255074433) ^ 627537216 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (10 : ZMod 1255074433) ^ 418358144 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (10 : ZMod 1255074433) ^ 40486272 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (10 : ZMod 1255074433) ^ 21272448 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (10 : ZMod 1255074433) ^ 702336 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide

private theorem prime_twentyFourV_492979 : Nat.Prime 492979 := by norm_num
private theorem prime_twentyFourV_17483007257 : Nat.Prime 17483007257 := by
  apply lucas_primality 17483007257 (6 : ZMod 17483007257)
  · rw [← twentyFourVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (11, 1), (13, 1), (31, 1), (492979, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (11, 1), (13, 1), (31, 1), (492979, 1)] : List FactorBlock).map factorBlockValue).prod = 17483007257 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyFourV_2
      · exact prime_twentyFourV_11
      · exact prime_twentyFourV_13
      · exact prime_twentyFourV_31
      · exact prime_twentyFourV_492979
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 17483007257) ^ 8741503628 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (6 : ZMod 17483007257) ^ 1589364296 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (6 : ZMod 17483007257) ^ 1344846712 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (6 : ZMod 17483007257) ^ 563967976 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (6 : ZMod 17483007257) ^ 35464 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide

private theorem prime_twentyFourV_1449300501505145286560051 : Nat.Prime 1449300501505145286560051 := by
  apply lucas_primality 1449300501505145286560051 (6 : ZMod 1449300501505145286560051)
  · rw [← twentyFourVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 2), (1321, 1), (1255074433, 1), (17483007257, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 2), (1321, 1), (1255074433, 1), (17483007257, 1)] : List FactorBlock).map factorBlockValue).prod = 1449300501505145286560051 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyFourV_2
      · exact prime_twentyFourV_5
      · exact prime_twentyFourV_1321
      · exact prime_twentyFourV_1255074433
      · exact prime_twentyFourV_17483007257
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 1449300501505145286560051) ^ 724650250752572643280025 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (6 : ZMod 1449300501505145286560051) ^ 289860100301029057312010 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (6 : ZMod 1449300501505145286560051) ^ 1097123771010708014050 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (6 : ZMod 1449300501505145286560051) ^ 1154752629324850 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (6 : ZMod 1449300501505145286560051) ^ 82897666299650 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide

private theorem prime_twentyFourV_359 : Nat.Prime 359 := by norm_num
private theorem prime_twentyFourV_460217 : Nat.Prime 460217 := by norm_num
private theorem prime_twentyFourV_1052438042111 : Nat.Prime 1052438042111 := by
  apply lucas_primality 1052438042111 (11 : ZMod 1052438042111)
  · rw [← twentyFourVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 1), (7, 2), (13, 1), (359, 1), (460217, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 1), (7, 2), (13, 1), (359, 1), (460217, 1)] : List FactorBlock).map factorBlockValue).prod = 1052438042111 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyFourV_2
      · exact prime_twentyFourV_5
      · exact prime_twentyFourV_7
      · exact prime_twentyFourV_13
      · exact prime_twentyFourV_359
      · exact prime_twentyFourV_460217
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 1052438042111) ^ 526219021055 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (11 : ZMod 1052438042111) ^ 210487608422 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (11 : ZMod 1052438042111) ^ 150348291730 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (11 : ZMod 1052438042111) ^ 80956772470 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (11 : ZMod 1052438042111) ^ 2931582290 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (11 : ZMod 1052438042111) ^ 2286830 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide

private theorem prime_twentyFourV_4870651 : Nat.Prime 4870651 := by norm_num
private theorem prime_twentyFourV_613702027 : Nat.Prime 613702027 := by
  apply lucas_primality 613702027 (2 : ZMod 613702027)
  · rw [← twentyFourVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 2), (7, 1), (4870651, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 2), (7, 1), (4870651, 1)] : List FactorBlock).map factorBlockValue).prod = 613702027 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyFourV_2
      · exact prime_twentyFourV_3
      · exact prime_twentyFourV_7
      · exact prime_twentyFourV_4870651
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 613702027) ^ 306851013 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (2 : ZMod 613702027) ^ 204567342 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (2 : ZMod 613702027) ^ 87671718 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (2 : ZMod 613702027) ^ 126 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide

private theorem prime_twentyFourV_47868758107 : Nat.Prime 47868758107 := by
  apply lucas_primality 47868758107 (7 : ZMod 47868758107)
  · rw [← twentyFourVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (13, 1), (613702027, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (13, 1), (613702027, 1)] : List FactorBlock).map factorBlockValue).prod = 47868758107 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyFourV_2
      · exact prime_twentyFourV_3
      · exact prime_twentyFourV_13
      · exact prime_twentyFourV_613702027
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 47868758107) ^ 23934379053 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (7 : ZMod 47868758107) ^ 15956252702 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (7 : ZMod 47868758107) ^ 3682212162 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (7 : ZMod 47868758107) ^ 78 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide

private theorem prime_twentyFourV_180943905644461 : Nat.Prime 180943905644461 := by
  apply lucas_primality 180943905644461 (10 : ZMod 180943905644461)
  · rw [← twentyFourVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 3), (5, 1), (7, 1), (47868758107, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 3), (5, 1), (7, 1), (47868758107, 1)] : List FactorBlock).map factorBlockValue).prod = 180943905644461 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyFourV_2
      · exact prime_twentyFourV_3
      · exact prime_twentyFourV_5
      · exact prime_twentyFourV_7
      · exact prime_twentyFourV_47868758107
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 180943905644461) ^ 90471952822230 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (10 : ZMod 180943905644461) ^ 60314635214820 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (10 : ZMod 180943905644461) ^ 36188781128892 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (10 : ZMod 180943905644461) ^ 25849129377780 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (10 : ZMod 180943905644461) ^ 3780 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide

private theorem prime_twentyFourV_180533 : Nat.Prime 180533 := by norm_num
private theorem prime_twentyFourV_2161 : Nat.Prime 2161 := by norm_num
private theorem prime_twentyFourV_8537 : Nat.Prime 8537 := by norm_num
private theorem prime_twentyFourV_561521 : Nat.Prime 561521 := by norm_num
private theorem prime_twentyFourV_19518469961 : Nat.Prime 19518469961 := by
  apply lucas_primality 19518469961 (3 : ZMod 19518469961)
  · rw [← twentyFourVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (5, 1), (11, 1), (79, 1), (561521, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (5, 1), (11, 1), (79, 1), (561521, 1)] : List FactorBlock).map factorBlockValue).prod = 19518469961 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyFourV_2
      · exact prime_twentyFourV_5
      · exact prime_twentyFourV_11
      · exact prime_twentyFourV_79
      · exact prime_twentyFourV_561521
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 19518469961) ^ 9759234980 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (3 : ZMod 19518469961) ^ 3903693992 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (3 : ZMod 19518469961) ^ 1774406360 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (3 : ZMod 19518469961) ^ 247069240 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (3 : ZMod 19518469961) ^ 34760 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide

private theorem prime_twentyFourV_44650621068881221949 : Nat.Prime 44650621068881221949 := by
  apply lucas_primality 44650621068881221949 (2 : ZMod 44650621068881221949)
  · rw [← twentyFourVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (31, 1), (2161, 1), (8537, 1), (19518469961, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (31, 1), (2161, 1), (8537, 1), (19518469961, 1)] : List FactorBlock).map factorBlockValue).prod = 44650621068881221949 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyFourV_2
      · exact prime_twentyFourV_31
      · exact prime_twentyFourV_2161
      · exact prime_twentyFourV_8537
      · exact prime_twentyFourV_19518469961
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 44650621068881221949) ^ 22325310534440610974 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (2 : ZMod 44650621068881221949) ^ 1440342615125200708 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (2 : ZMod 44650621068881221949) ^ 20662018079075068 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (2 : ZMod 44650621068881221949) ^ 5230247284629404 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (2 : ZMod 44650621068881221949) ^ 2287608668 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide

private theorem prime_twentyFourV_1964627327030773765757 : Nat.Prime 1964627327030773765757 := by
  apply lucas_primality 1964627327030773765757 (3 : ZMod 1964627327030773765757)
  · rw [← twentyFourVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (11, 1), (44650621068881221949, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (11, 1), (44650621068881221949, 1)] : List FactorBlock).map factorBlockValue).prod = 1964627327030773765757 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twentyFourV_2
      · exact prime_twentyFourV_11
      · exact prime_twentyFourV_44650621068881221949
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 1964627327030773765757) ^ 982313663515386882878 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (3 : ZMod 1964627327030773765757) ^ 178602484275524887796 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (3 : ZMod 1964627327030773765757) ^ 44 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide

private theorem prime_twentyFourV_307381 : Nat.Prime 307381 := by norm_num
private theorem prime_twentyFourV_234103828649 : Nat.Prime 234103828649 := by
  apply lucas_primality 234103828649 (3 : ZMod 234103828649)
  · rw [← twentyFourVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (31, 1), (37, 1), (83, 1), (307381, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (31, 1), (37, 1), (83, 1), (307381, 1)] : List FactorBlock).map factorBlockValue).prod = 234103828649 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyFourV_2
      · exact prime_twentyFourV_31
      · exact prime_twentyFourV_37
      · exact prime_twentyFourV_83
      · exact prime_twentyFourV_307381
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 234103828649) ^ 117051914324 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (3 : ZMod 234103828649) ^ 7551736408 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (3 : ZMod 234103828649) ^ 6327130504 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (3 : ZMod 234103828649) ^ 2820528056 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (3 : ZMod 234103828649) ^ 761608 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide

private theorem prime_twentyFourV_35461 : Nat.Prime 35461 := by norm_num
private theorem prime_twentyFourV_97678393 : Nat.Prime 97678393 := by
  apply lucas_primality 97678393 (11 : ZMod 97678393)
  · rw [← twentyFourVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (3, 1), (7, 1), (19, 1), (71, 1), (431, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (3, 1), (7, 1), (19, 1), (71, 1), (431, 1)] : List FactorBlock).map factorBlockValue).prod = 97678393 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyFourV_2
      · exact prime_twentyFourV_3
      · exact prime_twentyFourV_7
      · exact prime_twentyFourV_19
      · exact prime_twentyFourV_71
      · exact prime_twentyFourV_431
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 97678393) ^ 48839196 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (11 : ZMod 97678393) ^ 32559464 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (11 : ZMod 97678393) ^ 13954056 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (11 : ZMod 97678393) ^ 5140968 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (11 : ZMod 97678393) ^ 1375752 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (11 : ZMod 97678393) ^ 226632 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide

private theorem prime_twentyFourV_20782640965039 : Nat.Prime 20782640965039 := by
  apply lucas_primality 20782640965039 (3 : ZMod 20782640965039)
  · rw [← twentyFourVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (35461, 1), (97678393, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (35461, 1), (97678393, 1)] : List FactorBlock).map factorBlockValue).prod = 20782640965039 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyFourV_2
      · exact prime_twentyFourV_3
      · exact prime_twentyFourV_35461
      · exact prime_twentyFourV_97678393
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 20782640965039) ^ 10391320482519 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (3 : ZMod 20782640965039) ^ 6927546988346 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (3 : ZMod 20782640965039) ^ 586070358 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (3 : ZMod 20782640965039) ^ 212766 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide

private theorem prime_twentyFourV_38922366554825424444818489 : Nat.Prime 38922366554825424444818489 := by
  apply lucas_primality 38922366554825424444818489 (3 : ZMod 38922366554825424444818489)
  · rw [← twentyFourVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (234103828649, 1), (20782640965039, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (234103828649, 1), (20782640965039, 1)] : List FactorBlock).map factorBlockValue).prod = 38922366554825424444818489 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twentyFourV_2
      · exact prime_twentyFourV_234103828649
      · exact prime_twentyFourV_20782640965039
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 38922366554825424444818489) ^ 19461183277412712222409244 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (3 : ZMod 38922366554825424444818489) ^ 166261127720312 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (3 : ZMod 38922366554825424444818489) ^ 1872830629192 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide

private theorem prime_twentyFourV_16492747 : Nat.Prime 16492747 := by norm_num
private theorem prime_twentyFourV_5094919 : Nat.Prime 5094919 := by norm_num
private theorem prime_twentyFourV_491357 : Nat.Prime 491357 := by norm_num
private theorem prime_twentyFourV_47170273 : Nat.Prime 47170273 := by
  apply lucas_primality 47170273 (7 : ZMod 47170273)
  · rw [← twentyFourVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 5), (3, 1), (491357, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 5), (3, 1), (491357, 1)] : List FactorBlock).map factorBlockValue).prod = 47170273 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twentyFourV_2
      · exact prime_twentyFourV_3
      · exact prime_twentyFourV_491357
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 47170273) ^ 23585136 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (7 : ZMod 47170273) ^ 15723424 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (7 : ZMod 47170273) ^ 96 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide

private theorem prime_twentyFourV_36049308021433051 : Nat.Prime 36049308021433051 := by
  apply lucas_primality 36049308021433051 (3 : ZMod 36049308021433051)
  · rw [← twentyFourVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (5, 2), (5094919, 1), (47170273, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (5, 2), (5094919, 1), (47170273, 1)] : List FactorBlock).map factorBlockValue).prod = 36049308021433051 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyFourV_2
      · exact prime_twentyFourV_3
      · exact prime_twentyFourV_5
      · exact prime_twentyFourV_5094919
      · exact prime_twentyFourV_47170273
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 36049308021433051) ^ 18024654010716525 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (3 : ZMod 36049308021433051) ^ 12016436007144350 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (3 : ZMod 36049308021433051) ^ 7209861604286610 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (3 : ZMod 36049308021433051) ^ 7075540950 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (3 : ZMod 36049308021433051) ^ 764237850 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide

private theorem prime_twentyFourV_20980697268474035683 : Nat.Prime 20980697268474035683 := by
  apply lucas_primality 20980697268474035683 (2 : ZMod 20980697268474035683)
  · rw [← twentyFourVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (97, 1), (36049308021433051, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (97, 1), (36049308021433051, 1)] : List FactorBlock).map factorBlockValue).prod = 20980697268474035683 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyFourV_2
      · exact prime_twentyFourV_3
      · exact prime_twentyFourV_97
      · exact prime_twentyFourV_36049308021433051
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 20980697268474035683) ^ 10490348634237017841 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (2 : ZMod 20980697268474035683) ^ 6993565756158011894 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (2 : ZMod 20980697268474035683) ^ 216295848128598306 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (2 : ZMod 20980697268474035683) ^ 582 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide

private theorem prime_twentyFourV_374093 : Nat.Prime 374093 := by norm_num
private theorem prime_twentyFourV_1444291 : Nat.Prime 1444291 := by norm_num
private theorem prime_twentyFourV_87723346759 : Nat.Prime 87723346759 := by
  apply lucas_primality 87723346759 (11 : ZMod 87723346759)
  · rw [← twentyFourVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (53, 1), (191, 1), (1444291, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (53, 1), (191, 1), (1444291, 1)] : List FactorBlock).map factorBlockValue).prod = 87723346759 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyFourV_2
      · exact prime_twentyFourV_3
      · exact prime_twentyFourV_53
      · exact prime_twentyFourV_191
      · exact prime_twentyFourV_1444291
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 87723346759) ^ 43861673379 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (11 : ZMod 87723346759) ^ 29241115586 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (11 : ZMod 87723346759) ^ 1655157486 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (11 : ZMod 87723346759) ^ 459284538 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (11 : ZMod 87723346759) ^ 60738 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide

private theorem prime_twentyFourV_10653123230412961 : Nat.Prime 10653123230412961 := by
  apply lucas_primality 10653123230412961 (17 : ZMod 10653123230412961)
  · rw [← twentyFourVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 5), (3, 1), (5, 1), (11, 1), (23, 1), (87723346759, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 5), (3, 1), (5, 1), (11, 1), (23, 1), (87723346759, 1)] : List FactorBlock).map factorBlockValue).prod = 10653123230412961 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyFourV_2
      · exact prime_twentyFourV_3
      · exact prime_twentyFourV_5
      · exact prime_twentyFourV_11
      · exact prime_twentyFourV_23
      · exact prime_twentyFourV_87723346759
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (17 : ZMod 10653123230412961) ^ 5326561615206480 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (17 : ZMod 10653123230412961) ^ 3551041076804320 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (17 : ZMod 10653123230412961) ^ 2130624646082592 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (17 : ZMod 10653123230412961) ^ 968465748219360 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (17 : ZMod 10653123230412961) ^ 463179270887520 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (17 : ZMod 10653123230412961) ^ 121440 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide

private theorem prime_twentyFourV_170449971686607377 : Nat.Prime 170449971686607377 := by
  apply lucas_primality 170449971686607377 (3 : ZMod 170449971686607377)
  · rw [← twentyFourVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 4), (10653123230412961, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 4), (10653123230412961, 1)] : List FactorBlock).map factorBlockValue).prod = 170449971686607377 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_twentyFourV_2
      · exact prime_twentyFourV_10653123230412961
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 170449971686607377) ^ 85224985843303688 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (3 : ZMod 170449971686607377) ^ 16 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide

private theorem prime_twentyFourV_75848532900823416691231 : Nat.Prime 75848532900823416691231 := by
  apply lucas_primality 75848532900823416691231 (12 : ZMod 75848532900823416691231)
  · rw [← twentyFourVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (5, 1), (7, 1), (13, 1), (163, 1), (170449971686607377, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (5, 1), (7, 1), (13, 1), (163, 1), (170449971686607377, 1)] : List FactorBlock).map factorBlockValue).prod = 75848532900823416691231 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyFourV_2
      · exact prime_twentyFourV_3
      · exact prime_twentyFourV_5
      · exact prime_twentyFourV_7
      · exact prime_twentyFourV_13
      · exact prime_twentyFourV_163
      · exact prime_twentyFourV_170449971686607377
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (12 : ZMod 75848532900823416691231) ^ 37924266450411708345615 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (12 : ZMod 75848532900823416691231) ^ 25282844300274472230410 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (12 : ZMod 75848532900823416691231) ^ 15169706580164683338246 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (12 : ZMod 75848532900823416691231) ^ 10835504700117630955890 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (12 : ZMod 75848532900823416691231) ^ 5834502530832570514710 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (12 : ZMod 75848532900823416691231) ^ 465328422704438139210 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (12 : ZMod 75848532900823416691231) ^ 444990 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide

private theorem prime_twentyFourV_97523 : Nat.Prime 97523 := by norm_num
private theorem prime_twentyFourV_467 : Nat.Prime 467 := by norm_num
private theorem prime_twentyFourV_1123 : Nat.Prime 1123 := by norm_num
private theorem prime_twentyFourV_5826967 : Nat.Prime 5826967 := by norm_num
private theorem prime_twentyFourV_138448735921 : Nat.Prime 138448735921 := by
  apply lucas_primality 138448735921 (14 : ZMod 138448735921)
  · rw [← twentyFourVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 4), (3, 3), (5, 1), (11, 1), (5826967, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 4), (3, 3), (5, 1), (11, 1), (5826967, 1)] : List FactorBlock).map factorBlockValue).prod = 138448735921 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyFourV_2
      · exact prime_twentyFourV_3
      · exact prime_twentyFourV_5
      · exact prime_twentyFourV_11
      · exact prime_twentyFourV_5826967
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (14 : ZMod 138448735921) ^ 69224367960 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (14 : ZMod 138448735921) ^ 46149578640 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (14 : ZMod 138448735921) ^ 27689747184 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (14 : ZMod 138448735921) ^ 12586248720 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (14 : ZMod 138448735921) ^ 23760 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide

private theorem prime_twentyFourV_621911721757133 : Nat.Prime 621911721757133 := by
  apply lucas_primality 621911721757133 (2 : ZMod 621911721757133)
  · rw [← twentyFourVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (1123, 1), (138448735921, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (1123, 1), (138448735921, 1)] : List FactorBlock).map factorBlockValue).prod = 621911721757133 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twentyFourV_2
      · exact prime_twentyFourV_1123
      · exact prime_twentyFourV_138448735921
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 621911721757133) ^ 310955860878566 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (2 : ZMod 621911721757133) ^ 553794943684 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (2 : ZMod 621911721757133) ^ 4492 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide

private theorem prime_twentyFourV_3463701263446490329787 : Nat.Prime 3463701263446490329787 := by
  apply lucas_primality 3463701263446490329787 (2 : ZMod 3463701263446490329787)
  · rw [← twentyFourVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (67, 1), (89, 1), (467, 1), (621911721757133, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (67, 1), (89, 1), (467, 1), (621911721757133, 1)] : List FactorBlock).map factorBlockValue).prod = 3463701263446490329787 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyFourV_2
      · exact prime_twentyFourV_67
      · exact prime_twentyFourV_89
      · exact prime_twentyFourV_467
      · exact prime_twentyFourV_621911721757133
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 3463701263446490329787) ^ 1731850631723245164893 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (2 : ZMod 3463701263446490329787) ^ 51697033782783437758 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (2 : ZMod 3463701263446490329787) ^ 38917991724117868874 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (2 : ZMod 3463701263446490329787) ^ 7416919193675568158 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide
    · change (2 : ZMod 3463701263446490329787) ^ 5569442 ≠ 1
      rw [← twentyFourVFastPow_eq_pow]
      decide

private theorem phi_twentyFourV_28374405218467734420272678385 : Nat.totient 28374405218467734420272678385 = 15017496909519818726251187520 := by
  rw [← show ((([(3, 1), (5, 1), (131, 1), (14439900874538287236779989, 1)] : List FactorBlock).map factorBlockValue).prod) = 28374405218467734420272678385 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyFourV_3, prime_twentyFourV_5, prime_twentyFourV_131, prime_twentyFourV_14439900874538287236779989]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyFourV_28374405218467734420272678386 : Nat.totient 28374405218467734420272678386 = 12160459379343314751545433588 := by
  rw [← show ((([(2, 1), (7, 1), (2026743229890552458590905599, 1)] : List FactorBlock).map factorBlockValue).prod) = 28374405218467734420272678386 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyFourV_2, prime_twentyFourV_7, prime_twentyFourV_2026743229890552458590905599]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyFourV_28374405218467734420272678387 : Nat.totient 28374405218467734420272678387 = 26191241479066094186501859840 := by
  rw [← show ((([(13, 1), (58153, 1), (392143, 1), (95712095198917481, 1)] : List FactorBlock).map factorBlockValue).prod) = 28374405218467734420272678387 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyFourV_13, prime_twentyFourV_58153, prime_twentyFourV_392143, prime_twentyFourV_95712095198917481]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyFourV_28374405218467734420272678388 : Nat.totient 28374405218467734420272678388 = 9450836487322544148642097920 := by
  rw [← show ((([(2, 2), (3, 1), (1531, 1), (11923, 1), (28807, 1), (4496625855541289, 1)] : List FactorBlock).map factorBlockValue).prod) = 28374405218467734420272678388 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyFourV_2, prime_twentyFourV_3, prime_twentyFourV_1531, prime_twentyFourV_11923, prime_twentyFourV_28807, prime_twentyFourV_4496625855541289]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyFourV_28374405218467734420272678389 : Nat.totient 28374405218467734420272678389 = 25794913834970667654793343980 := by
  rw [← show ((([(11, 1), (2579491383497066765479334399, 1)] : List FactorBlock).map factorBlockValue).prod) = 28374405218467734420272678389 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyFourV_11, prime_twentyFourV_2579491383497066765479334399]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyFourV_28374405218467734420272678390 : Nat.totient 28374405218467734420272678390 = 11349290379557519473866503520 := by
  rw [← show ((([(2, 1), (5, 1), (24061, 1), (117926957393573560617899, 1)] : List FactorBlock).map factorBlockValue).prod) = 28374405218467734420272678390 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyFourV_2, prime_twentyFourV_5, prime_twentyFourV_24061, prime_twentyFourV_117926957393573560617899]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyFourV_28374405218467734420272678391 : Nat.totient 28374405218467734420272678391 = 18916270094857055212247552784 := by
  rw [← show ((([(3, 2), (372454763, 1), (8464683510949917373, 1)] : List FactorBlock).map factorBlockValue).prod) = 28374405218467734420272678391 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyFourV_3, prime_twentyFourV_372454763, prime_twentyFourV_8464683510949917373]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyFourV_28374405218467734420272678392 : Nat.totient 28374405218467734420272678392 = 14183584462241545743906877440 := by
  rw [← show ((([(2, 3), (3923, 1), (8197093, 1), (110295707065568641, 1)] : List FactorBlock).map factorBlockValue).prod) = 28374405218467734420272678392 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyFourV_2, prime_twentyFourV_3923, prime_twentyFourV_8197093, prime_twentyFourV_110295707065568641]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyFourV_28374405218467734420272678393 : Nat.totient 28374405218467734420272678393 = 24299578674779043973733222400 := by
  rw [← show ((([(7, 1), (1163, 1), (60773, 1), (1269173, 1), (3473737, 1), (13008301, 1)] : List FactorBlock).map factorBlockValue).prod) = 28374405218467734420272678393 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyFourV_7, prime_twentyFourV_1163, prime_twentyFourV_60773, prime_twentyFourV_1269173, prime_twentyFourV_3473737, prime_twentyFourV_13008301]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyFourV_28374405218467734420272678394 : Nat.totient 28374405218467734420272678394 = 9457537686649636689178586112 := by
  rw [← show ((([(2, 1), (3, 1), (18713, 1), (109469, 1), (1701179, 1), (1357034643673, 1)] : List FactorBlock).map factorBlockValue).prod) = 28374405218467734420272678394 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyFourV_2, prime_twentyFourV_3, prime_twentyFourV_18713, prime_twentyFourV_109469, prime_twentyFourV_1701179, prime_twentyFourV_1357034643673]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyFourV_28374405218467734420272678395 : Nat.totient 28374405218467734420272678395 = 22699524174774187536218142712 := by
  rw [← show ((([(5, 1), (5674881043693546884054535679, 1)] : List FactorBlock).map factorBlockValue).prod) = 28374405218467734420272678395 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyFourV_5, prime_twentyFourV_5674881043693546884054535679]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyFourV_28374405218467734420272678396 : Nat.totient 28374405218467734420272678396 = 13986180465894842667327004160 := by
  rw [← show ((([(2, 2), (71, 1), (11633, 1), (8588487709947216218393, 1)] : List FactorBlock).map factorBlockValue).prod) = 28374405218467734420272678396 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyFourV_2, prime_twentyFourV_71, prime_twentyFourV_11633, prime_twentyFourV_8588487709947216218393]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyFourV_28374405218467734420272678397 : Nat.totient 28374405218467734420272678397 = 18916233246092007100935429120 := by
  rw [← show ((([(3, 1), (566437, 1), (5397907, 1), (3093346001652161, 1)] : List FactorBlock).map factorBlockValue).prod) = 28374405218467734420272678397 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyFourV_3, prime_twentyFourV_566437, prime_twentyFourV_5397907, prime_twentyFourV_3093346001652161]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyFourV_28374405218467734420272678398 : Nat.totient 28374405218467734420272678398 = 14187202217963476445475459240 := by
  rw [← show ((([(2, 1), (36259331, 1), (391270390764624620629, 1)] : List FactorBlock).map factorBlockValue).prod) = 28374405218467734420272678398 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyFourV_2, prime_twentyFourV_36259331, prime_twentyFourV_391270390764624620629]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyFourV_28374405218467734420272678399 : Nat.totient 28374405218467734420272678399 = 28374405218467734420272678398 := by
  rw [← show ((([(28374405218467734420272678399, 1)] : List FactorBlock).map factorBlockValue).prod) = 28374405218467734420272678399 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyFourV_28374405218467734420272678399]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyFourV_28374405218467734420272678400 : Nat.totient 28374405218467734420272678400 = 3733712843024655345254400000 := by
  rw [← show ((([(2, 9), (3, 4), (5, 2), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 28374405218467734420272678400 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyFourV_2, prime_twentyFourV_3, prime_twentyFourV_5, prime_twentyFourV_7, prime_twentyFourV_11, prime_twentyFourV_13, prime_twentyFourV_17, prime_twentyFourV_19, prime_twentyFourV_23, prime_twentyFourV_29, prime_twentyFourV_31, prime_twentyFourV_37, prime_twentyFourV_41, prime_twentyFourV_43, prime_twentyFourV_47, prime_twentyFourV_53, prime_twentyFourV_59, prime_twentyFourV_61]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyFourV_28374405218467734420272678401 : Nat.totient 28374405218467734420272678401 = 28225848092486214184111416000 := by
  rw [← show ((([(191, 1), (922507631, 1), (161036169666815281, 1)] : List FactorBlock).map factorBlockValue).prod) = 28374405218467734420272678401 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyFourV_191, prime_twentyFourV_922507631, prime_twentyFourV_161036169666815281]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyFourV_28374405218467734420272678402 : Nat.totient 28374405218467734420272678402 = 14064312954898694022213634560 := by
  rw [← show ((([(2, 1), (181, 1), (317, 1), (247262885986263959602913, 1)] : List FactorBlock).map factorBlockValue).prod) = 28374405218467734420272678402 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyFourV_2, prime_twentyFourV_181, prime_twentyFourV_317, prime_twentyFourV_247262885986263959602913]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyFourV_28374405218467734420272678403 : Nat.totient 28374405218467734420272678403 = 18795777323961156236076393216 := by
  rw [← show ((([(3, 1), (157, 1), (4315799, 1), (7041049, 1), (1982473007243, 1)] : List FactorBlock).map factorBlockValue).prod) = 28374405218467734420272678403 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyFourV_3, prime_twentyFourV_157, prime_twentyFourV_4315799, prime_twentyFourV_7041049, prime_twentyFourV_1982473007243]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyFourV_28374405218467734420272678404 : Nat.totient 28374405218467734420272678404 = 14187080202959039276371584960 := by
  rw [← show ((([(2, 2), (115903, 1), (32244294937, 1), (1898100541591, 1)] : List FactorBlock).map factorBlockValue).prod) = 28374405218467734420272678404 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyFourV_2, prime_twentyFourV_115903, prime_twentyFourV_32244294937, prime_twentyFourV_1898100541591]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyFourV_28374405218467734420272678405 : Nat.totient 28374405218467734420272678405 = 22563643268499179843484576000 := by
  rw [← show ((([(5, 1), (173, 1), (4951, 1), (228023, 1), (1805911, 1), (16089506899, 1)] : List FactorBlock).map factorBlockValue).prod) = 28374405218467734420272678405 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyFourV_5, prime_twentyFourV_173, prime_twentyFourV_4951, prime_twentyFourV_228023, prime_twentyFourV_1805911, prime_twentyFourV_16089506899]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyFourV_28374405218467734420272678406 : Nat.totient 28374405218467734420272678406 = 9433519265891016348115968000 := by
  rw [← show ((([(2, 1), (3, 1), (401, 1), (11069, 1), (53269, 1), (20000838920189041, 1)] : List FactorBlock).map factorBlockValue).prod) = 28374405218467734420272678406 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyFourV_2, prime_twentyFourV_3, prime_twentyFourV_401, prime_twentyFourV_11069, prime_twentyFourV_53269, prime_twentyFourV_20000838920189041]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyFourV_28374405218467734420272678407 : Nat.totient 28374405218467734420272678407 = 24317472974197316796885191904 := by
  rw [← show ((([(7, 1), (9067, 1), (32143, 1), (3542327, 1), (3926359426523, 1)] : List FactorBlock).map factorBlockValue).prod) = 28374405218467734420272678407 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyFourV_7, prime_twentyFourV_9067, prime_twentyFourV_32143, prime_twentyFourV_3542327, prime_twentyFourV_3926359426523]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyFourV_28374405218467734420272678408 : Nat.totient 28374405218467734420272678408 = 14187202608767627957354904400 := by
  rw [← show ((([(2, 3), (30429025931, 1), (116559782766332771, 1)] : List FactorBlock).map factorBlockValue).prod) = 28374405218467734420272678408 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyFourV_2, prime_twentyFourV_30429025931, prime_twentyFourV_116559782766332771]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyFourV_28374405218467734420272678409 : Nat.totient 28374405218467734420272678409 = 18878663245492027111985259552 := by
  rw [← show ((([(3, 2), (503, 1), (15040590709, 1), (416726749916363, 1)] : List FactorBlock).map factorBlockValue).prod) = 28374405218467734420272678409 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyFourV_3, prime_twentyFourV_503, prime_twentyFourV_15040590709, prime_twentyFourV_416726749916363]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyFourV_28374405218467734420272678410 : Nat.totient 28374405218467734420272678410 = 11349762087385306169741002768 := by
  rw [← show ((([(2, 1), (5, 1), (6442029294047, 1), (440457562723103, 1)] : List FactorBlock).map factorBlockValue).prod) = 28374405218467734420272678410 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyFourV_2, prime_twentyFourV_5, prime_twentyFourV_6442029294047, prime_twentyFourV_440457562723103]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyFourV_28374405218467734420272678411 : Nat.totient 28374405218467734420272678411 = 25566562037057670271412582400 := by
  rw [← show ((([(11, 1), (113, 1), (637519, 1), (670673, 1), (53388987237871, 1)] : List FactorBlock).map factorBlockValue).prod) = 28374405218467734420272678411 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyFourV_11, prime_twentyFourV_113, prime_twentyFourV_637519, prime_twentyFourV_670673, prime_twentyFourV_53388987237871]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyFourV_28374405218467734420272678412 : Nat.totient 28374405218467734420272678412 = 9458090075438874484030430208 := by
  rw [← show ((([(2, 2), (3, 1), (210193, 1), (11249345925914014905457, 1)] : List FactorBlock).map factorBlockValue).prod) = 28374405218467734420272678412 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyFourV_2, prime_twentyFourV_3, prime_twentyFourV_210193, prime_twentyFourV_11249345925914014905457]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyFourV_28374405218467734420272678413 : Nat.totient 28374405218467734420272678413 = 26191452796726712525364821760 := by
  rw [← show ((([(13, 1), (175141, 1), (183439, 1), (1934663, 1), (35115478373, 1)] : List FactorBlock).map factorBlockValue).prod) = 28374405218467734420272678413 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyFourV_13, prime_twentyFourV_175141, prime_twentyFourV_183439, prime_twentyFourV_1934663, prime_twentyFourV_35115478373]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyFourV_28374405218467734420272678414 : Nat.totient 28374405218467734420272678414 = 12023739222634282607417865600 := by
  rw [← show ((([(2, 1), (7, 1), (109, 1), (479, 1), (8596663, 1), (20538307, 1), (219857951, 1)] : List FactorBlock).map factorBlockValue).prod) = 28374405218467734420272678414 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyFourV_2, prime_twentyFourV_7, prime_twentyFourV_109, prime_twentyFourV_479, prime_twentyFourV_8596663, prime_twentyFourV_20538307, prime_twentyFourV_219857951]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyFourV_28374405218467734420272678415 : Nat.totient 28374405218467734420272678415 = 15132836825899783643358817920 := by
  rw [← show ((([(3, 1), (5, 1), (85243, 1), (18480383, 1), (23255671, 1), (51634139, 1)] : List FactorBlock).map factorBlockValue).prod) = 28374405218467734420272678415 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyFourV_3, prime_twentyFourV_5, prime_twentyFourV_85243, prime_twentyFourV_18480383, prime_twentyFourV_23255671, prime_twentyFourV_51634139]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyFourV_28374405218467734420272678416 : Nat.totient 28374405218467734420272678416 = 14185326469577935538308700160 := by
  rw [← show ((([(2, 4), (8233, 1), (93811, 1), (8274073, 1), (277508030299, 1)] : List FactorBlock).map factorBlockValue).prod) = 28374405218467734420272678416 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyFourV_2, prime_twentyFourV_8233, prime_twentyFourV_93811, prime_twentyFourV_8274073, prime_twentyFourV_277508030299]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyFourV_28374405218467734420272678417 : Nat.totient 28374405218467734420272678417 = 26705322542900743547935064832 := by
  rw [← show ((([(17, 1), (1705633957, 1), (978570257152699693, 1)] : List FactorBlock).map factorBlockValue).prod) = 28374405218467734420272678417 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyFourV_17, prime_twentyFourV_1705633957, prime_twentyFourV_978570257152699693]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyFourV_28374405218467734420272678418 : Nat.totient 28374405218467734420272678418 = 9458135072822578140090892800 := by
  rw [← show ((([(2, 1), (3, 2), (1576355845470429690015148801, 1)] : List FactorBlock).map factorBlockValue).prod) = 28374405218467734420272678418 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyFourV_2, prime_twentyFourV_3, prime_twentyFourV_1576355845470429690015148801]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyFourV_28374405218467734420272678419 : Nat.totient 28374405218467734420272678419 = 26867432339520896154341296872 := by
  rw [← show ((([(19, 1), (1979, 1), (754618367023955065564019, 1)] : List FactorBlock).map factorBlockValue).prod) = 28374405218467734420272678419 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyFourV_19, prime_twentyFourV_1979, prime_twentyFourV_754618367023955065564019]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyFourV_28374405218467734420272678420 : Nat.totient 28374405218467734420272678420 = 11338861159810098678655401984 := by
  rw [← show ((([(2, 2), (5, 1), (1049, 1), (139537, 1), (175593973, 1), (55197867029, 1)] : List FactorBlock).map factorBlockValue).prod) = 28374405218467734420272678420 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyFourV_2, prime_twentyFourV_5, prime_twentyFourV_1049, prime_twentyFourV_139537, prime_twentyFourV_175593973, prime_twentyFourV_55197867029]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyFourV_28374405218467734420272678421 : Nat.totient 28374405218467734420272678421 = 16008706018362235401871405056 := by
  rw [← show ((([(3, 1), (7, 1), (79, 1), (1272241326337, 1), (13443454509487, 1)] : List FactorBlock).map factorBlockValue).prod) = 28374405218467734420272678421 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyFourV_3, prime_twentyFourV_7, prime_twentyFourV_79, prime_twentyFourV_1272241326337, prime_twentyFourV_13443454509487]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyFourV_28374405218467734420272678422 : Nat.totient 28374405218467734420272678422 = 12897362947627791912700125000 := by
  rw [← show ((([(2, 1), (11, 1), (137251, 1), (9396985754191469517451, 1)] : List FactorBlock).map factorBlockValue).prod) = 28374405218467734420272678422 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyFourV_2, prime_twentyFourV_11, prime_twentyFourV_137251, prime_twentyFourV_9396985754191469517451]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyFourV_28374405218467734420272678423 : Nat.totient 28374405218467734420272678423 = 27138810770769310564463043840 := by
  rw [← show ((([(23, 1), (14489, 1), (527381, 1), (161449252589470789, 1)] : List FactorBlock).map factorBlockValue).prod) = 28374405218467734420272678423 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyFourV_23, prime_twentyFourV_14489, prime_twentyFourV_527381, prime_twentyFourV_161449252589470789]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyFourV_28374405218467734420272678424 : Nat.totient 28374405218467734420272678424 = 9364438622826365116007809536 := by
  rw [← show ((([(2, 3), (3, 1), (103, 1), (5009, 1), (2291539082278737626663, 1)] : List FactorBlock).map factorBlockValue).prod) = 28374405218467734420272678424 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyFourV_2, prime_twentyFourV_3, prime_twentyFourV_103, prime_twentyFourV_5009, prime_twentyFourV_2291539082278737626663]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyFourV_28374405218467734420272678425 : Nat.totient 28374405218467734420272678425 = 22699392272115887813462838720 := by
  rw [← show ((([(5, 2), (172093, 1), (6595132914986137593109, 1)] : List FactorBlock).map factorBlockValue).prod) = 28374405218467734420272678425 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyFourV_5, prime_twentyFourV_172093, prime_twentyFourV_6595132914986137593109]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyFourV_28374405218467734420272678426 : Nat.totient 28374405218467734420272678426 = 13064366850383300752330490880 := by
  rw [← show ((([(2, 1), (13, 1), (431, 1), (11719, 1), (1228273, 1), (9574219, 1), (18373307, 1)] : List FactorBlock).map factorBlockValue).prod) = 28374405218467734420272678426 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyFourV_2, prime_twentyFourV_13, prime_twentyFourV_431, prime_twentyFourV_11719, prime_twentyFourV_1228273, prime_twentyFourV_9574219, prime_twentyFourV_18373307]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyFourV_28374405218467734420272678427 : Nat.totient 28374405218467734420272678427 = 18795761964798830945561441664 := by
  rw [← show ((([(3, 3), (227, 1), (509, 1), (106363, 1), (85512338798115589, 1)] : List FactorBlock).map factorBlockValue).prod) = 28374405218467734420272678427 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyFourV_3, prime_twentyFourV_227, prime_twentyFourV_509, prime_twentyFourV_106363, prime_twentyFourV_85512338798115589]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyFourV_28374405218467734420272678428 : Nat.totient 28374405218467734420272678428 = 12122020211250044472243546240 := by
  rw [← show ((([(2, 2), (7, 1), (331, 1), (7129, 1), (429449525106920937499, 1)] : List FactorBlock).map factorBlockValue).prod) = 28374405218467734420272678428 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyFourV_2, prime_twentyFourV_7, prime_twentyFourV_331, prime_twentyFourV_7129, prime_twentyFourV_429449525106920937499]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyFourV_28374405218467734420272678429 : Nat.totient 28374405218467734420272678429 = 26994618520847220352880332800 := by
  rw [← show ((([(29, 2), (73, 1), (1069, 1), (34591, 1), (1856137, 1), (6733751111, 1)] : List FactorBlock).map factorBlockValue).prod) = 28374405218467734420272678429 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyFourV_29, prime_twentyFourV_73, prime_twentyFourV_1069, prime_twentyFourV_34591, prime_twentyFourV_1856137, prime_twentyFourV_6733751111]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyFourV_28374405218467734420272678430 : Nat.totient 28374405218467734420272678430 = 7488393379571239139119808000 := by
  rw [← show ((([(2, 1), (3, 1), (5, 1), (107, 1), (1013, 1), (144417341, 1), (60421700572451, 1)] : List FactorBlock).map factorBlockValue).prod) = 28374405218467734420272678430 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyFourV_2, prime_twentyFourV_3, prime_twentyFourV_5, prime_twentyFourV_107, prime_twentyFourV_1013, prime_twentyFourV_144417341, prime_twentyFourV_60421700572451]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyFourV_28374405218467734420272678431 : Nat.totient 28374405218467734420272678431 = 27458251431864542401124476800 := by
  rw [← show ((([(31, 1), (53173, 1), (82763, 1), (12444181, 1), (16713652379, 1)] : List FactorBlock).map factorBlockValue).prod) = 28374405218467734420272678431 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyFourV_31, prime_twentyFourV_53173, prime_twentyFourV_82763, prime_twentyFourV_12444181, prime_twentyFourV_16713652379]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyFourV_28374405218467734420272678432 : Nat.totient 28374405218467734420272678432 = 14160493283226141610141286400 := by
  rw [← show ((([(2, 5), (769, 1), (2143, 1), (8597, 1), (9792301, 1), (6391408799, 1)] : List FactorBlock).map factorBlockValue).prod) = 28374405218467734420272678432 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyFourV_2, prime_twentyFourV_769, prime_twentyFourV_2143, prime_twentyFourV_8597, prime_twentyFourV_9792301, prime_twentyFourV_6391408799]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyFourV_28374405218467734420272678433 : Nat.totient 28374405218467734420272678433 = 17196407574338606892000215040 := by
  rw [← show ((([(3, 1), (11, 1), (85313, 1), (219959393, 1), (45820001621089, 1)] : List FactorBlock).map factorBlockValue).prod) = 28374405218467734420272678433 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyFourV_3, prime_twentyFourV_11, prime_twentyFourV_85313, prime_twentyFourV_219959393, prime_twentyFourV_45820001621089]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyFourV_28374405218467734420272678434 : Nat.totient 28374405218467734420272678434 = 13330663443608576742587343360 := by
  rw [← show ((([(2, 1), (17, 1), (607, 1), (324023303, 1), (4243096546919081, 1)] : List FactorBlock).map factorBlockValue).prod) = 28374405218467734420272678434 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyFourV_2, prime_twentyFourV_17, prime_twentyFourV_607, prime_twentyFourV_324023303, prime_twentyFourV_4243096546919081]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyFourV_28374405218467734420272678435 : Nat.totient 28374405218467734420272678435 = 19456735006938536767486204416 := by
  rw [← show ((([(5, 1), (7, 1), (1814437336489, 1), (446803687100569, 1)] : List FactorBlock).map factorBlockValue).prod) = 28374405218467734420272678435 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyFourV_5, prime_twentyFourV_7, prime_twentyFourV_1814437336489, prime_twentyFourV_446803687100569]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyFourV_28374405218467734420272678436 : Nat.totient 28374405218467734420272678436 = 9429298375565393472865536000 := by
  rw [← show ((([(2, 2), (3, 2), (421, 1), (1483, 1), (2072201, 1), (2567179, 1), (237308333, 1)] : List FactorBlock).map factorBlockValue).prod) = 28374405218467734420272678436 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyFourV_2, prime_twentyFourV_3, prime_twentyFourV_421, prime_twentyFourV_1483, prime_twentyFourV_2072201, prime_twentyFourV_2567179, prime_twentyFourV_237308333]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyFourV_28374405218467734420272678437 : Nat.totient 28374405218467734420272678437 = 27600733235461146457463324928 := by
  rw [← show ((([(37, 1), (4079, 1), (992263, 1), (276413069, 1), (685466077, 1)] : List FactorBlock).map factorBlockValue).prod) = 28374405218467734420272678437 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyFourV_37, prime_twentyFourV_4079, prime_twentyFourV_992263, prime_twentyFourV_276413069, prime_twentyFourV_685466077]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyFourV_28374405218467734420272678438 : Nat.totient 28374405218467734420272678438 = 13240450668486914686476748800 := by
  rw [← show ((([(2, 1), (19, 2), (101, 1), (199, 1), (119737, 1), (21706837, 1), (752298509, 1)] : List FactorBlock).map factorBlockValue).prod) = 28374405218467734420272678438 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyFourV_2, prime_twentyFourV_19, prime_twentyFourV_101, prime_twentyFourV_199, prime_twentyFourV_119737, prime_twentyFourV_21706837, prime_twentyFourV_752298509]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyFourV_28374405218467734420272678439 : Nat.totient 28374405218467734420272678439 = 17395640938693272227543377920 := by
  rw [← show ((([(3, 1), (13, 1), (307, 1), (2011, 1), (100888969, 1), (11680677399577, 1)] : List FactorBlock).map factorBlockValue).prod) = 28374405218467734420272678439 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyFourV_3, prime_twentyFourV_13, prime_twentyFourV_307, prime_twentyFourV_2011, prime_twentyFourV_100888969, prime_twentyFourV_11680677399577]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyFourV_28374405218467734420272678440 : Nat.totient 28374405218467734420272678440 = 11294067856788255329410314240 := by
  rw [← show ((([(2, 3), (5, 1), (281, 1), (739, 1), (3540386347, 1), (964862349257, 1)] : List FactorBlock).map factorBlockValue).prod) = 28374405218467734420272678440 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyFourV_2, prime_twentyFourV_5, prime_twentyFourV_281, prime_twentyFourV_739, prime_twentyFourV_3540386347, prime_twentyFourV_964862349257]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyFourV_28374405218467734420272678441 : Nat.totient 28374405218467734420272678441 = 27269135460650116555872556800 := by
  rw [← show ((([(41, 1), (67, 1), (653273, 1), (15811511862622282211, 1)] : List FactorBlock).map factorBlockValue).prod) = 28374405218467734420272678441 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyFourV_41, prime_twentyFourV_67, prime_twentyFourV_653273, prime_twentyFourV_15811511862622282211]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyFourV_28374405218467734420272678442 : Nat.totient 28374405218467734420272678442 = 8099514802800883054387193904 := by
  rw [← show ((([(2, 1), (3, 1), (7, 1), (1087, 1), (621509730110564998034623, 1)] : List FactorBlock).map factorBlockValue).prod) = 28374405218467734420272678442 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyFourV_2, prime_twentyFourV_3, prime_twentyFourV_7, prime_twentyFourV_1087, prime_twentyFourV_621509730110564998034623]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyFourV_28374405218467734420272678443 : Nat.totient 28374405218467734420272678443 = 27703145558829412790105702400 := by
  rw [← show ((([(43, 1), (2441, 1), (1127537, 1), (2422033, 1), (98987344441, 1)] : List FactorBlock).map factorBlockValue).prod) = 28374405218467734420272678443 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyFourV_43, prime_twentyFourV_2441, prime_twentyFourV_1127537, prime_twentyFourV_2422033, prime_twentyFourV_98987344441]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyFourV_28374405218467734420272678444 : Nat.totient 28374405218467734420272678444 = 12897259335595233175515382080 := by
  rw [← show ((([(2, 2), (11, 1), (97327, 1), (208223, 1), (4129087, 1), (7706514863, 1)] : List FactorBlock).map factorBlockValue).prod) = 28374405218467734420272678444 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyFourV_2, prime_twentyFourV_11, prime_twentyFourV_97327, prime_twentyFourV_208223, prime_twentyFourV_4129087, prime_twentyFourV_7706514863]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyFourV_28374405218467734420272678445 : Nat.totient 28374405218467734420272678445 = 15132788778754478100226643712 := by
  rw [← show ((([(3, 2), (5, 1), (66569, 1), (1596046247, 1), (5934672374047, 1)] : List FactorBlock).map factorBlockValue).prod) = 28374405218467734420272678445 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyFourV_3, prime_twentyFourV_5, prime_twentyFourV_66569, prime_twentyFourV_1596046247, prime_twentyFourV_5934672374047]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyFourV_28374405218467734420272678446 : Nat.totient 28374405218467734420272678446 = 13515729490456587620938973184 := by
  rw [← show ((([(2, 1), (23, 1), (449, 1), (557, 1), (128239, 1), (73816529, 1), (260551547, 1)] : List FactorBlock).map factorBlockValue).prod) = 28374405218467734420272678446 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyFourV_2, prime_twentyFourV_23, prime_twentyFourV_449, prime_twentyFourV_557, prime_twentyFourV_128239, prime_twentyFourV_73816529, prime_twentyFourV_260551547]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyFourV_28374405218467734420272678447 : Nat.totient 28374405218467734420272678447 = 27770694469136337280435881984 := by
  rw [← show ((([(47, 1), (20563414774369, 1), (29358487194529, 1)] : List FactorBlock).map factorBlockValue).prod) = 28374405218467734420272678447 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyFourV_47, prime_twentyFourV_20563414774369, prime_twentyFourV_29358487194529]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyFourV_28374405218467734420272678448 : Nat.totient 28374405218467734420272678448 = 9458135065086595926115297600 := by
  rw [← show ((([(2, 4), (3, 1), (1222615931, 1), (483498887150858771, 1)] : List FactorBlock).map factorBlockValue).prod) = 28374405218467734420272678448 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyFourV_2, prime_twentyFourV_3, prime_twentyFourV_1222615931, prime_twentyFourV_483498887150858771]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyFourV_28374405218467734420272678449 : Nat.totient 28374405218467734420272678449 = 24317574797338797167596763136 := by
  rw [← show ((([(7, 2), (8209, 1), (63793, 1), (971781007, 1), (1137886639, 1)] : List FactorBlock).map factorBlockValue).prod) = 28374405218467734420272678449 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyFourV_7, prime_twentyFourV_8209, prime_twentyFourV_63793, prime_twentyFourV_971781007, prime_twentyFourV_1137886639]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyFourV_28374405218467734420272678450 : Nat.totient 28374405218467734420272678450 = 11349587821513406361671801600 := by
  rw [← show ((([(2, 1), (5, 2), (65129, 1), (8713293684370321798361, 1)] : List FactorBlock).map factorBlockValue).prod) = 28374405218467734420272678450 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyFourV_2, prime_twentyFourV_5, prime_twentyFourV_65129, prime_twentyFourV_8713293684370321798361]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyFourV_28374405218467734420272678451 : Nat.totient 28374405218467734420272678451 = 17778132830762956802022260736 := by
  rw [← show ((([(3, 1), (17, 1), (709, 1), (58337, 1), (13451362101445396397, 1)] : List FactorBlock).map factorBlockValue).prod) = 28374405218467734420272678451 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyFourV_3, prime_twentyFourV_17, prime_twentyFourV_709, prime_twentyFourV_58337, prime_twentyFourV_13451362101445396397]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyFourV_28374405218467734420272678452 : Nat.totient 28374405218467734420272678452 = 13095879331600492809356620800 := by
  rw [← show ((([(2, 2), (13, 1), (545661638816687200389859201, 1)] : List FactorBlock).map factorBlockValue).prod) = 28374405218467734420272678452 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyFourV_2, prime_twentyFourV_13, prime_twentyFourV_545661638816687200389859201]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyFourV_28374405218467734420272678453 : Nat.totient 28374405218467734420272678453 = 27839039082238736184065708800 := by
  rw [← show ((([(53, 1), (885246550361, 1), (604765006968041, 1)] : List FactorBlock).map factorBlockValue).prod) = 28374405218467734420272678453 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyFourV_53, prime_twentyFourV_885246550361, prime_twentyFourV_604765006968041]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyFourV_28374405218467734420272678454 : Nat.totient 28374405218467734420272678454 = 9458135072822578140090892800 := by
  rw [← show ((([(2, 1), (3, 3), (525451948490143230005049601, 1)] : List FactorBlock).map factorBlockValue).prod) = 28374405218467734420272678454 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyFourV_2, prime_twentyFourV_3, prime_twentyFourV_525451948490143230005049601]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyFourV_28374405218467734420272678455 : Nat.totient 28374405218467734420272678455 = 20051870879806192955243520000 := by
  rw [← show ((([(5, 1), (11, 1), (83, 1), (151, 1), (193, 1), (211, 1), (1010809402816401359, 1)] : List FactorBlock).map factorBlockValue).prod) = 28374405218467734420272678455 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyFourV_5, prime_twentyFourV_11, prime_twentyFourV_83, prime_twentyFourV_151, prime_twentyFourV_193, prime_twentyFourV_211, prime_twentyFourV_1010809402816401359]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyFourV_28374405218467734420272678456 : Nat.totient 28374405218467734420272678456 = 12143732174124047542787144832 := by
  rw [← show ((([(2, 3), (7, 1), (727, 1), (40346827, 1), (17274080639688469, 1)] : List FactorBlock).map factorBlockValue).prod) = 28374405218467734420272678456 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyFourV_2, prime_twentyFourV_7, prime_twentyFourV_727, prime_twentyFourV_40346827, prime_twentyFourV_17274080639688469]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyFourV_28374405218467734420272678457 : Nat.totient 28374405218467734420272678457 = 17920676980038927057667210944 := by
  rw [← show ((([(3, 1), (19, 1), (390056504429, 1), (1276216592026469, 1)] : List FactorBlock).map factorBlockValue).prod) = 28374405218467734420272678457 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyFourV_3, prime_twentyFourV_19, prime_twentyFourV_390056504429, prime_twentyFourV_1276216592026469]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyFourV_28374405218467734420272678458 : Nat.totient 28374405218467734420272678458 = 13696936356894101396859977280 := by
  rw [← show ((([(2, 1), (29, 1), (16831, 1), (57427, 1), (506142404437043173, 1)] : List FactorBlock).map factorBlockValue).prod) = 28374405218467734420272678458 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyFourV_2, prime_twentyFourV_29, prime_twentyFourV_16831, prime_twentyFourV_57427, prime_twentyFourV_506142404437043173]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyFourV_28374405218467734420272678459 : Nat.totient 28374405218467734420272678459 = 27881295439905497296365410304 := by
  rw [← show ((([(59, 1), (2297, 1), (630577, 1), (332028706727135129, 1)] : List FactorBlock).map factorBlockValue).prod) = 28374405218467734420272678459 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyFourV_59, prime_twentyFourV_2297, prime_twentyFourV_630577, prime_twentyFourV_332028706727135129]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyFourV_28374405218467734420272678460 : Nat.totient 28374405218467734420272678460 = 7533101469501398473590152448 := by
  rw [← show ((([(2, 2), (3, 1), (5, 1), (239, 1), (4327, 1), (1214459, 1), (376537177183483, 1)] : List FactorBlock).map factorBlockValue).prod) = 28374405218467734420272678460 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyFourV_2, prime_twentyFourV_3, prime_twentyFourV_5, prime_twentyFourV_239, prime_twentyFourV_4327, prime_twentyFourV_1214459, prime_twentyFourV_376537177183483]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyFourV_28374405218467734420272678461 : Nat.totient 28374405218467734420272678461 = 27909243696235015319121907200 := by
  rw [← show ((([(61, 1), (3842989, 1), (367917289, 1), (328986133981, 1)] : List FactorBlock).map factorBlockValue).prod) = 28374405218467734420272678461 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyFourV_61, prime_twentyFourV_3842989, prime_twentyFourV_367917289, prime_twentyFourV_328986133981]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyFourV_28374405218467734420272678462 : Nat.totient 28374405218467734420272678462 = 13587707080306578714386976000 := by
  rw [← show ((([(2, 1), (31, 1), (97, 1), (44983, 1), (104885372978717557351, 1)] : List FactorBlock).map factorBlockValue).prod) = 28374405218467734420272678462 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyFourV_2, prime_twentyFourV_31, prime_twentyFourV_97, prime_twentyFourV_44983, prime_twentyFourV_104885372978717557351]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyFourV_28374405218467734420272678463 : Nat.totient 28374405218467734420272678463 = 16213945839124419668727244800 := by
  rw [← show ((([(3, 2), (7, 1), (450387384420122768575756801, 1)] : List FactorBlock).map factorBlockValue).prod) = 28374405218467734420272678463 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyFourV_3, prime_twentyFourV_7, prime_twentyFourV_450387384420122768575756801]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyFourV_28374405218467734420272678464 : Nat.totient 28374405218467734420272678464 = 14148802857292038353182556160 := by
  rw [← show ((([(2, 6), (373, 1), (55249, 1), (157429, 1), (773027, 1), (176780411, 1)] : List FactorBlock).map factorBlockValue).prod) = 28374405218467734420272678464 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyFourV_2, prime_twentyFourV_373, prime_twentyFourV_55249, prime_twentyFourV_157429, prime_twentyFourV_773027, prime_twentyFourV_176780411]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyFourV_28374405218467734420272678465 : Nat.totient 28374405218467734420272678465 = 20953406930560788494970593280 := by
  rw [← show ((([(5, 1), (13, 1), (436529311053349760311887361, 1)] : List FactorBlock).map factorBlockValue).prod) = 28374405218467734420272678465 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyFourV_5, prime_twentyFourV_13, prime_twentyFourV_436529311053349760311887361]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyFourV_28374405218467734420272678466 : Nat.totient 28374405218467734420272678466 = 8596761758684795040349213440 := by
  rw [← show ((([(2, 1), (3, 1), (11, 2), (5573, 1), (3198253273, 1), (2192745608479, 1)] : List FactorBlock).map factorBlockValue).prod) = 28374405218467734420272678466 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyFourV_2, prime_twentyFourV_3, prime_twentyFourV_11, prime_twentyFourV_5573, prime_twentyFourV_3198253273, prime_twentyFourV_2192745608479]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyFourV_28374405218467734420272678467 : Nat.totient 28374405218467734420272678467 = 27974765708348470555198415320 := by
  rw [← show ((([(71, 1), (399639510119263865074263077, 1)] : List FactorBlock).map factorBlockValue).prod) = 28374405218467734420272678467 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyFourV_71, prime_twentyFourV_399639510119263865074263077]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyFourV_28374405218467734420272678468 : Nat.totient 28374405218467734420272678468 = 13194205958389474737301625856 := by
  rw [← show ((([(2, 2), (17, 1), (89, 1), (1567, 1), (2991981134619696139127, 1)] : List FactorBlock).map factorBlockValue).prod) = 28374405218467734420272678468 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyFourV_2, prime_twentyFourV_17, prime_twentyFourV_89, prime_twentyFourV_1567, prime_twentyFourV_2991981134619696139127]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyFourV_28374405218467734420272678469 : Nat.totient 28374405218467734420272678469 = 17961751912335864040083746048 := by
  rw [← show ((([(3, 1), (23, 1), (137, 1), (3001629664494629685842873, 1)] : List FactorBlock).map factorBlockValue).prod) = 28374405218467734420272678469 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyFourV_3, prime_twentyFourV_23, prime_twentyFourV_137, prime_twentyFourV_3001629664494629685842873]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyFourV_28374405218467734420272678470 : Nat.totient 28374405218467734420272678470 = 9727404584786789319616661088 := by
  rw [← show ((([(2, 1), (5, 1), (7, 1), (10103, 1), (40121611994270067476807, 1)] : List FactorBlock).map factorBlockValue).prod) = 28374405218467734420272678470 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyFourV_2, prime_twentyFourV_5, prime_twentyFourV_7, prime_twentyFourV_10103, prime_twentyFourV_40121611994270067476807]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyFourV_28374405218467734420272678471 : Nat.totient 28374405218467734420272678471 = 28374393322494917563508178600 := by
  rw [← show ((([(2385211, 1), (11895972816856762114661, 1)] : List FactorBlock).map factorBlockValue).prod) = 28374405218467734420272678471 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyFourV_2385211, prime_twentyFourV_11895972816856762114661]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyFourV_28374405218467734420272678472 : Nat.totient 28374405218467734420272678472 = 9458135072822578140090892800 := by
  rw [← show ((([(2, 3), (3, 2), (394088961367607422503787201, 1)] : List FactorBlock).map factorBlockValue).prod) = 28374405218467734420272678472 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyFourV_2, prime_twentyFourV_3, prime_twentyFourV_394088961367607422503787201]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyFourV_28374405218467734420272678473 : Nat.totient 28374405218467734420272678473 = 28168428116050273516247390160 := by
  rw [← show ((([(139, 1), (15271, 1), (13367324447885060939917, 1)] : List FactorBlock).map factorBlockValue).prod) = 28374405218467734420272678473 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyFourV_139, prime_twentyFourV_15271, prime_twentyFourV_13367324447885060939917]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyFourV_28374405218467734420272678474 : Nat.totient 28374405218467734420272678474 = 13803763337469637436943091152 := by
  rw [← show ((([(2, 1), (37, 1), (10124467, 1), (37872404380168564603, 1)] : List FactorBlock).map factorBlockValue).prod) = 28374405218467734420272678474 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyFourV_2, prime_twentyFourV_37, prime_twentyFourV_10124467, prime_twentyFourV_37872404380168564603]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyFourV_28374405218467734420272678475 : Nat.totient 28374405218467734420272678475 = 15040175526844246956512628000 := by
  rw [← show ((([(3, 1), (5, 2), (163, 1), (2321014741796951690819851, 1)] : List FactorBlock).map factorBlockValue).prod) = 28374405218467734420272678475 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyFourV_3, prime_twentyFourV_5, prime_twentyFourV_163, prime_twentyFourV_2321014741796951690819851]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyFourV_28374405218467734420272678476 : Nat.totient 28374405218467734420272678476 = 13440502779739994429621517312 := by
  rw [← show ((([(2, 2), (19, 1), (2712337, 1), (137647879701195599473, 1)] : List FactorBlock).map factorBlockValue).prod) = 28374405218467734420272678476 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyFourV_2, prime_twentyFourV_19, prime_twentyFourV_2712337, prime_twentyFourV_137647879701195599473]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyFourV_28374405218467734420272678477 : Nat.totient 28374405218467734420272678477 = 22088120373684613258430208000 := by
  rw [← show ((([(7, 1), (11, 1), (1283, 1), (7577, 1), (13331, 1), (2843474706519281, 1)] : List FactorBlock).map factorBlockValue).prod) = 28374405218467734420272678477 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyFourV_7, prime_twentyFourV_11, prime_twentyFourV_1283, prime_twentyFourV_7577, prime_twentyFourV_13331, prime_twentyFourV_2843474706519281]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyFourV_28374405218467734420272678478 : Nat.totient 28374405218467734420272678478 = 8695803009030871719360300000 := by
  rw [← show ((([(2, 1), (3, 1), (13, 1), (251, 1), (1449300501505145286560051, 1)] : List FactorBlock).map factorBlockValue).prod) = 28374405218467734420272678478 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyFourV_2, prime_twentyFourV_3, prime_twentyFourV_13, prime_twentyFourV_251, prime_twentyFourV_1449300501505145286560051]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyFourV_28374405218467734420272678479 : Nat.totient 28374405218467734420272678479 = 28183972968652424904895168800 := by
  rw [← show ((([(149, 1), (1052438042111, 1), (180943905644461, 1)] : List FactorBlock).map factorBlockValue).prod) = 28374405218467734420272678479 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyFourV_149, prime_twentyFourV_1052438042111, prime_twentyFourV_180943905644461]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyFourV_28374405218467734420272678480 : Nat.totient 28374405218467734420272678480 = 11349699219312628783342790144 := by
  rw [← show ((([(2, 4), (5, 1), (180533, 1), (1964627327030773765757, 1)] : List FactorBlock).map factorBlockValue).prod) = 28374405218467734420272678480 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyFourV_2, prime_twentyFourV_5, prime_twentyFourV_180533, prime_twentyFourV_1964627327030773765757]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyFourV_28374405218467734420272678481 : Nat.totient 28374405218467734420272678481 = 18916270145645156280181785168 := by
  rw [← show ((([(3, 6), (38922366554825424444818489, 1)] : List FactorBlock).map factorBlockValue).prod) = 28374405218467734420272678481 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyFourV_3, prime_twentyFourV_38922366554825424444818489]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyFourV_28374405218467734420272678482 : Nat.totient 28374405218467734420272678482 = 13841172438073443123926510880 := by
  rw [← show ((([(2, 1), (41, 1), (16492747, 1), (20980697268474035683, 1)] : List FactorBlock).map factorBlockValue).prod) = 28374405218467734420272678482 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyFourV_2, prime_twentyFourV_41, prime_twentyFourV_16492747, prime_twentyFourV_20980697268474035683]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyFourV_28374405218467734420272678483 : Nat.totient 28374405218467734420272678483 = 28374329369934833596855613160 := by
  rw [← show ((([(374093, 1), (75848532900823416691231, 1)] : List FactorBlock).map factorBlockValue).prod) = 28374405218467734420272678483 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyFourV_374093, prime_twentyFourV_75848532900823416691231]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyFourV_28374405218467734420272678484 : Nat.totient 28374405218467734420272678484 = 8106889790731887118593367008 := by
  rw [← show ((([(2, 2), (3, 1), (7, 1), (97523, 1), (3463701263446490329787, 1)] : List FactorBlock).map factorBlockValue).prod) = 28374405218467734420272678484 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyFourV_2, prime_twentyFourV_3, prime_twentyFourV_7, prime_twentyFourV_97523, prime_twentyFourV_3463701263446490329787]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

theorem freeKill_64TwentyFourV : certifiedKill 1 28374405218467734420272678384 99 := by
  norm_num [certifiedKill, windowDiscrepancy, Finset.sum_range_succ,
    phi_twentyFourV_28374405218467734420272678385, phi_twentyFourV_28374405218467734420272678386, phi_twentyFourV_28374405218467734420272678387,
    phi_twentyFourV_28374405218467734420272678388, phi_twentyFourV_28374405218467734420272678389, phi_twentyFourV_28374405218467734420272678390,
    phi_twentyFourV_28374405218467734420272678391, phi_twentyFourV_28374405218467734420272678392, phi_twentyFourV_28374405218467734420272678393,
    phi_twentyFourV_28374405218467734420272678394, phi_twentyFourV_28374405218467734420272678395, phi_twentyFourV_28374405218467734420272678396,
    phi_twentyFourV_28374405218467734420272678397, phi_twentyFourV_28374405218467734420272678398, phi_twentyFourV_28374405218467734420272678399,
    phi_twentyFourV_28374405218467734420272678400, phi_twentyFourV_28374405218467734420272678401, phi_twentyFourV_28374405218467734420272678402,
    phi_twentyFourV_28374405218467734420272678403, phi_twentyFourV_28374405218467734420272678404, phi_twentyFourV_28374405218467734420272678405,
    phi_twentyFourV_28374405218467734420272678406, phi_twentyFourV_28374405218467734420272678407, phi_twentyFourV_28374405218467734420272678408,
    phi_twentyFourV_28374405218467734420272678409, phi_twentyFourV_28374405218467734420272678410, phi_twentyFourV_28374405218467734420272678411,
    phi_twentyFourV_28374405218467734420272678412, phi_twentyFourV_28374405218467734420272678413, phi_twentyFourV_28374405218467734420272678414,
    phi_twentyFourV_28374405218467734420272678415, phi_twentyFourV_28374405218467734420272678416, phi_twentyFourV_28374405218467734420272678417,
    phi_twentyFourV_28374405218467734420272678418, phi_twentyFourV_28374405218467734420272678419, phi_twentyFourV_28374405218467734420272678420,
    phi_twentyFourV_28374405218467734420272678421, phi_twentyFourV_28374405218467734420272678422, phi_twentyFourV_28374405218467734420272678423,
    phi_twentyFourV_28374405218467734420272678424, phi_twentyFourV_28374405218467734420272678425, phi_twentyFourV_28374405218467734420272678426,
    phi_twentyFourV_28374405218467734420272678427, phi_twentyFourV_28374405218467734420272678428, phi_twentyFourV_28374405218467734420272678429,
    phi_twentyFourV_28374405218467734420272678430, phi_twentyFourV_28374405218467734420272678431, phi_twentyFourV_28374405218467734420272678432,
    phi_twentyFourV_28374405218467734420272678433, phi_twentyFourV_28374405218467734420272678434, phi_twentyFourV_28374405218467734420272678435,
    phi_twentyFourV_28374405218467734420272678436, phi_twentyFourV_28374405218467734420272678437, phi_twentyFourV_28374405218467734420272678438,
    phi_twentyFourV_28374405218467734420272678439, phi_twentyFourV_28374405218467734420272678440, phi_twentyFourV_28374405218467734420272678441,
    phi_twentyFourV_28374405218467734420272678442, phi_twentyFourV_28374405218467734420272678443, phi_twentyFourV_28374405218467734420272678444,
    phi_twentyFourV_28374405218467734420272678445, phi_twentyFourV_28374405218467734420272678446, phi_twentyFourV_28374405218467734420272678447,
    phi_twentyFourV_28374405218467734420272678448, phi_twentyFourV_28374405218467734420272678449, phi_twentyFourV_28374405218467734420272678450,
    phi_twentyFourV_28374405218467734420272678451, phi_twentyFourV_28374405218467734420272678452, phi_twentyFourV_28374405218467734420272678453,
    phi_twentyFourV_28374405218467734420272678454, phi_twentyFourV_28374405218467734420272678455, phi_twentyFourV_28374405218467734420272678456,
    phi_twentyFourV_28374405218467734420272678457, phi_twentyFourV_28374405218467734420272678458, phi_twentyFourV_28374405218467734420272678459,
    phi_twentyFourV_28374405218467734420272678460, phi_twentyFourV_28374405218467734420272678461, phi_twentyFourV_28374405218467734420272678462,
    phi_twentyFourV_28374405218467734420272678463, phi_twentyFourV_28374405218467734420272678464, phi_twentyFourV_28374405218467734420272678465,
    phi_twentyFourV_28374405218467734420272678466, phi_twentyFourV_28374405218467734420272678467, phi_twentyFourV_28374405218467734420272678468,
    phi_twentyFourV_28374405218467734420272678469, phi_twentyFourV_28374405218467734420272678470, phi_twentyFourV_28374405218467734420272678471,
    phi_twentyFourV_28374405218467734420272678472, phi_twentyFourV_28374405218467734420272678473, phi_twentyFourV_28374405218467734420272678474,
    phi_twentyFourV_28374405218467734420272678475, phi_twentyFourV_28374405218467734420272678476, phi_twentyFourV_28374405218467734420272678477,
    phi_twentyFourV_28374405218467734420272678478, phi_twentyFourV_28374405218467734420272678479, phi_twentyFourV_28374405218467734420272678480,
    phi_twentyFourV_28374405218467734420272678481, phi_twentyFourV_28374405218467734420272678482, phi_twentyFourV_28374405218467734420272678483,
    phi_twentyFourV_28374405218467734420272678484]

end TotientTailPeriodKiller
end Erdos249257
