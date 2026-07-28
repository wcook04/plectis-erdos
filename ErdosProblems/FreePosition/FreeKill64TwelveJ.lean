import Erdos249257.DiagonalPincerCertificatesT64

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

private def twelveJFastPow {M : Type*} [Monoid M] (a : M) (n : ℕ) : M :=
  Nat.binaryRec 1 (fun b _ r => if b then r * r * a else r * r) n

private theorem twelveJFastPow_eq_pow {M : Type*} [Monoid M] (a : M) (n : ℕ) :
    twelveJFastPow a n = a ^ n := by
  induction n using Nat.binaryRec with
  | zero => simp [twelveJFastPow, Nat.binaryRec_zero]
  | bit b n ih =>
      rw [twelveJFastPow, Nat.binaryRec_eq b n (by left; simp)]
      change (if b then twelveJFastPow a n * twelveJFastPow a n * a
        else twelveJFastPow a n * twelveJFastPow a n) = _
      rw [ih]
      cases b <;> simp [Nat.bit, two_mul, pow_add]

private theorem prime_twelveJ_2 : Nat.Prime 2 := by norm_num
private theorem prime_twelveJ_3923 : Nat.Prime 3923 := by norm_num
private theorem prime_twelveJ_8197093 : Nat.Prime 8197093 := by norm_num
private theorem prime_twelveJ_3 : Nat.Prime 3 := by norm_num
private theorem prime_twelveJ_5 : Nat.Prime 5 := by norm_num
private theorem prime_twelveJ_7 : Nat.Prime 7 := by norm_num
private theorem prime_twelveJ_11 : Nat.Prime 11 := by norm_num
private theorem prime_twelveJ_149 : Nat.Prime 149 := by norm_num
private theorem prime_twelveJ_929 : Nat.Prime 929 := by norm_num
private theorem prime_twelveJ_1796567 : Nat.Prime 1796567 := by norm_num
private theorem prime_twelveJ_110295707065568641 : Nat.Prime 110295707065568641 := by
  apply lucas_primality 110295707065568641 (26 : ZMod 110295707065568641)
  · rw [← twelveJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 7), (3, 2), (5, 1), (7, 1), (11, 1), (149, 1), (929, 1), (1796567, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 7), (3, 2), (5, 1), (7, 1), (11, 1), (149, 1), (929, 1), (1796567, 1)] : List FactorBlock).map factorBlockValue).prod = 110295707065568641 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_twelveJ_2
      · exact prime_twelveJ_3
      · exact prime_twelveJ_5
      · exact prime_twelveJ_7
      · exact prime_twelveJ_11
      · exact prime_twelveJ_149
      · exact prime_twelveJ_929
      · exact prime_twelveJ_1796567
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (26 : ZMod 110295707065568641) ^ 55147853532784320 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (26 : ZMod 110295707065568641) ^ 36765235688522880 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (26 : ZMod 110295707065568641) ^ 22059141413113728 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (26 : ZMod 110295707065568641) ^ 15756529580795520 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (26 : ZMod 110295707065568641) ^ 10026882460506240 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (26 : ZMod 110295707065568641) ^ 740239644735360 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (26 : ZMod 110295707065568641) ^ 118725195980160 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (26 : ZMod 110295707065568641) ^ 61392481920 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide

private theorem prime_twelveJ_18713 : Nat.Prime 18713 := by norm_num
private theorem prime_twelveJ_109469 : Nat.Prime 109469 := by norm_num
private theorem prime_twelveJ_1701179 : Nat.Prime 1701179 := by norm_num
private theorem prime_twelveJ_83 : Nat.Prime 83 := by norm_num
private theorem prime_twelveJ_2269 : Nat.Prime 2269 := by norm_num
private theorem prime_twelveJ_300239 : Nat.Prime 300239 := by norm_num
private theorem prime_twelveJ_1357034643673 : Nat.Prime 1357034643673 := by
  apply lucas_primality 1357034643673 (5 : ZMod 1357034643673)
  · rw [← twelveJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (3, 1), (83, 1), (2269, 1), (300239, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (3, 1), (83, 1), (2269, 1), (300239, 1)] : List FactorBlock).map factorBlockValue).prod = 1357034643673 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twelveJ_2
      · exact prime_twelveJ_3
      · exact prime_twelveJ_83
      · exact prime_twelveJ_2269
      · exact prime_twelveJ_300239
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 1357034643673) ^ 678517321836 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (5 : ZMod 1357034643673) ^ 452344881224 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (5 : ZMod 1357034643673) ^ 16349814984 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (5 : ZMod 1357034643673) ^ 598076088 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (5 : ZMod 1357034643673) ^ 4519848 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide

private theorem prime_twelveJ_71 : Nat.Prime 71 := by norm_num
private theorem prime_twelveJ_11633 : Nat.Prime 11633 := by norm_num
private theorem prime_twelveJ_43 : Nat.Prime 43 := by norm_num
private theorem prime_twelveJ_109 : Nat.Prime 109 := by norm_num
private theorem prime_twelveJ_173 : Nat.Prime 173 := by norm_num
private theorem prime_twelveJ_311 : Nat.Prime 311 := by norm_num
private theorem prime_twelveJ_13 : Nat.Prime 13 := by norm_num
private theorem prime_twelveJ_2169877 : Nat.Prime 2169877 := by norm_num
private theorem prime_twelveJ_789835229 : Nat.Prime 789835229 := by
  apply lucas_primality 789835229 (10 : ZMod 789835229)
  · rw [← twelveJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (7, 1), (13, 1), (2169877, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (7, 1), (13, 1), (2169877, 1)] : List FactorBlock).map factorBlockValue).prod = 789835229 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twelveJ_2
      · exact prime_twelveJ_7
      · exact prime_twelveJ_13
      · exact prime_twelveJ_2169877
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (10 : ZMod 789835229) ^ 394917614 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (10 : ZMod 789835229) ^ 112833604 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (10 : ZMod 789835229) ^ 60756556 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (10 : ZMod 789835229) ^ 364 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide

private theorem prime_twelveJ_86881875191 : Nat.Prime 86881875191 := by
  apply lucas_primality 86881875191 (11 : ZMod 86881875191)
  · rw [← twelveJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 1), (11, 1), (789835229, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 1), (11, 1), (789835229, 1)] : List FactorBlock).map factorBlockValue).prod = 86881875191 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twelveJ_2
      · exact prime_twelveJ_5
      · exact prime_twelveJ_11
      · exact prime_twelveJ_789835229
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 86881875191) ^ 43440937595 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (11 : ZMod 86881875191) ^ 17376375038 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (11 : ZMod 86881875191) ^ 7898352290 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (11 : ZMod 86881875191) ^ 110 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide

private theorem prime_twelveJ_8588487709947216218393 : Nat.Prime 8588487709947216218393 := by
  apply lucas_primality 8588487709947216218393 (5 : ZMod 8588487709947216218393)
  · rw [← twelveJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (7, 2), (43, 1), (109, 1), (173, 1), (311, 1), (86881875191, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (7, 2), (43, 1), (109, 1), (173, 1), (311, 1), (86881875191, 1)] : List FactorBlock).map factorBlockValue).prod = 8588487709947216218393 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_twelveJ_2
      · exact prime_twelveJ_7
      · exact prime_twelveJ_43
      · exact prime_twelveJ_109
      · exact prime_twelveJ_173
      · exact prime_twelveJ_311
      · exact prime_twelveJ_86881875191
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 8588487709947216218393) ^ 4294243854973608109196 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (5 : ZMod 8588487709947216218393) ^ 1226926815706745174056 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (5 : ZMod 8588487709947216218393) ^ 199732272324353865544 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (5 : ZMod 8588487709947216218393) ^ 78793465228873543288 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (5 : ZMod 8588487709947216218393) ^ 49644437629752694904 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (5 : ZMod 8588487709947216218393) ^ 27615716109155036072 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (5 : ZMod 8588487709947216218393) ^ 98852467112 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide

private theorem prime_twelveJ_373 : Nat.Prime 373 := by norm_num
private theorem prime_twelveJ_9721 : Nat.Prime 9721 := by norm_num
private theorem prime_twelveJ_36259331 : Nat.Prime 36259331 := by
  apply lucas_primality 36259331 (2 : ZMod 36259331)
  · rw [← twelveJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 1), (373, 1), (9721, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 1), (373, 1), (9721, 1)] : List FactorBlock).map factorBlockValue).prod = 36259331 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twelveJ_2
      · exact prime_twelveJ_5
      · exact prime_twelveJ_373
      · exact prime_twelveJ_9721
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 36259331) ^ 18129665 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (2 : ZMod 36259331) ^ 7251866 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (2 : ZMod 36259331) ^ 97210 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (2 : ZMod 36259331) ^ 3730 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide

private theorem prime_twelveJ_1483 : Nat.Prime 1483 := by norm_num
private theorem prime_twelveJ_25639 : Nat.Prime 25639 := by norm_num
private theorem prime_twelveJ_5669 : Nat.Prime 5669 := by norm_num
private theorem prime_twelveJ_6302833 : Nat.Prime 6302833 := by norm_num
private theorem prime_twelveJ_75633997 : Nat.Prime 75633997 := by
  apply lucas_primality 75633997 (2 : ZMod 75633997)
  · rw [← twelveJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (6302833, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (6302833, 1)] : List FactorBlock).map factorBlockValue).prod = 75633997 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twelveJ_2
      · exact prime_twelveJ_3
      · exact prime_twelveJ_6302833
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 75633997) ^ 37816998 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (2 : ZMod 75633997) ^ 25211332 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (2 : ZMod 75633997) ^ 12 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide

private theorem prime_twelveJ_857538257987 : Nat.Prime 857538257987 := by
  apply lucas_primality 857538257987 (2 : ZMod 857538257987)
  · rw [← twelveJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5669, 1), (75633997, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5669, 1), (75633997, 1)] : List FactorBlock).map factorBlockValue).prod = 857538257987 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twelveJ_2
      · exact prime_twelveJ_5669
      · exact prime_twelveJ_75633997
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 857538257987) ^ 428769128993 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (2 : ZMod 857538257987) ^ 151267994 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (2 : ZMod 857538257987) ^ 11338 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide

private theorem prime_twelveJ_391270390764624620629 : Nat.Prime 391270390764624620629 := by
  apply lucas_primality 391270390764624620629 (2 : ZMod 391270390764624620629)
  · rw [← twelveJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (1483, 1), (25639, 1), (857538257987, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (1483, 1), (25639, 1), (857538257987, 1)] : List FactorBlock).map factorBlockValue).prod = 391270390764624620629 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twelveJ_2
      · exact prime_twelveJ_3
      · exact prime_twelveJ_1483
      · exact prime_twelveJ_25639
      · exact prime_twelveJ_857538257987
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 391270390764624620629) ^ 195635195382312310314 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (2 : ZMod 391270390764624620629) ^ 130423463588208206876 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (2 : ZMod 391270390764624620629) ^ 263837080758344316 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (2 : ZMod 391270390764624620629) ^ 15260750839136652 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (2 : ZMod 391270390764624620629) ^ 456271644 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide

private theorem prime_twelveJ_17 : Nat.Prime 17 := by norm_num
private theorem prime_twelveJ_19 : Nat.Prime 19 := by norm_num
private theorem prime_twelveJ_23 : Nat.Prime 23 := by norm_num
private theorem prime_twelveJ_29 : Nat.Prime 29 := by norm_num
private theorem prime_twelveJ_31 : Nat.Prime 31 := by norm_num
private theorem prime_twelveJ_37 : Nat.Prime 37 := by norm_num
private theorem prime_twelveJ_41 : Nat.Prime 41 := by norm_num
private theorem prime_twelveJ_47 : Nat.Prime 47 := by norm_num
private theorem prime_twelveJ_53 : Nat.Prime 53 := by norm_num
private theorem prime_twelveJ_59 : Nat.Prime 59 := by norm_num
private theorem prime_twelveJ_61 : Nat.Prime 61 := by norm_num
private theorem prime_twelveJ_181 : Nat.Prime 181 := by norm_num
private theorem prime_twelveJ_317 : Nat.Prime 317 := by norm_num
private theorem prime_twelveJ_372377 : Nat.Prime 372377 := by norm_num
private theorem prime_twelveJ_6305347 : Nat.Prime 6305347 := by norm_num
private theorem prime_twelveJ_441374291 : Nat.Prime 441374291 := by
  apply lucas_primality 441374291 (6 : ZMod 441374291)
  · rw [← twelveJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 1), (7, 1), (6305347, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 1), (7, 1), (6305347, 1)] : List FactorBlock).map factorBlockValue).prod = 441374291 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twelveJ_2
      · exact prime_twelveJ_5
      · exact prime_twelveJ_7
      · exact prime_twelveJ_6305347
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 441374291) ^ 220687145 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (6 : ZMod 441374291) ^ 88274858 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (6 : ZMod 441374291) ^ 63053470 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (6 : ZMod 441374291) ^ 70 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide

private theorem prime_twelveJ_4491424785217 : Nat.Prime 4491424785217 := by
  apply lucas_primality 4491424785217 (7 : ZMod 4491424785217)
  · rw [← twelveJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 6), (3, 1), (53, 1), (441374291, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 6), (3, 1), (53, 1), (441374291, 1)] : List FactorBlock).map factorBlockValue).prod = 4491424785217 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twelveJ_2
      · exact prime_twelveJ_3
      · exact prime_twelveJ_53
      · exact prime_twelveJ_441374291
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 4491424785217) ^ 2245712392608 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (7 : ZMod 4491424785217) ^ 1497141595072 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (7 : ZMod 4491424785217) ^ 84743863872 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (7 : ZMod 4491424785217) ^ 10176 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide

private theorem prime_twelveJ_702451380642795339781 : Nat.Prime 702451380642795339781 := by
  apply lucas_primality 702451380642795339781 (2 : ZMod 702451380642795339781)
  · rw [← twelveJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (5, 1), (7, 1), (372377, 1), (4491424785217, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (5, 1), (7, 1), (372377, 1), (4491424785217, 1)] : List FactorBlock).map factorBlockValue).prod = 702451380642795339781 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_twelveJ_2
      · exact prime_twelveJ_3
      · exact prime_twelveJ_5
      · exact prime_twelveJ_7
      · exact prime_twelveJ_372377
      · exact prime_twelveJ_4491424785217
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 702451380642795339781) ^ 351225690321397669890 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (2 : ZMod 702451380642795339781) ^ 234150460214265113260 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (2 : ZMod 702451380642795339781) ^ 140490276128559067956 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (2 : ZMod 702451380642795339781) ^ 100350197234685048540 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (2 : ZMod 702451380642795339781) ^ 1886398409791140 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (2 : ZMod 702451380642795339781) ^ 156398340 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide

private theorem prime_twelveJ_247262885986263959602913 : Nat.Prime 247262885986263959602913 := by
  apply lucas_primality 247262885986263959602913 (3 : ZMod 247262885986263959602913)
  · rw [← twelveJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 5), (11, 1), (702451380642795339781, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 5), (11, 1), (702451380642795339781, 1)] : List FactorBlock).map factorBlockValue).prod = 247262885986263959602913 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twelveJ_2
      · exact prime_twelveJ_11
      · exact prime_twelveJ_702451380642795339781
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 247262885986263959602913) ^ 123631442993131979801456 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (3 : ZMod 247262885986263959602913) ^ 22478444180569450872992 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (3 : ZMod 247262885986263959602913) ^ 352 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide

private theorem prime_twelveJ_115903 : Nat.Prime 115903 := by norm_num
private theorem prime_twelveJ_131 : Nat.Prime 131 := by norm_num
private theorem prime_twelveJ_9833 : Nat.Prime 9833 := by norm_num
private theorem prime_twelveJ_32244294937 : Nat.Prime 32244294937 := by
  apply lucas_primality 32244294937 (10 : ZMod 32244294937)
  · rw [← twelveJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (3, 1), (7, 1), (131, 1), (149, 1), (9833, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (3, 1), (7, 1), (131, 1), (149, 1), (9833, 1)] : List FactorBlock).map factorBlockValue).prod = 32244294937 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_twelveJ_2
      · exact prime_twelveJ_3
      · exact prime_twelveJ_7
      · exact prime_twelveJ_131
      · exact prime_twelveJ_149
      · exact prime_twelveJ_9833
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 32244294937) ^ 16122147468 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (10 : ZMod 32244294937) ^ 10748098312 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (10 : ZMod 32244294937) ^ 4606327848 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (10 : ZMod 32244294937) ^ 246139656 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (10 : ZMod 32244294937) ^ 216404664 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (10 : ZMod 32244294937) ^ 3279192 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide

private theorem prime_twelveJ_457 : Nat.Prime 457 := by norm_num
private theorem prime_twelveJ_1433 : Nat.Prime 1433 := by norm_num
private theorem prime_twelveJ_8783 : Nat.Prime 8783 := by norm_num
private theorem prime_twelveJ_1898100541591 : Nat.Prime 1898100541591 := by
  apply lucas_primality 1898100541591 (3 : ZMod 1898100541591)
  · rw [← twelveJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (5, 1), (11, 1), (457, 1), (1433, 1), (8783, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (5, 1), (11, 1), (457, 1), (1433, 1), (8783, 1)] : List FactorBlock).map factorBlockValue).prod = 1898100541591 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_twelveJ_2
      · exact prime_twelveJ_3
      · exact prime_twelveJ_5
      · exact prime_twelveJ_11
      · exact prime_twelveJ_457
      · exact prime_twelveJ_1433
      · exact prime_twelveJ_8783
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1898100541591) ^ 949050270795 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (3 : ZMod 1898100541591) ^ 632700180530 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (3 : ZMod 1898100541591) ^ 379620108318 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (3 : ZMod 1898100541591) ^ 172554594690 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (3 : ZMod 1898100541591) ^ 4153392870 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (3 : ZMod 1898100541591) ^ 1324564230 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (3 : ZMod 1898100541591) ^ 216110730 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide

private theorem prime_twelveJ_401 : Nat.Prime 401 := by norm_num
private theorem prime_twelveJ_11069 : Nat.Prime 11069 := by norm_num
private theorem prime_twelveJ_53269 : Nat.Prime 53269 := by norm_num
private theorem prime_twelveJ_384973 : Nat.Prime 384973 := by norm_num
private theorem prime_twelveJ_1901 : Nat.Prime 1901 := by norm_num
private theorem prime_twelveJ_18979 : Nat.Prime 18979 := by norm_num
private theorem prime_twelveJ_72158159 : Nat.Prime 72158159 := by
  apply lucas_primality 72158159 (13 : ZMod 72158159)
  · rw [← twelveJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (1901, 1), (18979, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (1901, 1), (18979, 1)] : List FactorBlock).map factorBlockValue).prod = 72158159 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twelveJ_2
      · exact prime_twelveJ_1901
      · exact prime_twelveJ_18979
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (13 : ZMod 72158159) ^ 36079079 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (13 : ZMod 72158159) ^ 37958 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (13 : ZMod 72158159) ^ 3802 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide

private theorem prime_twelveJ_20000838920189041 : Nat.Prime 20000838920189041 := by
  apply lucas_primality 20000838920189041 (7 : ZMod 20000838920189041)
  · rw [← twelveJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 4), (3, 2), (5, 1), (384973, 1), (72158159, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 4), (3, 2), (5, 1), (384973, 1), (72158159, 1)] : List FactorBlock).map factorBlockValue).prod = 20000838920189041 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twelveJ_2
      · exact prime_twelveJ_3
      · exact prime_twelveJ_5
      · exact prime_twelveJ_384973
      · exact prime_twelveJ_72158159
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 20000838920189041) ^ 10000419460094520 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (7 : ZMod 20000838920189041) ^ 6666946306729680 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (7 : ZMod 20000838920189041) ^ 4000167784037808 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (7 : ZMod 20000838920189041) ^ 51953874480 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (7 : ZMod 20000838920189041) ^ 277180560 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide

private theorem prime_twelveJ_114593 : Nat.Prime 114593 := by norm_num
private theorem prime_twelveJ_42857783 : Nat.Prime 42857783 := by
  apply lucas_primality 42857783 (5 : ZMod 42857783)
  · rw [← twelveJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (11, 1), (17, 1), (114593, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (11, 1), (17, 1), (114593, 1)] : List FactorBlock).map factorBlockValue).prod = 42857783 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twelveJ_2
      · exact prime_twelveJ_11
      · exact prime_twelveJ_17
      · exact prime_twelveJ_114593
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 42857783) ^ 21428891 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (5 : ZMod 42857783) ^ 3896162 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (5 : ZMod 42857783) ^ 2521046 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (5 : ZMod 42857783) ^ 374 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide

private theorem prime_twelveJ_30429025931 : Nat.Prime 30429025931 := by
  apply lucas_primality 30429025931 (2 : ZMod 30429025931)
  · rw [← twelveJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 1), (71, 1), (42857783, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 1), (71, 1), (42857783, 1)] : List FactorBlock).map factorBlockValue).prod = 30429025931 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twelveJ_2
      · exact prime_twelveJ_5
      · exact prime_twelveJ_71
      · exact prime_twelveJ_42857783
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 30429025931) ^ 15214512965 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (2 : ZMod 30429025931) ^ 6085805186 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (2 : ZMod 30429025931) ^ 428577830 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (2 : ZMod 30429025931) ^ 710 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide

private theorem prime_twelveJ_81047 : Nat.Prime 81047 := by norm_num
private theorem prime_twelveJ_14999741 : Nat.Prime 14999741 := by norm_num
private theorem prime_twelveJ_11655978276633277 : Nat.Prime 11655978276633277 := by
  apply lucas_primality 11655978276633277 (2 : ZMod 11655978276633277)
  · rw [← twelveJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (17, 1), (47, 1), (81047, 1), (14999741, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (17, 1), (47, 1), (81047, 1), (14999741, 1)] : List FactorBlock).map factorBlockValue).prod = 11655978276633277 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_twelveJ_2
      · exact prime_twelveJ_3
      · exact prime_twelveJ_17
      · exact prime_twelveJ_47
      · exact prime_twelveJ_81047
      · exact prime_twelveJ_14999741
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 11655978276633277) ^ 5827989138316638 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (2 : ZMod 11655978276633277) ^ 3885326092211092 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (2 : ZMod 11655978276633277) ^ 685645780978428 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (2 : ZMod 11655978276633277) ^ 247999537800708 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (2 : ZMod 11655978276633277) ^ 143817516708 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (2 : ZMod 11655978276633277) ^ 777078636 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide

private theorem prime_twelveJ_116559782766332771 : Nat.Prime 116559782766332771 := by
  apply lucas_primality 116559782766332771 (2 : ZMod 116559782766332771)
  · rw [← twelveJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 1), (11655978276633277, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 1), (11655978276633277, 1)] : List FactorBlock).map factorBlockValue).prod = 116559782766332771 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twelveJ_2
      · exact prime_twelveJ_5
      · exact prime_twelveJ_11655978276633277
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 116559782766332771) ^ 58279891383166385 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (2 : ZMod 116559782766332771) ^ 23311956553266554 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (2 : ZMod 116559782766332771) ^ 10 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide

private theorem prime_twelveJ_277 : Nat.Prime 277 := by norm_num
private theorem prime_twelveJ_1965553 : Nat.Prime 1965553 := by norm_num
private theorem prime_twelveJ_66828803 : Nat.Prime 66828803 := by
  apply lucas_primality 66828803 (2 : ZMod 66828803)
  · rw [← twelveJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (17, 1), (1965553, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (17, 1), (1965553, 1)] : List FactorBlock).map factorBlockValue).prod = 66828803 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twelveJ_2
      · exact prime_twelveJ_17
      · exact prime_twelveJ_1965553
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 66828803) ^ 33414401 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (2 : ZMod 66828803) ^ 3931106 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (2 : ZMod 66828803) ^ 34 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide

private theorem prime_twelveJ_111069470587 : Nat.Prime 111069470587 := by
  apply lucas_primality 111069470587 (11 : ZMod 111069470587)
  · rw [← twelveJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (277, 1), (66828803, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (277, 1), (66828803, 1)] : List FactorBlock).map factorBlockValue).prod = 111069470587 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twelveJ_2
      · exact prime_twelveJ_3
      · exact prime_twelveJ_277
      · exact prime_twelveJ_66828803
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 111069470587) ^ 55534735293 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (11 : ZMod 111069470587) ^ 37023156862 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (11 : ZMod 111069470587) ^ 400972818 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (11 : ZMod 111069470587) ^ 1662 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide

private theorem prime_twelveJ_6442029294047 : Nat.Prime 6442029294047 := by
  apply lucas_primality 6442029294047 (5 : ZMod 6442029294047)
  · rw [← twelveJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (29, 1), (111069470587, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (29, 1), (111069470587, 1)] : List FactorBlock).map factorBlockValue).prod = 6442029294047 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twelveJ_2
      · exact prime_twelveJ_29
      · exact prime_twelveJ_111069470587
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 6442029294047) ^ 3221014647023 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (5 : ZMod 6442029294047) ^ 222138941174 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (5 : ZMod 6442029294047) ^ 58 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide

private theorem prime_twelveJ_14081 : Nat.Prime 14081 := by norm_num
private theorem prime_twelveJ_4603 : Nat.Prime 4603 := by norm_num
private theorem prime_twelveJ_8369 : Nat.Prime 8369 := by norm_num
private theorem prime_twelveJ_539315099 : Nat.Prime 539315099 := by
  apply lucas_primality 539315099 (2 : ZMod 539315099)
  · rw [← twelveJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (7, 1), (4603, 1), (8369, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (7, 1), (4603, 1), (8369, 1)] : List FactorBlock).map factorBlockValue).prod = 539315099 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twelveJ_2
      · exact prime_twelveJ_7
      · exact prime_twelveJ_4603
      · exact prime_twelveJ_8369
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 539315099) ^ 269657549 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (2 : ZMod 539315099) ^ 77045014 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (2 : ZMod 539315099) ^ 117166 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (2 : ZMod 539315099) ^ 64442 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide

private theorem prime_twelveJ_440457562723103 : Nat.Prime 440457562723103 := by
  apply lucas_primality 440457562723103 (5 : ZMod 440457562723103)
  · rw [← twelveJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (29, 1), (14081, 1), (539315099, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (29, 1), (14081, 1), (539315099, 1)] : List FactorBlock).map factorBlockValue).prod = 440457562723103 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twelveJ_2
      · exact prime_twelveJ_29
      · exact prime_twelveJ_14081
      · exact prime_twelveJ_539315099
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 440457562723103) ^ 220228781361551 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (5 : ZMod 440457562723103) ^ 15188191818038 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (5 : ZMod 440457562723103) ^ 31280275742 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (5 : ZMod 440457562723103) ^ 816698 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide

private theorem prime_twelveJ_210193 : Nat.Prime 210193 := by norm_num
private theorem prime_twelveJ_439 : Nat.Prime 439 := by norm_num
private theorem prime_twelveJ_853 : Nat.Prime 853 := by norm_num
private theorem prime_twelveJ_151 : Nat.Prime 151 := by norm_num
private theorem prime_twelveJ_479 : Nat.Prime 479 := by norm_num
private theorem prime_twelveJ_6343 : Nat.Prime 6343 := by norm_num
private theorem prime_twelveJ_44960719007 : Nat.Prime 44960719007 := by
  apply lucas_primality 44960719007 (5 : ZMod 44960719007)
  · rw [← twelveJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (7, 2), (151, 1), (479, 1), (6343, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (7, 2), (151, 1), (479, 1), (6343, 1)] : List FactorBlock).map factorBlockValue).prod = 44960719007 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twelveJ_2
      · exact prime_twelveJ_7
      · exact prime_twelveJ_151
      · exact prime_twelveJ_479
      · exact prime_twelveJ_6343
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 44960719007) ^ 22480359503 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (5 : ZMod 44960719007) ^ 6422959858 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (5 : ZMod 44960719007) ^ 297753106 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (5 : ZMod 44960719007) ^ 93863714 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (5 : ZMod 44960719007) ^ 7088242 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide

private theorem prime_twelveJ_1348821570211 : Nat.Prime 1348821570211 := by
  apply lucas_primality 1348821570211 (2 : ZMod 1348821570211)
  · rw [← twelveJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (5, 1), (44960719007, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (5, 1), (44960719007, 1)] : List FactorBlock).map factorBlockValue).prod = 1348821570211 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twelveJ_2
      · exact prime_twelveJ_3
      · exact prime_twelveJ_5
      · exact prime_twelveJ_44960719007
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1348821570211) ^ 674410785105 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (2 : ZMod 1348821570211) ^ 449607190070 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (2 : ZMod 1348821570211) ^ 269764314042 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (2 : ZMod 1348821570211) ^ 30 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide

private theorem prime_twelveJ_8081426670915240593 : Nat.Prime 8081426670915240593 := by
  apply lucas_primality 8081426670915240593 (3 : ZMod 8081426670915240593)
  · rw [← twelveJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 4), (439, 1), (853, 1), (1348821570211, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 4), (439, 1), (853, 1), (1348821570211, 1)] : List FactorBlock).map factorBlockValue).prod = 8081426670915240593 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twelveJ_2
      · exact prime_twelveJ_439
      · exact prime_twelveJ_853
      · exact prime_twelveJ_1348821570211
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 8081426670915240593) ^ 4040713335457620296 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (3 : ZMod 8081426670915240593) ^ 18408716790239728 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (3 : ZMod 8081426670915240593) ^ 9474122709162064 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (3 : ZMod 8081426670915240593) ^ 5991472 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide

private theorem prime_twelveJ_11249345925914014905457 : Nat.Prime 11249345925914014905457 := by
  apply lucas_primality 11249345925914014905457 (5 : ZMod 11249345925914014905457)
  · rw [← twelveJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 4), (3, 1), (29, 1), (8081426670915240593, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 4), (3, 1), (29, 1), (8081426670915240593, 1)] : List FactorBlock).map factorBlockValue).prod = 11249345925914014905457 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twelveJ_2
      · exact prime_twelveJ_3
      · exact prime_twelveJ_29
      · exact prime_twelveJ_8081426670915240593
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 11249345925914014905457) ^ 5624672962957007452728 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (5 : ZMod 11249345925914014905457) ^ 3749781975304671635152 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (5 : ZMod 11249345925914014905457) ^ 387908480203931548464 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (5 : ZMod 11249345925914014905457) ^ 1392 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide

private theorem prime_twelveJ_8596663 : Nat.Prime 8596663 := by norm_num
private theorem prime_twelveJ_12269 : Nat.Prime 12269 := by norm_num
private theorem prime_twelveJ_20538307 : Nat.Prime 20538307 := by
  apply lucas_primality 20538307 (2 : ZMod 20538307)
  · rw [← twelveJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 3), (31, 1), (12269, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 3), (31, 1), (12269, 1)] : List FactorBlock).map factorBlockValue).prod = 20538307 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twelveJ_2
      · exact prime_twelveJ_3
      · exact prime_twelveJ_31
      · exact prime_twelveJ_12269
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 20538307) ^ 10269153 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (2 : ZMod 20538307) ^ 6846102 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (2 : ZMod 20538307) ^ 662526 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (2 : ZMod 20538307) ^ 1674 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide

private theorem prime_twelveJ_409 : Nat.Prime 409 := by norm_num
private theorem prime_twelveJ_827 : Nat.Prime 827 := by norm_num
private theorem prime_twelveJ_219857951 : Nat.Prime 219857951 := by
  apply lucas_primality 219857951 (17 : ZMod 219857951)
  · rw [← twelveJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 2), (13, 1), (409, 1), (827, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 2), (13, 1), (409, 1), (827, 1)] : List FactorBlock).map factorBlockValue).prod = 219857951 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twelveJ_2
      · exact prime_twelveJ_5
      · exact prime_twelveJ_13
      · exact prime_twelveJ_409
      · exact prime_twelveJ_827
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (17 : ZMod 219857951) ^ 109928975 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (17 : ZMod 219857951) ^ 43971590 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (17 : ZMod 219857951) ^ 16912150 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (17 : ZMod 219857951) ^ 537550 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (17 : ZMod 219857951) ^ 265850 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide

private theorem prime_twelveJ_8233 : Nat.Prime 8233 := by norm_num
private theorem prime_twelveJ_93811 : Nat.Prime 93811 := by norm_num
private theorem prime_twelveJ_8274073 : Nat.Prime 8274073 := by norm_num
private theorem prime_twelveJ_1429 : Nat.Prime 1429 := by norm_num
private theorem prime_twelveJ_217223 : Nat.Prime 217223 := by norm_num
private theorem prime_twelveJ_277508030299 : Nat.Prime 277508030299 := by
  apply lucas_primality 277508030299 (3 : ZMod 277508030299)
  · rw [← twelveJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (149, 1), (1429, 1), (217223, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (149, 1), (1429, 1), (217223, 1)] : List FactorBlock).map factorBlockValue).prod = 277508030299 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twelveJ_2
      · exact prime_twelveJ_3
      · exact prime_twelveJ_149
      · exact prime_twelveJ_1429
      · exact prime_twelveJ_217223
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 277508030299) ^ 138754015149 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (3 : ZMod 277508030299) ^ 92502676766 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (3 : ZMod 277508030299) ^ 1862470002 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (3 : ZMod 277508030299) ^ 194197362 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (3 : ZMod 277508030299) ^ 1277526 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide

private theorem prime_twelveJ_1576355845470429690015148801 : Nat.Prime 1576355845470429690015148801 := by
  apply lucas_primality 1576355845470429690015148801 (101 : ZMod 1576355845470429690015148801)
  · rw [← twelveJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 8), (3, 2), (5, 2), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 8), (3, 2), (5, 2), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod = 1576355845470429690015148801 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_twelveJ_2
      · exact prime_twelveJ_3
      · exact prime_twelveJ_5
      · exact prime_twelveJ_7
      · exact prime_twelveJ_11
      · exact prime_twelveJ_13
      · exact prime_twelveJ_17
      · exact prime_twelveJ_19
      · exact prime_twelveJ_23
      · exact prime_twelveJ_29
      · exact prime_twelveJ_31
      · exact prime_twelveJ_37
      · exact prime_twelveJ_41
      · exact prime_twelveJ_43
      · exact prime_twelveJ_47
      · exact prime_twelveJ_53
      · exact prime_twelveJ_59
      · exact prime_twelveJ_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (101 : ZMod 1576355845470429690015148801) ^ 788177922735214845007574400 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (101 : ZMod 1576355845470429690015148801) ^ 525451948490143230005049600 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (101 : ZMod 1576355845470429690015148801) ^ 315271169094085938003029760 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (101 : ZMod 1576355845470429690015148801) ^ 225193692210061384287878400 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (101 : ZMod 1576355845470429690015148801) ^ 143305076860948153637740800 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (101 : ZMod 1576355845470429690015148801) ^ 121258141959263822308857600 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (101 : ZMod 1576355845470429690015148801) ^ 92726814439437040589126400 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (101 : ZMod 1576355845470429690015148801) ^ 82966097130022615263955200 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (101 : ZMod 1576355845470429690015148801) ^ 68537210672627377826745600 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (101 : ZMod 1576355845470429690015148801) ^ 54357098119669989310867200 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (101 : ZMod 1576355845470429690015148801) ^ 50850188563562248065004800 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (101 : ZMod 1576355845470429690015148801) ^ 42604212039741342973382400 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (101 : ZMod 1576355845470429690015148801) ^ 38447703548059260732076800 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (101 : ZMod 1576355845470429690015148801) ^ 36659438266754178837561600 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (101 : ZMod 1576355845470429690015148801) ^ 33539486073838929574790400 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (101 : ZMod 1576355845470429690015148801) ^ 29742563122083579056889600 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (101 : ZMod 1576355845470429690015148801) ^ 26717895685939486271443200 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (101 : ZMod 1576355845470429690015148801) ^ 25841899106072617869100800 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide

private theorem prime_twelveJ_1049 : Nat.Prime 1049 := by norm_num
private theorem prime_twelveJ_139537 : Nat.Prime 139537 := by norm_num
private theorem prime_twelveJ_5879 : Nat.Prime 5879 := by norm_num
private theorem prime_twelveJ_175593973 : Nat.Prime 175593973 := by
  apply lucas_primality 175593973 (5 : ZMod 175593973)
  · rw [← twelveJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (19, 1), (131, 1), (5879, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (19, 1), (131, 1), (5879, 1)] : List FactorBlock).map factorBlockValue).prod = 175593973 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twelveJ_2
      · exact prime_twelveJ_3
      · exact prime_twelveJ_19
      · exact prime_twelveJ_131
      · exact prime_twelveJ_5879
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 175593973) ^ 87796986 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (5 : ZMod 175593973) ^ 58531324 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (5 : ZMod 175593973) ^ 9241788 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (5 : ZMod 175593973) ^ 1340412 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (5 : ZMod 175593973) ^ 29868 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide

private theorem prime_twelveJ_229 : Nat.Prime 229 := by norm_num
private theorem prime_twelveJ_372958561 : Nat.Prime 372958561 := by
  apply lucas_primality 372958561 (11 : ZMod 372958561)
  · rw [← twelveJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 5), (3, 3), (5, 1), (13, 1), (29, 1), (229, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 5), (3, 3), (5, 1), (13, 1), (29, 1), (229, 1)] : List FactorBlock).map factorBlockValue).prod = 372958561 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_twelveJ_2
      · exact prime_twelveJ_3
      · exact prime_twelveJ_5
      · exact prime_twelveJ_13
      · exact prime_twelveJ_29
      · exact prime_twelveJ_229
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 372958561) ^ 186479280 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (11 : ZMod 372958561) ^ 124319520 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (11 : ZMod 372958561) ^ 74591712 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (11 : ZMod 372958561) ^ 28689120 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (11 : ZMod 372958561) ^ 12860640 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (11 : ZMod 372958561) ^ 1628640 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide

private theorem prime_twelveJ_55197867029 : Nat.Prime 55197867029 := by
  apply lucas_primality 55197867029 (2 : ZMod 55197867029)
  · rw [← twelveJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (37, 1), (372958561, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (37, 1), (372958561, 1)] : List FactorBlock).map factorBlockValue).prod = 55197867029 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twelveJ_2
      · exact prime_twelveJ_37
      · exact prime_twelveJ_372958561
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 55197867029) ^ 27598933514 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (2 : ZMod 55197867029) ^ 1491834244 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (2 : ZMod 55197867029) ^ 148 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide

private theorem prime_twelveJ_137251 : Nat.Prime 137251 := by norm_num
private theorem prime_twelveJ_163 : Nat.Prime 163 := by norm_num
private theorem prime_twelveJ_503 : Nat.Prime 503 := by norm_num
private theorem prime_twelveJ_1976731 : Nat.Prime 1976731 := by norm_num
private theorem prime_twelveJ_2112239 : Nat.Prime 2112239 := by norm_num
private theorem prime_twelveJ_9396985754191469517451 : Nat.Prime 9396985754191469517451 := by
  apply lucas_primality 9396985754191469517451 (2 : ZMod 9396985754191469517451)
  · rw [← twelveJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 2), (5, 2), (61, 1), (163, 1), (503, 1), (1976731, 1), (2112239, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 2), (5, 2), (61, 1), (163, 1), (503, 1), (1976731, 1), (2112239, 1)] : List FactorBlock).map factorBlockValue).prod = 9396985754191469517451 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_twelveJ_2
      · exact prime_twelveJ_3
      · exact prime_twelveJ_5
      · exact prime_twelveJ_61
      · exact prime_twelveJ_163
      · exact prime_twelveJ_503
      · exact prime_twelveJ_1976731
      · exact prime_twelveJ_2112239
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 9396985754191469517451) ^ 4698492877095734758725 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (2 : ZMod 9396985754191469517451) ^ 3132328584730489839150 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (2 : ZMod 9396985754191469517451) ^ 1879397150838293903490 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (2 : ZMod 9396985754191469517451) ^ 154048946790024090450 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (2 : ZMod 9396985754191469517451) ^ 57650219350867911150 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (2 : ZMod 9396985754191469517451) ^ 18681880227020814150 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (2 : ZMod 9396985754191469517451) ^ 4753800974533950 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (2 : ZMod 9396985754191469517451) ^ 4448826933974550 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide

private theorem prime_twelveJ_103 : Nat.Prime 103 := by norm_num
private theorem prime_twelveJ_5009 : Nat.Prime 5009 := by norm_num
private theorem prime_twelveJ_107 : Nat.Prime 107 := by norm_num
private theorem prime_twelveJ_61717 : Nat.Prime 61717 := by norm_num
private theorem prime_twelveJ_35279 : Nat.Prime 35279 := by norm_num
private theorem prime_twelveJ_7190123 : Nat.Prime 7190123 := by norm_num
private theorem prime_twelveJ_1521962095903 : Nat.Prime 1521962095903 := by
  apply lucas_primality 1521962095903 (3 : ZMod 1521962095903)
  · rw [← twelveJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (35279, 1), (7190123, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (35279, 1), (7190123, 1)] : List FactorBlock).map factorBlockValue).prod = 1521962095903 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twelveJ_2
      · exact prime_twelveJ_3
      · exact prime_twelveJ_35279
      · exact prime_twelveJ_7190123
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1521962095903) ^ 760981047951 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (3 : ZMod 1521962095903) ^ 507320698634 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (3 : ZMod 1521962095903) ^ 43140738 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (3 : ZMod 1521962095903) ^ 211674 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide

private theorem prime_twelveJ_563585608037072707 : Nat.Prime 563585608037072707 := by
  apply lucas_primality 563585608037072707 (3 : ZMod 563585608037072707)
  · rw [← twelveJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (61717, 1), (1521962095903, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (61717, 1), (1521962095903, 1)] : List FactorBlock).map factorBlockValue).prod = 563585608037072707 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twelveJ_2
      · exact prime_twelveJ_3
      · exact prime_twelveJ_61717
      · exact prime_twelveJ_1521962095903
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 563585608037072707) ^ 281792804018536353 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (3 : ZMod 563585608037072707) ^ 187861869345690902 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (3 : ZMod 563585608037072707) ^ 9131772575418 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (3 : ZMod 563585608037072707) ^ 370302 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide

private theorem prime_twelveJ_2291539082278737626663 : Nat.Prime 2291539082278737626663 := by
  apply lucas_primality 2291539082278737626663 (10 : ZMod 2291539082278737626663)
  · rw [← twelveJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (19, 1), (107, 1), (563585608037072707, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (19, 1), (107, 1), (563585608037072707, 1)] : List FactorBlock).map factorBlockValue).prod = 2291539082278737626663 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twelveJ_2
      · exact prime_twelveJ_19
      · exact prime_twelveJ_107
      · exact prime_twelveJ_563585608037072707
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (10 : ZMod 2291539082278737626663) ^ 1145769541139368813331 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (10 : ZMod 2291539082278737626663) ^ 120607320119933559298 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (10 : ZMod 2291539082278737626663) ^ 21416253105408762866 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (10 : ZMod 2291539082278737626663) ^ 4066 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide

private theorem prime_twelveJ_431 : Nat.Prime 431 := by norm_num
private theorem prime_twelveJ_11719 : Nat.Prime 11719 := by norm_num
private theorem prime_twelveJ_1228273 : Nat.Prime 1228273 := by norm_num
private theorem prime_twelveJ_9574219 : Nat.Prime 9574219 := by norm_num
private theorem prime_twelveJ_18373307 : Nat.Prime 18373307 := by norm_num
private theorem prime_twelveJ_331 : Nat.Prime 331 := by norm_num
private theorem prime_twelveJ_7129 : Nat.Prime 7129 := by norm_num
private theorem prime_twelveJ_199 : Nat.Prime 199 := by norm_num
private theorem prime_twelveJ_5449 : Nat.Prime 5449 := by norm_num
private theorem prime_twelveJ_8089 : Nat.Prime 8089 := by norm_num
private theorem prime_twelveJ_4121269 : Nat.Prime 4121269 := by norm_num
private theorem prime_twelveJ_123638071 : Nat.Prime 123638071 := by
  apply lucas_primality 123638071 (7 : ZMod 123638071)
  · rw [← twelveJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (5, 1), (4121269, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (5, 1), (4121269, 1)] : List FactorBlock).map factorBlockValue).prod = 123638071 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twelveJ_2
      · exact prime_twelveJ_3
      · exact prime_twelveJ_5
      · exact prime_twelveJ_4121269
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 123638071) ^ 61819035 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (7 : ZMod 123638071) ^ 41212690 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (7 : ZMod 123638071) ^ 24727614 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (7 : ZMod 123638071) ^ 30 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide

private theorem prime_twelveJ_741828427 : Nat.Prime 741828427 := by
  apply lucas_primality 741828427 (2 : ZMod 741828427)
  · rw [← twelveJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (123638071, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (123638071, 1)] : List FactorBlock).map factorBlockValue).prod = 741828427 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twelveJ_2
      · exact prime_twelveJ_3
      · exact prime_twelveJ_123638071
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 741828427) ^ 370914213 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (2 : ZMod 741828427) ^ 247276142 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (2 : ZMod 741828427) ^ 6 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide

private theorem prime_twelveJ_429449525106920937499 : Nat.Prime 429449525106920937499 := by
  apply lucas_primality 429449525106920937499 (2 : ZMod 429449525106920937499)
  · rw [← twelveJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (11, 1), (199, 1), (5449, 1), (8089, 1), (741828427, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (11, 1), (199, 1), (5449, 1), (8089, 1), (741828427, 1)] : List FactorBlock).map factorBlockValue).prod = 429449525106920937499 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_twelveJ_2
      · exact prime_twelveJ_3
      · exact prime_twelveJ_11
      · exact prime_twelveJ_199
      · exact prime_twelveJ_5449
      · exact prime_twelveJ_8089
      · exact prime_twelveJ_741828427
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 429449525106920937499) ^ 214724762553460468749 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (2 : ZMod 429449525106920937499) ^ 143149841702306979166 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (2 : ZMod 429449525106920937499) ^ 39040865918810994318 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (2 : ZMod 429449525106920937499) ^ 2158037814607642902 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (2 : ZMod 429449525106920937499) ^ 78812539017603402 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (2 : ZMod 429449525106920937499) ^ 53090558178627882 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (2 : ZMod 429449525106920937499) ^ 578906805774 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide

private theorem prime_twelveJ_1013 : Nat.Prime 1013 := by norm_num
private theorem prime_twelveJ_7220867 : Nat.Prime 7220867 := by norm_num
private theorem prime_twelveJ_144417341 : Nat.Prime 144417341 := by
  apply lucas_primality 144417341 (2 : ZMod 144417341)
  · rw [← twelveJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (5, 1), (7220867, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (5, 1), (7220867, 1)] : List FactorBlock).map factorBlockValue).prod = 144417341 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twelveJ_2
      · exact prime_twelveJ_5
      · exact prime_twelveJ_7220867
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 144417341) ^ 72208670 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (2 : ZMod 144417341) ^ 28883468 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (2 : ZMod 144417341) ^ 20 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide

private theorem prime_twelveJ_89 : Nat.Prime 89 := by norm_num
private theorem prime_twelveJ_67 : Nat.Prime 67 := by norm_num
private theorem prime_twelveJ_277100209 : Nat.Prime 277100209 := by
  apply lucas_primality 277100209 (17 : ZMod 277100209)
  · rw [← twelveJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 4), (3, 2), (7, 1), (11, 1), (67, 1), (373, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 4), (3, 2), (7, 1), (11, 1), (67, 1), (373, 1)] : List FactorBlock).map factorBlockValue).prod = 277100209 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_twelveJ_2
      · exact prime_twelveJ_3
      · exact prime_twelveJ_7
      · exact prime_twelveJ_11
      · exact prime_twelveJ_67
      · exact prime_twelveJ_373
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (17 : ZMod 277100209) ^ 138550104 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (17 : ZMod 277100209) ^ 92366736 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (17 : ZMod 277100209) ^ 39585744 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (17 : ZMod 277100209) ^ 25190928 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (17 : ZMod 277100209) ^ 4135824 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (17 : ZMod 277100209) ^ 742896 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide

private theorem prime_twelveJ_60421700572451 : Nat.Prime 60421700572451 := by
  apply lucas_primality 60421700572451 (2 : ZMod 60421700572451)
  · rw [← twelveJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 2), (7, 2), (89, 1), (277100209, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 2), (7, 2), (89, 1), (277100209, 1)] : List FactorBlock).map factorBlockValue).prod = 60421700572451 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twelveJ_2
      · exact prime_twelveJ_5
      · exact prime_twelveJ_7
      · exact prime_twelveJ_89
      · exact prime_twelveJ_277100209
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 60421700572451) ^ 30210850286225 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (2 : ZMod 60421700572451) ^ 12084340114490 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (2 : ZMod 60421700572451) ^ 8631671510350 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (2 : ZMod 60421700572451) ^ 678895512050 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (2 : ZMod 60421700572451) ^ 218050 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide

private theorem prime_twelveJ_769 : Nat.Prime 769 := by norm_num
private theorem prime_twelveJ_2143 : Nat.Prime 2143 := by norm_num
private theorem prime_twelveJ_8597 : Nat.Prime 8597 := by norm_num
private theorem prime_twelveJ_9792301 : Nat.Prime 9792301 := by norm_num
private theorem prime_twelveJ_223 : Nat.Prime 223 := by norm_num
private theorem prime_twelveJ_161017 : Nat.Prime 161017 := by norm_num
private theorem prime_twelveJ_6391408799 : Nat.Prime 6391408799 := by
  apply lucas_primality 6391408799 (23 : ZMod 6391408799)
  · rw [← twelveJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (89, 1), (223, 1), (161017, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (89, 1), (223, 1), (161017, 1)] : List FactorBlock).map factorBlockValue).prod = 6391408799 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twelveJ_2
      · exact prime_twelveJ_89
      · exact prime_twelveJ_223
      · exact prime_twelveJ_161017
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (23 : ZMod 6391408799) ^ 3195704399 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (23 : ZMod 6391408799) ^ 71813582 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (23 : ZMod 6391408799) ^ 28661026 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (23 : ZMod 6391408799) ^ 39694 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide

private theorem prime_twelveJ_607 : Nat.Prime 607 := by norm_num
private theorem prime_twelveJ_8526929 : Nat.Prime 8526929 := by norm_num
private theorem prime_twelveJ_324023303 : Nat.Prime 324023303 := by
  apply lucas_primality 324023303 (5 : ZMod 324023303)
  · rw [← twelveJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (19, 1), (8526929, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (19, 1), (8526929, 1)] : List FactorBlock).map factorBlockValue).prod = 324023303 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twelveJ_2
      · exact prime_twelveJ_19
      · exact prime_twelveJ_8526929
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 324023303) ^ 162011651 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (5 : ZMod 324023303) ^ 17053858 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (5 : ZMod 324023303) ^ 38 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide

private theorem prime_twelveJ_4817 : Nat.Prime 4817 := by norm_num
private theorem prime_twelveJ_557 : Nat.Prime 557 := by norm_num
private theorem prime_twelveJ_1109 : Nat.Prime 1109 := by norm_num
private theorem prime_twelveJ_710369951 : Nat.Prime 710369951 := by
  apply lucas_primality 710369951 (7 : ZMod 710369951)
  · rw [← twelveJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 2), (23, 1), (557, 1), (1109, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 2), (23, 1), (557, 1), (1109, 1)] : List FactorBlock).map factorBlockValue).prod = 710369951 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twelveJ_2
      · exact prime_twelveJ_5
      · exact prime_twelveJ_23
      · exact prime_twelveJ_557
      · exact prime_twelveJ_1109
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 710369951) ^ 355184975 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (7 : ZMod 710369951) ^ 142073990 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (7 : ZMod 710369951) ^ 30885650 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (7 : ZMod 710369951) ^ 1275350 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (7 : ZMod 710369951) ^ 640550 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide

private theorem prime_twelveJ_4243096546919081 : Nat.Prime 4243096546919081 := by
  apply lucas_primality 4243096546919081 (3 : ZMod 4243096546919081)
  · rw [← twelveJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (5, 1), (31, 1), (4817, 1), (710369951, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (5, 1), (31, 1), (4817, 1), (710369951, 1)] : List FactorBlock).map factorBlockValue).prod = 4243096546919081 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twelveJ_2
      · exact prime_twelveJ_5
      · exact prime_twelveJ_31
      · exact prime_twelveJ_4817
      · exact prime_twelveJ_710369951
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 4243096546919081) ^ 2121548273459540 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (3 : ZMod 4243096546919081) ^ 848619309383816 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (3 : ZMod 4243096546919081) ^ 136874082158680 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (3 : ZMod 4243096546919081) ^ 880858739240 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (3 : ZMod 4243096546919081) ^ 5973080 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide

private theorem prime_twelveJ_421 : Nat.Prime 421 := by norm_num
private theorem prime_twelveJ_2072201 : Nat.Prime 2072201 := by norm_num
private theorem prime_twelveJ_2567179 : Nat.Prime 2567179 := by norm_num
private theorem prime_twelveJ_191 : Nat.Prime 191 := by norm_num
private theorem prime_twelveJ_383 : Nat.Prime 383 := by norm_num
private theorem prime_twelveJ_811 : Nat.Prime 811 := by norm_num
private theorem prime_twelveJ_237308333 : Nat.Prime 237308333 := by
  apply lucas_primality 237308333 (2 : ZMod 237308333)
  · rw [← twelveJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (191, 1), (383, 1), (811, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (191, 1), (383, 1), (811, 1)] : List FactorBlock).map factorBlockValue).prod = 237308333 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twelveJ_2
      · exact prime_twelveJ_191
      · exact prime_twelveJ_383
      · exact prime_twelveJ_811
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 237308333) ^ 118654166 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (2 : ZMod 237308333) ^ 1242452 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (2 : ZMod 237308333) ^ 619604 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (2 : ZMod 237308333) ^ 292612 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide

private theorem prime_twelveJ_101 : Nat.Prime 101 := by norm_num
private theorem prime_twelveJ_119737 : Nat.Prime 119737 := by norm_num
private theorem prime_twelveJ_211 : Nat.Prime 211 := by norm_num
private theorem prime_twelveJ_8573 : Nat.Prime 8573 := by norm_num
private theorem prime_twelveJ_21706837 : Nat.Prime 21706837 := by
  apply lucas_primality 21706837 (2 : ZMod 21706837)
  · rw [← twelveJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (211, 1), (8573, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (211, 1), (8573, 1)] : List FactorBlock).map factorBlockValue).prod = 21706837 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twelveJ_2
      · exact prime_twelveJ_3
      · exact prime_twelveJ_211
      · exact prime_twelveJ_8573
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 21706837) ^ 10853418 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (2 : ZMod 21706837) ^ 7235612 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (2 : ZMod 21706837) ^ 102876 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (2 : ZMod 21706837) ^ 2532 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide

private theorem prime_twelveJ_14467279 : Nat.Prime 14467279 := by norm_num
private theorem prime_twelveJ_752298509 : Nat.Prime 752298509 := by
  apply lucas_primality 752298509 (2 : ZMod 752298509)
  · rw [← twelveJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (13, 1), (14467279, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (13, 1), (14467279, 1)] : List FactorBlock).map factorBlockValue).prod = 752298509 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twelveJ_2
      · exact prime_twelveJ_13
      · exact prime_twelveJ_14467279
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 752298509) ^ 376149254 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (2 : ZMod 752298509) ^ 57869116 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (2 : ZMod 752298509) ^ 52 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide

private theorem prime_twelveJ_281 : Nat.Prime 281 := by norm_num
private theorem prime_twelveJ_739 : Nat.Prime 739 := by norm_num
private theorem prime_twelveJ_8443 : Nat.Prime 8443 := by norm_num
private theorem prime_twelveJ_84294913 : Nat.Prime 84294913 := by
  apply lucas_primality 84294913 (14 : ZMod 84294913)
  · rw [← twelveJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 8), (3, 1), (13, 1), (8443, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 8), (3, 1), (13, 1), (8443, 1)] : List FactorBlock).map factorBlockValue).prod = 84294913 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twelveJ_2
      · exact prime_twelveJ_3
      · exact prime_twelveJ_13
      · exact prime_twelveJ_8443
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (14 : ZMod 84294913) ^ 42147456 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (14 : ZMod 84294913) ^ 28098304 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (14 : ZMod 84294913) ^ 6484224 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (14 : ZMod 84294913) ^ 9984 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide

private theorem prime_twelveJ_3540386347 : Nat.Prime 3540386347 := by
  apply lucas_primality 3540386347 (11 : ZMod 3540386347)
  · rw [← twelveJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (7, 1), (84294913, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (7, 1), (84294913, 1)] : List FactorBlock).map factorBlockValue).prod = 3540386347 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twelveJ_2
      · exact prime_twelveJ_3
      · exact prime_twelveJ_7
      · exact prime_twelveJ_84294913
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 3540386347) ^ 1770193173 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (11 : ZMod 3540386347) ^ 1180128782 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (11 : ZMod 3540386347) ^ 505769478 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (11 : ZMod 3540386347) ^ 42 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide

private theorem prime_twelveJ_1509031 : Nat.Prime 1509031 := by norm_num
private theorem prime_twelveJ_9277522589 : Nat.Prime 9277522589 := by
  apply lucas_primality 9277522589 (2 : ZMod 9277522589)
  · rw [← twelveJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (29, 1), (53, 1), (1509031, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (29, 1), (53, 1), (1509031, 1)] : List FactorBlock).map factorBlockValue).prod = 9277522589 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twelveJ_2
      · exact prime_twelveJ_29
      · exact prime_twelveJ_53
      · exact prime_twelveJ_1509031
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 9277522589) ^ 4638761294 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (2 : ZMod 9277522589) ^ 319914572 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (2 : ZMod 9277522589) ^ 175047596 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (2 : ZMod 9277522589) ^ 6148 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide

private theorem prime_twelveJ_964862349257 : Nat.Prime 964862349257 := by
  apply lucas_primality 964862349257 (5 : ZMod 964862349257)
  · rw [← twelveJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (13, 1), (9277522589, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (13, 1), (9277522589, 1)] : List FactorBlock).map factorBlockValue).prod = 964862349257 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twelveJ_2
      · exact prime_twelveJ_13
      · exact prime_twelveJ_9277522589
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 964862349257) ^ 482431174628 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (5 : ZMod 964862349257) ^ 74220180712 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (5 : ZMod 964862349257) ^ 104 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide

private theorem prime_twelveJ_1087 : Nat.Prime 1087 := by norm_num
private theorem prime_twelveJ_3061 : Nat.Prime 3061 := by norm_num
private theorem prime_twelveJ_61379 : Nat.Prime 61379 := by norm_num
private theorem prime_twelveJ_382747 : Nat.Prime 382747 := by norm_num
private theorem prime_twelveJ_163987 : Nat.Prime 163987 := by norm_num
private theorem prime_twelveJ_1440461809 : Nat.Prime 1440461809 := by
  apply lucas_primality 1440461809 (7 : ZMod 1440461809)
  · rw [← twelveJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 4), (3, 2), (61, 1), (163987, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 4), (3, 2), (61, 1), (163987, 1)] : List FactorBlock).map factorBlockValue).prod = 1440461809 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twelveJ_2
      · exact prime_twelveJ_3
      · exact prime_twelveJ_61
      · exact prime_twelveJ_163987
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 1440461809) ^ 720230904 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (7 : ZMod 1440461809) ^ 480153936 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (7 : ZMod 1440461809) ^ 23614128 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (7 : ZMod 1440461809) ^ 8784 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide

private theorem prime_twelveJ_621509730110564998034623 : Nat.Prime 621509730110564998034623 := by
  apply lucas_primality 621509730110564998034623 (5 : ZMod 621509730110564998034623)
  · rw [← twelveJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (3061, 1), (61379, 1), (382747, 1), (1440461809, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (3061, 1), (61379, 1), (382747, 1), (1440461809, 1)] : List FactorBlock).map factorBlockValue).prod = 621509730110564998034623 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_twelveJ_2
      · exact prime_twelveJ_3
      · exact prime_twelveJ_3061
      · exact prime_twelveJ_61379
      · exact prime_twelveJ_382747
      · exact prime_twelveJ_1440461809
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 621509730110564998034623) ^ 310754865055282499017311 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (5 : ZMod 621509730110564998034623) ^ 207169910036854999344874 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (5 : ZMod 621509730110564998034623) ^ 203041401538897418502 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (5 : ZMod 621509730110564998034623) ^ 10125771519747226218 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (5 : ZMod 621509730110564998034623) ^ 1623813459310105626 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (5 : ZMod 621509730110564998034623) ^ 431465607923358 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide

private theorem prime_twelveJ_97327 : Nat.Prime 97327 := by norm_num
private theorem prime_twelveJ_208223 : Nat.Prime 208223 := by norm_num
private theorem prime_twelveJ_4129087 : Nat.Prime 4129087 := by norm_num
private theorem prime_twelveJ_1997 : Nat.Prime 1997 := by norm_num
private theorem prime_twelveJ_1929523 : Nat.Prime 1929523 := by norm_num
private theorem prime_twelveJ_7706514863 : Nat.Prime 7706514863 := by
  apply lucas_primality 7706514863 (5 : ZMod 7706514863)
  · rw [← twelveJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (1997, 1), (1929523, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (1997, 1), (1929523, 1)] : List FactorBlock).map factorBlockValue).prod = 7706514863 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twelveJ_2
      · exact prime_twelveJ_1997
      · exact prime_twelveJ_1929523
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 7706514863) ^ 3853257431 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (5 : ZMod 7706514863) ^ 3859046 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (5 : ZMod 7706514863) ^ 3994 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide

private theorem prime_twelveJ_449 : Nat.Prime 449 := by norm_num
private theorem prime_twelveJ_128239 : Nat.Prime 128239 := by norm_num
private theorem prime_twelveJ_4613533 : Nat.Prime 4613533 := by norm_num
private theorem prime_twelveJ_73816529 : Nat.Prime 73816529 := by
  apply lucas_primality 73816529 (3 : ZMod 73816529)
  · rw [← twelveJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 4), (4613533, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 4), (4613533, 1)] : List FactorBlock).map factorBlockValue).prod = 73816529 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_twelveJ_2
      · exact prime_twelveJ_4613533
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 73816529) ^ 36908264 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (3 : ZMod 73816529) ^ 16 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide

private theorem prime_twelveJ_3209 : Nat.Prime 3209 := by norm_num
private theorem prime_twelveJ_40597 : Nat.Prime 40597 := by norm_num
private theorem prime_twelveJ_260551547 : Nat.Prime 260551547 := by
  apply lucas_primality 260551547 (2 : ZMod 260551547)
  · rw [← twelveJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3209, 1), (40597, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3209, 1), (40597, 1)] : List FactorBlock).map factorBlockValue).prod = 260551547 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twelveJ_2
      · exact prime_twelveJ_3209
      · exact prime_twelveJ_40597
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 260551547) ^ 130275773 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (2 : ZMod 260551547) ^ 81194 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (2 : ZMod 260551547) ^ 6418 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide

private theorem prime_twelveJ_113 : Nat.Prime 113 := by norm_num
private theorem prime_twelveJ_37309 : Nat.Prime 37309 := by norm_num
private theorem prime_twelveJ_1222615931 : Nat.Prime 1222615931 := by
  apply lucas_primality 1222615931 (2 : ZMod 1222615931)
  · rw [← twelveJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 1), (29, 1), (113, 1), (37309, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 1), (29, 1), (113, 1), (37309, 1)] : List FactorBlock).map factorBlockValue).prod = 1222615931 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twelveJ_2
      · exact prime_twelveJ_5
      · exact prime_twelveJ_29
      · exact prime_twelveJ_113
      · exact prime_twelveJ_37309
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1222615931) ^ 611307965 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (2 : ZMod 1222615931) ^ 244523186 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (2 : ZMod 1222615931) ^ 42159170 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (2 : ZMod 1222615931) ^ 10819610 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (2 : ZMod 1222615931) ^ 32770 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide

private theorem prime_twelveJ_397 : Nat.Prime 397 := by norm_num
private theorem prime_twelveJ_2531 : Nat.Prime 2531 := by norm_num
private theorem prime_twelveJ_6763 : Nat.Prime 6763 := by norm_num
private theorem prime_twelveJ_462094662389 : Nat.Prime 462094662389 := by
  apply lucas_primality 462094662389 (2 : ZMod 462094662389)
  · rw [← twelveJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (17, 1), (397, 1), (2531, 1), (6763, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (17, 1), (397, 1), (2531, 1), (6763, 1)] : List FactorBlock).map factorBlockValue).prod = 462094662389 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twelveJ_2
      · exact prime_twelveJ_17
      · exact prime_twelveJ_397
      · exact prime_twelveJ_2531
      · exact prime_twelveJ_6763
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 462094662389) ^ 231047331194 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (2 : ZMod 462094662389) ^ 27182038964 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (2 : ZMod 462094662389) ^ 1163966404 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (2 : ZMod 462094662389) ^ 182573948 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (2 : ZMod 462094662389) ^ 68326876 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide

private theorem prime_twelveJ_1667237541899513 : Nat.Prime 1667237541899513 := by
  apply lucas_primality 1667237541899513 (3 : ZMod 1667237541899513)
  · rw [← twelveJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (11, 1), (41, 1), (462094662389, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (11, 1), (41, 1), (462094662389, 1)] : List FactorBlock).map factorBlockValue).prod = 1667237541899513 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twelveJ_2
      · exact prime_twelveJ_11
      · exact prime_twelveJ_41
      · exact prime_twelveJ_462094662389
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1667237541899513) ^ 833618770949756 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (3 : ZMod 1667237541899513) ^ 151567049263592 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (3 : ZMod 1667237541899513) ^ 40664330290232 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (3 : ZMod 1667237541899513) ^ 3608 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide

private theorem prime_twelveJ_483498887150858771 : Nat.Prime 483498887150858771 := by
  apply lucas_primality 483498887150858771 (2 : ZMod 483498887150858771)
  · rw [← twelveJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 1), (29, 1), (1667237541899513, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 1), (29, 1), (1667237541899513, 1)] : List FactorBlock).map factorBlockValue).prod = 483498887150858771 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twelveJ_2
      · exact prime_twelveJ_5
      · exact prime_twelveJ_29
      · exact prime_twelveJ_1667237541899513
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 483498887150858771) ^ 241749443575429385 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (2 : ZMod 483498887150858771) ^ 96699777430171754 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (2 : ZMod 483498887150858771) ^ 16672375418995130 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (2 : ZMod 483498887150858771) ^ 290 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide

private theorem prime_twelveJ_65129 : Nat.Prime 65129 := by norm_num
private theorem prime_twelveJ_182467 : Nat.Prime 182467 := by norm_num
private theorem prime_twelveJ_2207 : Nat.Prime 2207 := by norm_num
private theorem prime_twelveJ_5400053 : Nat.Prime 5400053 := by norm_num
private theorem prime_twelveJ_170545391855011 : Nat.Prime 170545391855011 := by
  apply lucas_primality 170545391855011 (2 : ZMod 170545391855011)
  · rw [← twelveJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 3), (5, 1), (53, 1), (2207, 1), (5400053, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 3), (5, 1), (53, 1), (2207, 1), (5400053, 1)] : List FactorBlock).map factorBlockValue).prod = 170545391855011 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_twelveJ_2
      · exact prime_twelveJ_3
      · exact prime_twelveJ_5
      · exact prime_twelveJ_53
      · exact prime_twelveJ_2207
      · exact prime_twelveJ_5400053
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 170545391855011) ^ 85272695927505 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (2 : ZMod 170545391855011) ^ 56848463951670 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (2 : ZMod 170545391855011) ^ 34109078371002 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (2 : ZMod 170545391855011) ^ 3217837582170 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (2 : ZMod 170545391855011) ^ 77274758430 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (2 : ZMod 170545391855011) ^ 31582170 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide

private theorem prime_twelveJ_8713293684370321798361 : Nat.Prime 8713293684370321798361 := by
  apply lucas_primality 8713293684370321798361 (3 : ZMod 8713293684370321798361)
  · rw [← twelveJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (5, 1), (7, 1), (182467, 1), (170545391855011, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (5, 1), (7, 1), (182467, 1), (170545391855011, 1)] : List FactorBlock).map factorBlockValue).prod = 8713293684370321798361 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twelveJ_2
      · exact prime_twelveJ_5
      · exact prime_twelveJ_7
      · exact prime_twelveJ_182467
      · exact prime_twelveJ_170545391855011
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 8713293684370321798361) ^ 4356646842185160899180 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (3 : ZMod 8713293684370321798361) ^ 1742658736874064359672 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (3 : ZMod 8713293684370321798361) ^ 1244756240624331685480 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (3 : ZMod 8713293684370321798361) ^ 47752709719403080 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (3 : ZMod 8713293684370321798361) ^ 51090760 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide

private theorem prime_twelveJ_545661638816687200389859201 : Nat.Prime 545661638816687200389859201 := by
  apply lucas_primality 545661638816687200389859201 (13 : ZMod 545661638816687200389859201)
  · rw [← twelveJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 7), (3, 4), (5, 2), (7, 2), (11, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 7), (3, 4), (5, 2), (7, 2), (11, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod = 545661638816687200389859201 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_twelveJ_2
      · exact prime_twelveJ_3
      · exact prime_twelveJ_5
      · exact prime_twelveJ_7
      · exact prime_twelveJ_11
      · exact prime_twelveJ_17
      · exact prime_twelveJ_19
      · exact prime_twelveJ_23
      · exact prime_twelveJ_29
      · exact prime_twelveJ_31
      · exact prime_twelveJ_37
      · exact prime_twelveJ_41
      · exact prime_twelveJ_43
      · exact prime_twelveJ_47
      · exact prime_twelveJ_53
      · exact prime_twelveJ_59
      · exact prime_twelveJ_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 545661638816687200389859201) ^ 272830819408343600194929600 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (13 : ZMod 545661638816687200389859201) ^ 181887212938895733463286400 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (13 : ZMod 545661638816687200389859201) ^ 109132327763337440077971840 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (13 : ZMod 545661638816687200389859201) ^ 77951662688098171484265600 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (13 : ZMod 545661638816687200389859201) ^ 49605603528789745489987200 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (13 : ZMod 545661638816687200389859201) ^ 32097743459805129434697600 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (13 : ZMod 545661638816687200389859201) ^ 28719033621930905283676800 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (13 : ZMod 545661638816687200389859201) ^ 23724419078986400016950400 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (13 : ZMod 545661638816687200389859201) ^ 18815918579885765530684800 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (13 : ZMod 545661638816687200389859201) ^ 17601988348925393560963200 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (13 : ZMod 545661638816687200389859201) ^ 14747611859910464875401600 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (13 : ZMod 545661638816687200389859201) ^ 13308820458943590253411200 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (13 : ZMod 545661638816687200389859201) ^ 12689805553876446520694400 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (13 : ZMod 545661638816687200389859201) ^ 11609822102482706391273600 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (13 : ZMod 545661638816687200389859201) ^ 10295502619182777365846400 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (13 : ZMod 545661638816687200389859201) ^ 9248502352825206786268800 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (13 : ZMod 545661638816687200389859201) ^ 8945272767486675416227200 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide

private theorem prime_twelveJ_525451948490143230005049601 : Nat.Prime 525451948490143230005049601 := by
  apply lucas_primality 525451948490143230005049601 (179 : ZMod 525451948490143230005049601)
  · rw [← twelveJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 8), (3, 1), (5, 2), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 8), (3, 1), (5, 2), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod = 525451948490143230005049601 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_twelveJ_2
      · exact prime_twelveJ_3
      · exact prime_twelveJ_5
      · exact prime_twelveJ_7
      · exact prime_twelveJ_11
      · exact prime_twelveJ_13
      · exact prime_twelveJ_17
      · exact prime_twelveJ_19
      · exact prime_twelveJ_23
      · exact prime_twelveJ_29
      · exact prime_twelveJ_31
      · exact prime_twelveJ_37
      · exact prime_twelveJ_41
      · exact prime_twelveJ_43
      · exact prime_twelveJ_47
      · exact prime_twelveJ_53
      · exact prime_twelveJ_59
      · exact prime_twelveJ_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (179 : ZMod 525451948490143230005049601) ^ 262725974245071615002524800 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (179 : ZMod 525451948490143230005049601) ^ 175150649496714410001683200 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (179 : ZMod 525451948490143230005049601) ^ 105090389698028646001009920 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (179 : ZMod 525451948490143230005049601) ^ 75064564070020461429292800 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (179 : ZMod 525451948490143230005049601) ^ 47768358953649384545913600 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (179 : ZMod 525451948490143230005049601) ^ 40419380653087940769619200 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (179 : ZMod 525451948490143230005049601) ^ 30908938146479013529708800 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (179 : ZMod 525451948490143230005049601) ^ 27655365710007538421318400 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (179 : ZMod 525451948490143230005049601) ^ 22845736890875792608915200 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (179 : ZMod 525451948490143230005049601) ^ 18119032706556663103622400 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (179 : ZMod 525451948490143230005049601) ^ 16950062854520749355001600 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (179 : ZMod 525451948490143230005049601) ^ 14201404013247114324460800 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (179 : ZMod 525451948490143230005049601) ^ 12815901182686420244025600 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (179 : ZMod 525451948490143230005049601) ^ 12219812755584726279187200 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (179 : ZMod 525451948490143230005049601) ^ 11179828691279643191596800 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (179 : ZMod 525451948490143230005049601) ^ 9914187707361193018963200 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (179 : ZMod 525451948490143230005049601) ^ 8905965228646495423814400 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (179 : ZMod 525451948490143230005049601) ^ 8613966368690872623033600 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide

private theorem prime_twelveJ_727 : Nat.Prime 727 := by norm_num
private theorem prime_twelveJ_517267 : Nat.Prime 517267 := by norm_num
private theorem prime_twelveJ_40346827 : Nat.Prime 40346827 := by
  apply lucas_primality 40346827 (2 : ZMod 40346827)
  · rw [← twelveJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (13, 1), (517267, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (13, 1), (517267, 1)] : List FactorBlock).map factorBlockValue).prod = 40346827 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twelveJ_2
      · exact prime_twelveJ_3
      · exact prime_twelveJ_13
      · exact prime_twelveJ_517267
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 40346827) ^ 20173413 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (2 : ZMod 40346827) ^ 13448942 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (2 : ZMod 40346827) ^ 3103602 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (2 : ZMod 40346827) ^ 78 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide

private theorem prime_twelveJ_4159 : Nat.Prime 4159 := by norm_num
private theorem prime_twelveJ_16453 : Nat.Prime 16453 := by norm_num
private theorem prime_twelveJ_910838081 : Nat.Prime 910838081 := by
  apply lucas_primality 910838081 (3 : ZMod 910838081)
  · rw [← twelveJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 6), (5, 1), (173, 1), (16453, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 6), (5, 1), (173, 1), (16453, 1)] : List FactorBlock).map factorBlockValue).prod = 910838081 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twelveJ_2
      · exact prime_twelveJ_5
      · exact prime_twelveJ_173
      · exact prime_twelveJ_16453
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 910838081) ^ 455419040 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (3 : ZMod 910838081) ^ 182167616 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (3 : ZMod 910838081) ^ 5264960 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (3 : ZMod 910838081) ^ 55360 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide

private theorem prime_twelveJ_75763511577581 : Nat.Prime 75763511577581 := by
  apply lucas_primality 75763511577581 (3 : ZMod 75763511577581)
  · rw [← twelveJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (5, 1), (4159, 1), (910838081, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (5, 1), (4159, 1), (910838081, 1)] : List FactorBlock).map factorBlockValue).prod = 75763511577581 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twelveJ_2
      · exact prime_twelveJ_5
      · exact prime_twelveJ_4159
      · exact prime_twelveJ_910838081
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 75763511577581) ^ 37881755788790 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (3 : ZMod 75763511577581) ^ 15152702315516 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (3 : ZMod 75763511577581) ^ 18216761620 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (3 : ZMod 75763511577581) ^ 83180 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide

private theorem prime_twelveJ_17274080639688469 : Nat.Prime 17274080639688469 := by
  apply lucas_primality 17274080639688469 (2 : ZMod 17274080639688469)
  · rw [← twelveJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (19, 1), (75763511577581, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (19, 1), (75763511577581, 1)] : List FactorBlock).map factorBlockValue).prod = 17274080639688469 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twelveJ_2
      · exact prime_twelveJ_3
      · exact prime_twelveJ_19
      · exact prime_twelveJ_75763511577581
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 17274080639688469) ^ 8637040319844234 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (2 : ZMod 17274080639688469) ^ 5758026879896156 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (2 : ZMod 17274080639688469) ^ 909162138930972 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (2 : ZMod 17274080639688469) ^ 228 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide

private theorem prime_twelveJ_16831 : Nat.Prime 16831 := by norm_num
private theorem prime_twelveJ_57427 : Nat.Prime 57427 := by norm_num
private theorem prime_twelveJ_389 : Nat.Prime 389 := by norm_num
private theorem prime_twelveJ_10976629 : Nat.Prime 10976629 := by norm_num
private theorem prime_twelveJ_205745933977 : Nat.Prime 205745933977 := by
  apply lucas_primality 205745933977 (5 : ZMod 205745933977)
  · rw [← twelveJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (3, 1), (11, 1), (71, 1), (10976629, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (3, 1), (11, 1), (71, 1), (10976629, 1)] : List FactorBlock).map factorBlockValue).prod = 205745933977 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twelveJ_2
      · exact prime_twelveJ_3
      · exact prime_twelveJ_11
      · exact prime_twelveJ_71
      · exact prime_twelveJ_10976629
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 205745933977) ^ 102872966988 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (5 : ZMod 205745933977) ^ 68581977992 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (5 : ZMod 205745933977) ^ 18704175816 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (5 : ZMod 205745933977) ^ 2897830056 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (5 : ZMod 205745933977) ^ 18744 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide

private theorem prime_twelveJ_506142404437043173 : Nat.Prime 506142404437043173 := by
  apply lucas_primality 506142404437043173 (5 : ZMod 506142404437043173)
  · rw [← twelveJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (17, 1), (31, 1), (389, 1), (205745933977, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (17, 1), (31, 1), (389, 1), (205745933977, 1)] : List FactorBlock).map factorBlockValue).prod = 506142404437043173 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_twelveJ_2
      · exact prime_twelveJ_3
      · exact prime_twelveJ_17
      · exact prime_twelveJ_31
      · exact prime_twelveJ_389
      · exact prime_twelveJ_205745933977
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 506142404437043173) ^ 253071202218521586 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (5 : ZMod 506142404437043173) ^ 168714134812347724 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (5 : ZMod 506142404437043173) ^ 29773082613943716 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (5 : ZMod 506142404437043173) ^ 16327174336678812 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (5 : ZMod 506142404437043173) ^ 1301137286470548 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (5 : ZMod 506142404437043173) ^ 2460036 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide

private theorem prime_twelveJ_239 : Nat.Prime 239 := by norm_num
private theorem prime_twelveJ_4327 : Nat.Prime 4327 := by norm_num
private theorem prime_twelveJ_1214459 : Nat.Prime 1214459 := by norm_num
private theorem prime_twelveJ_983 : Nat.Prime 983 := by norm_num
private theorem prime_twelveJ_6079 : Nat.Prime 6079 := by norm_num
private theorem prime_twelveJ_35853943 : Nat.Prime 35853943 := by
  apply lucas_primality 35853943 (3 : ZMod 35853943)
  · rw [← twelveJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (983, 1), (6079, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (983, 1), (6079, 1)] : List FactorBlock).map factorBlockValue).prod = 35853943 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twelveJ_2
      · exact prime_twelveJ_3
      · exact prime_twelveJ_983
      · exact prime_twelveJ_6079
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 35853943) ^ 17926971 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (3 : ZMod 35853943) ^ 11951314 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (3 : ZMod 35853943) ^ 36474 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (3 : ZMod 35853943) ^ 5898 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide

private theorem prime_twelveJ_376537177183483 : Nat.Prime 376537177183483 := by
  apply lucas_primality 376537177183483 (2 : ZMod 376537177183483)
  · rw [← twelveJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 7), (7, 4), (35853943, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 7), (7, 4), (35853943, 1)] : List FactorBlock).map factorBlockValue).prod = 376537177183483 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twelveJ_2
      · exact prime_twelveJ_3
      · exact prime_twelveJ_7
      · exact prime_twelveJ_35853943
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 376537177183483) ^ 188268588591741 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (2 : ZMod 376537177183483) ^ 125512392394494 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (2 : ZMod 376537177183483) ^ 53791025311926 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (2 : ZMod 376537177183483) ^ 10501974 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide

private theorem prime_twelveJ_97 : Nat.Prime 97 := by norm_num
private theorem prime_twelveJ_44983 : Nat.Prime 44983 := by norm_num
private theorem prime_twelveJ_62011 : Nat.Prime 62011 := by norm_num
private theorem prime_twelveJ_367 : Nat.Prime 367 := by norm_num
private theorem prime_twelveJ_15787 : Nat.Prime 15787 := by norm_num
private theorem prime_twelveJ_69525949 : Nat.Prime 69525949 := by
  apply lucas_primality 69525949 (2 : ZMod 69525949)
  · rw [← twelveJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (367, 1), (15787, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (367, 1), (15787, 1)] : List FactorBlock).map factorBlockValue).prod = 69525949 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twelveJ_2
      · exact prime_twelveJ_3
      · exact prime_twelveJ_367
      · exact prime_twelveJ_15787
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 69525949) ^ 34762974 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (2 : ZMod 69525949) ^ 23175316 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (2 : ZMod 69525949) ^ 189444 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (2 : ZMod 69525949) ^ 4404 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide

private theorem prime_twelveJ_6118283513 : Nat.Prime 6118283513 := by
  apply lucas_primality 6118283513 (3 : ZMod 6118283513)
  · rw [← twelveJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (11, 1), (69525949, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (11, 1), (69525949, 1)] : List FactorBlock).map factorBlockValue).prod = 6118283513 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twelveJ_2
      · exact prime_twelveJ_11
      · exact prime_twelveJ_69525949
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 6118283513) ^ 3059141756 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (3 : ZMod 6118283513) ^ 556207592 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (3 : ZMod 6118283513) ^ 88 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide

private theorem prime_twelveJ_104885372978717557351 : Nat.Prime 104885372978717557351 := by
  apply lucas_primality 104885372978717557351 (6 : ZMod 104885372978717557351)
  · rw [← twelveJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (5, 2), (19, 1), (97, 1), (62011, 1), (6118283513, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (5, 2), (19, 1), (97, 1), (62011, 1), (6118283513, 1)] : List FactorBlock).map factorBlockValue).prod = 104885372978717557351 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_twelveJ_2
      · exact prime_twelveJ_3
      · exact prime_twelveJ_5
      · exact prime_twelveJ_19
      · exact prime_twelveJ_97
      · exact prime_twelveJ_62011
      · exact prime_twelveJ_6118283513
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 104885372978717557351) ^ 52442686489358778675 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (6 : ZMod 104885372978717557351) ^ 34961790992905852450 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (6 : ZMod 104885372978717557351) ^ 20977074595743511470 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (6 : ZMod 104885372978717557351) ^ 5520282788353555650 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (6 : ZMod 104885372978717557351) ^ 1081292504935232550 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (6 : ZMod 104885372978717557351) ^ 1691399477168850 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (6 : ZMod 104885372978717557351) ^ 17142940950 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide

private theorem prime_twelveJ_55249 : Nat.Prime 55249 := by norm_num
private theorem prime_twelveJ_157429 : Nat.Prime 157429 := by norm_num
private theorem prime_twelveJ_773027 : Nat.Prime 773027 := by norm_num
private theorem prime_twelveJ_17678041 : Nat.Prime 17678041 := by norm_num
private theorem prime_twelveJ_176780411 : Nat.Prime 176780411 := by
  apply lucas_primality 176780411 (2 : ZMod 176780411)
  · rw [← twelveJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 1), (17678041, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 1), (17678041, 1)] : List FactorBlock).map factorBlockValue).prod = 176780411 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twelveJ_2
      · exact prime_twelveJ_5
      · exact prime_twelveJ_17678041
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 176780411) ^ 88390205 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (2 : ZMod 176780411) ^ 35356082 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (2 : ZMod 176780411) ^ 10 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide

private theorem prime_twelveJ_5573 : Nat.Prime 5573 := by norm_num
private theorem prime_twelveJ_12097 : Nat.Prime 12097 := by norm_num
private theorem prime_twelveJ_133260553 : Nat.Prime 133260553 := by
  apply lucas_primality 133260553 (7 : ZMod 133260553)
  · rw [← twelveJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (3, 4), (17, 1), (12097, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (3, 4), (17, 1), (12097, 1)] : List FactorBlock).map factorBlockValue).prod = 133260553 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twelveJ_2
      · exact prime_twelveJ_3
      · exact prime_twelveJ_17
      · exact prime_twelveJ_12097
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 133260553) ^ 66630276 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (7 : ZMod 133260553) ^ 44420184 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (7 : ZMod 133260553) ^ 7838856 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (7 : ZMod 133260553) ^ 11016 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide

private theorem prime_twelveJ_3198253273 : Nat.Prime 3198253273 := by
  apply lucas_primality 3198253273 (7 : ZMod 3198253273)
  · rw [← twelveJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (3, 1), (133260553, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (3, 1), (133260553, 1)] : List FactorBlock).map factorBlockValue).prod = 3198253273 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twelveJ_2
      · exact prime_twelveJ_3
      · exact prime_twelveJ_133260553
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 3198253273) ^ 1599126636 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (7 : ZMod 3198253273) ^ 1066084424 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (7 : ZMod 3198253273) ^ 24 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide

private theorem prime_twelveJ_9739 : Nat.Prime 9739 := by norm_num
private theorem prime_twelveJ_60427 : Nat.Prime 60427 := by norm_num
private theorem prime_twelveJ_2192745608479 : Nat.Prime 2192745608479 := by
  apply lucas_primality 2192745608479 (6 : ZMod 2192745608479)
  · rw [← twelveJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 4), (23, 1), (9739, 1), (60427, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 4), (23, 1), (9739, 1), (60427, 1)] : List FactorBlock).map factorBlockValue).prod = 2192745608479 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twelveJ_2
      · exact prime_twelveJ_3
      · exact prime_twelveJ_23
      · exact prime_twelveJ_9739
      · exact prime_twelveJ_60427
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 2192745608479) ^ 1096372804239 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (6 : ZMod 2192745608479) ^ 730915202826 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (6 : ZMod 2192745608479) ^ 95336765586 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (6 : ZMod 2192745608479) ^ 225151002 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (6 : ZMod 2192745608479) ^ 36287514 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide

private theorem prime_twelveJ_1567 : Nat.Prime 1567 := by norm_num
private theorem prime_twelveJ_4969 : Nat.Prime 4969 := by norm_num
private theorem prime_twelveJ_10103311 : Nat.Prime 10103311 := by norm_num
private theorem prime_twelveJ_32429 : Nat.Prime 32429 := by norm_num
private theorem prime_twelveJ_38287 : Nat.Prime 38287 := by norm_num
private theorem prime_twelveJ_7449654739 : Nat.Prime 7449654739 := by
  apply lucas_primality 7449654739 (2 : ZMod 7449654739)
  · rw [← twelveJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (32429, 1), (38287, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (32429, 1), (38287, 1)] : List FactorBlock).map factorBlockValue).prod = 7449654739 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twelveJ_2
      · exact prime_twelveJ_3
      · exact prime_twelveJ_32429
      · exact prime_twelveJ_38287
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 7449654739) ^ 3724827369 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (2 : ZMod 7449654739) ^ 2483218246 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (2 : ZMod 7449654739) ^ 229722 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (2 : ZMod 7449654739) ^ 194574 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide

private theorem prime_twelveJ_29798618957 : Nat.Prime 29798618957 := by
  apply lucas_primality 29798618957 (2 : ZMod 29798618957)
  · rw [← twelveJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (7449654739, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (7449654739, 1)] : List FactorBlock).map factorBlockValue).prod = 29798618957 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_twelveJ_2
      · exact prime_twelveJ_7449654739
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 29798618957) ^ 14899309478 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (2 : ZMod 29798618957) ^ 4 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide

private theorem prime_twelveJ_2991981134619696139127 : Nat.Prime 2991981134619696139127 := by
  apply lucas_primality 2991981134619696139127 (5 : ZMod 2991981134619696139127)
  · rw [← twelveJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (4969, 1), (10103311, 1), (29798618957, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (4969, 1), (10103311, 1), (29798618957, 1)] : List FactorBlock).map factorBlockValue).prod = 2991981134619696139127 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twelveJ_2
      · exact prime_twelveJ_4969
      · exact prime_twelveJ_10103311
      · exact prime_twelveJ_29798618957
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 2991981134619696139127) ^ 1495990567309848069563 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (5 : ZMod 2991981134619696139127) ^ 602129429386133254 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (5 : ZMod 2991981134619696139127) ^ 296138675194666 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (5 : ZMod 2991981134619696139127) ^ 100406704718 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide

private theorem prime_twelveJ_10103 : Nat.Prime 10103 := by norm_num
private theorem prime_twelveJ_743 : Nat.Prime 743 := by norm_num
private theorem prime_twelveJ_937 : Nat.Prime 937 := by norm_num
private theorem prime_twelveJ_7487 : Nat.Prime 7487 := by norm_num
private theorem prime_twelveJ_1466551 : Nat.Prime 1466551 := by norm_num
private theorem prime_twelveJ_2624309 : Nat.Prime 2624309 := by norm_num
private theorem prime_twelveJ_40121611994270067476807 : Nat.Prime 40121611994270067476807 := by
  apply lucas_primality 40121611994270067476807 (5 : ZMod 40121611994270067476807)
  · rw [← twelveJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (743, 1), (937, 1), (7487, 1), (1466551, 1), (2624309, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (743, 1), (937, 1), (7487, 1), (1466551, 1), (2624309, 1)] : List FactorBlock).map factorBlockValue).prod = 40121611994270067476807 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_twelveJ_2
      · exact prime_twelveJ_743
      · exact prime_twelveJ_937
      · exact prime_twelveJ_7487
      · exact prime_twelveJ_1466551
      · exact prime_twelveJ_2624309
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 40121611994270067476807) ^ 20060805997135033738403 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (5 : ZMod 40121611994270067476807) ^ 53999477785020279242 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (5 : ZMod 40121611994270067476807) ^ 42819223046179367638 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (5 : ZMod 40121611994270067476807) ^ 5358836916558042938 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (5 : ZMod 40121611994270067476807) ^ 27357802077302506 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (5 : ZMod 40121611994270067476807) ^ 15288448118826734 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide

private theorem prime_twelveJ_394088961367607422503787201 : Nat.Prime 394088961367607422503787201 := by
  apply lucas_primality 394088961367607422503787201 (103 : ZMod 394088961367607422503787201)
  · rw [← twelveJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 6), (3, 2), (5, 2), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 6), (3, 2), (5, 2), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod = 394088961367607422503787201 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_twelveJ_2
      · exact prime_twelveJ_3
      · exact prime_twelveJ_5
      · exact prime_twelveJ_7
      · exact prime_twelveJ_11
      · exact prime_twelveJ_13
      · exact prime_twelveJ_17
      · exact prime_twelveJ_19
      · exact prime_twelveJ_23
      · exact prime_twelveJ_29
      · exact prime_twelveJ_31
      · exact prime_twelveJ_37
      · exact prime_twelveJ_41
      · exact prime_twelveJ_43
      · exact prime_twelveJ_47
      · exact prime_twelveJ_53
      · exact prime_twelveJ_59
      · exact prime_twelveJ_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (103 : ZMod 394088961367607422503787201) ^ 197044480683803711251893600 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 131362987122535807501262400 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 78817792273521484500757440 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 56298423052515346071969600 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 35826269215237038409435200 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 30314535489815955577214400 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 23181703609859260147281600 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 20741524282505653815988800 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 17134302668156844456686400 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 13589274529917497327716800 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 12712547140890562016251200 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 10651053009935335743345600 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 9611925887014815183019200 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 9164859566688544709390400 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 8384871518459732393697600 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 7435640780520894764222400 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 6679473921484871567860800 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 6460474776518154467275200 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide

private theorem prime_twelveJ_10124467 : Nat.Prime 10124467 := by norm_num
private theorem prime_twelveJ_263 : Nat.Prime 263 := by norm_num
private theorem prime_twelveJ_16361 : Nat.Prime 16361 := by norm_num
private theorem prime_twelveJ_68639 : Nat.Prime 68639 := by norm_num
private theorem prime_twelveJ_1606701713 : Nat.Prime 1606701713 := by
  apply lucas_primality 1606701713 (5 : ZMod 1606701713)
  · rw [← twelveJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 4), (7, 1), (11, 1), (19, 1), (68639, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 4), (7, 1), (11, 1), (19, 1), (68639, 1)] : List FactorBlock).map factorBlockValue).prod = 1606701713 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twelveJ_2
      · exact prime_twelveJ_7
      · exact prime_twelveJ_11
      · exact prime_twelveJ_19
      · exact prime_twelveJ_68639
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 1606701713) ^ 803350856 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (5 : ZMod 1606701713) ^ 229528816 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (5 : ZMod 1606701713) ^ 146063792 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (5 : ZMod 1606701713) ^ 84563248 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (5 : ZMod 1606701713) ^ 23408 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide

private theorem prime_twelveJ_37872404380168564603 : Nat.Prime 37872404380168564603 := by
  apply lucas_primality 37872404380168564603 (2 : ZMod 37872404380168564603)
  · rw [← twelveJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (11, 1), (83, 1), (263, 1), (16361, 1), (1606701713, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (11, 1), (83, 1), (263, 1), (16361, 1), (1606701713, 1)] : List FactorBlock).map factorBlockValue).prod = 37872404380168564603 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_twelveJ_2
      · exact prime_twelveJ_3
      · exact prime_twelveJ_11
      · exact prime_twelveJ_83
      · exact prime_twelveJ_263
      · exact prime_twelveJ_16361
      · exact prime_twelveJ_1606701713
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 37872404380168564603) ^ 18936202190084282301 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (2 : ZMod 37872404380168564603) ^ 12624134793389521534 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (2 : ZMod 37872404380168564603) ^ 3442945852742596782 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (2 : ZMod 37872404380168564603) ^ 456294028676729694 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (2 : ZMod 37872404380168564603) ^ 144001537567180854 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (2 : ZMod 37872404380168564603) ^ 2314797651743082 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (2 : ZMod 37872404380168564603) ^ 23571521754 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide

private theorem prime_twelveJ_2712337 : Nat.Prime 2712337 := by norm_num
private theorem prime_twelveJ_2442113 : Nat.Prime 2442113 := by norm_num
private theorem prime_twelveJ_21683 : Nat.Prime 21683 := by norm_num
private theorem prime_twelveJ_106750482823 : Nat.Prime 106750482823 := by
  apply lucas_primality 106750482823 (3 : ZMod 106750482823)
  · rw [← twelveJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 3), (17, 1), (31, 1), (173, 1), (21683, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 3), (17, 1), (31, 1), (173, 1), (21683, 1)] : List FactorBlock).map factorBlockValue).prod = 106750482823 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_twelveJ_2
      · exact prime_twelveJ_3
      · exact prime_twelveJ_17
      · exact prime_twelveJ_31
      · exact prime_twelveJ_173
      · exact prime_twelveJ_21683
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 106750482823) ^ 53375241411 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (3 : ZMod 106750482823) ^ 35583494274 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (3 : ZMod 106750482823) ^ 6279440166 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (3 : ZMod 106750482823) ^ 3443563962 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (3 : ZMod 106750482823) ^ 617054814 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (3 : ZMod 106750482823) ^ 4923234 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide

private theorem prime_twelveJ_137647879701195599473 : Nat.Prime 137647879701195599473 := by
  apply lucas_primality 137647879701195599473 (5 : ZMod 137647879701195599473)
  · rw [← twelveJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 4), (3, 1), (11, 1), (2442113, 1), (106750482823, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 4), (3, 1), (11, 1), (2442113, 1), (106750482823, 1)] : List FactorBlock).map factorBlockValue).prod = 137647879701195599473 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twelveJ_2
      · exact prime_twelveJ_3
      · exact prime_twelveJ_11
      · exact prime_twelveJ_2442113
      · exact prime_twelveJ_106750482823
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 137647879701195599473) ^ 68823939850597799736 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (5 : ZMod 137647879701195599473) ^ 45882626567065199824 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (5 : ZMod 137647879701195599473) ^ 12513443609199599952 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (5 : ZMod 137647879701195599473) ^ 56364254930544 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (5 : ZMod 137647879701195599473) ^ 1289435664 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide

private theorem prime_twelveJ_251 : Nat.Prime 251 := by norm_num
private theorem prime_twelveJ_1321 : Nat.Prime 1321 := by norm_num
private theorem prime_twelveJ_1787 : Nat.Prime 1787 := by norm_num
private theorem prime_twelveJ_1255074433 : Nat.Prime 1255074433 := by
  apply lucas_primality 1255074433 (10 : ZMod 1255074433)
  · rw [← twelveJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 7), (3, 1), (31, 1), (59, 1), (1787, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 7), (3, 1), (31, 1), (59, 1), (1787, 1)] : List FactorBlock).map factorBlockValue).prod = 1255074433 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twelveJ_2
      · exact prime_twelveJ_3
      · exact prime_twelveJ_31
      · exact prime_twelveJ_59
      · exact prime_twelveJ_1787
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 1255074433) ^ 627537216 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (10 : ZMod 1255074433) ^ 418358144 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (10 : ZMod 1255074433) ^ 40486272 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (10 : ZMod 1255074433) ^ 21272448 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (10 : ZMod 1255074433) ^ 702336 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide

private theorem prime_twelveJ_492979 : Nat.Prime 492979 := by norm_num
private theorem prime_twelveJ_17483007257 : Nat.Prime 17483007257 := by
  apply lucas_primality 17483007257 (6 : ZMod 17483007257)
  · rw [← twelveJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (11, 1), (13, 1), (31, 1), (492979, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (11, 1), (13, 1), (31, 1), (492979, 1)] : List FactorBlock).map factorBlockValue).prod = 17483007257 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twelveJ_2
      · exact prime_twelveJ_11
      · exact prime_twelveJ_13
      · exact prime_twelveJ_31
      · exact prime_twelveJ_492979
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 17483007257) ^ 8741503628 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (6 : ZMod 17483007257) ^ 1589364296 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (6 : ZMod 17483007257) ^ 1344846712 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (6 : ZMod 17483007257) ^ 563967976 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (6 : ZMod 17483007257) ^ 35464 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide

private theorem prime_twelveJ_1449300501505145286560051 : Nat.Prime 1449300501505145286560051 := by
  apply lucas_primality 1449300501505145286560051 (6 : ZMod 1449300501505145286560051)
  · rw [← twelveJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 2), (1321, 1), (1255074433, 1), (17483007257, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 2), (1321, 1), (1255074433, 1), (17483007257, 1)] : List FactorBlock).map factorBlockValue).prod = 1449300501505145286560051 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twelveJ_2
      · exact prime_twelveJ_5
      · exact prime_twelveJ_1321
      · exact prime_twelveJ_1255074433
      · exact prime_twelveJ_17483007257
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 1449300501505145286560051) ^ 724650250752572643280025 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (6 : ZMod 1449300501505145286560051) ^ 289860100301029057312010 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (6 : ZMod 1449300501505145286560051) ^ 1097123771010708014050 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (6 : ZMod 1449300501505145286560051) ^ 1154752629324850 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (6 : ZMod 1449300501505145286560051) ^ 82897666299650 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide

private theorem prime_twelveJ_180533 : Nat.Prime 180533 := by norm_num
private theorem prime_twelveJ_2161 : Nat.Prime 2161 := by norm_num
private theorem prime_twelveJ_8537 : Nat.Prime 8537 := by norm_num
private theorem prime_twelveJ_79 : Nat.Prime 79 := by norm_num
private theorem prime_twelveJ_561521 : Nat.Prime 561521 := by norm_num
private theorem prime_twelveJ_19518469961 : Nat.Prime 19518469961 := by
  apply lucas_primality 19518469961 (3 : ZMod 19518469961)
  · rw [← twelveJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (5, 1), (11, 1), (79, 1), (561521, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (5, 1), (11, 1), (79, 1), (561521, 1)] : List FactorBlock).map factorBlockValue).prod = 19518469961 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twelveJ_2
      · exact prime_twelveJ_5
      · exact prime_twelveJ_11
      · exact prime_twelveJ_79
      · exact prime_twelveJ_561521
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 19518469961) ^ 9759234980 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (3 : ZMod 19518469961) ^ 3903693992 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (3 : ZMod 19518469961) ^ 1774406360 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (3 : ZMod 19518469961) ^ 247069240 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (3 : ZMod 19518469961) ^ 34760 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide

private theorem prime_twelveJ_44650621068881221949 : Nat.Prime 44650621068881221949 := by
  apply lucas_primality 44650621068881221949 (2 : ZMod 44650621068881221949)
  · rw [← twelveJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (31, 1), (2161, 1), (8537, 1), (19518469961, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (31, 1), (2161, 1), (8537, 1), (19518469961, 1)] : List FactorBlock).map factorBlockValue).prod = 44650621068881221949 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twelveJ_2
      · exact prime_twelveJ_31
      · exact prime_twelveJ_2161
      · exact prime_twelveJ_8537
      · exact prime_twelveJ_19518469961
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 44650621068881221949) ^ 22325310534440610974 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (2 : ZMod 44650621068881221949) ^ 1440342615125200708 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (2 : ZMod 44650621068881221949) ^ 20662018079075068 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (2 : ZMod 44650621068881221949) ^ 5230247284629404 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (2 : ZMod 44650621068881221949) ^ 2287608668 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide

private theorem prime_twelveJ_1964627327030773765757 : Nat.Prime 1964627327030773765757 := by
  apply lucas_primality 1964627327030773765757 (3 : ZMod 1964627327030773765757)
  · rw [← twelveJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (11, 1), (44650621068881221949, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (11, 1), (44650621068881221949, 1)] : List FactorBlock).map factorBlockValue).prod = 1964627327030773765757 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twelveJ_2
      · exact prime_twelveJ_11
      · exact prime_twelveJ_44650621068881221949
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 1964627327030773765757) ^ 982313663515386882878 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (3 : ZMod 1964627327030773765757) ^ 178602484275524887796 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (3 : ZMod 1964627327030773765757) ^ 44 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide

private theorem prime_twelveJ_16492747 : Nat.Prime 16492747 := by norm_num
private theorem prime_twelveJ_5094919 : Nat.Prime 5094919 := by norm_num
private theorem prime_twelveJ_491357 : Nat.Prime 491357 := by norm_num
private theorem prime_twelveJ_47170273 : Nat.Prime 47170273 := by
  apply lucas_primality 47170273 (7 : ZMod 47170273)
  · rw [← twelveJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 5), (3, 1), (491357, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 5), (3, 1), (491357, 1)] : List FactorBlock).map factorBlockValue).prod = 47170273 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twelveJ_2
      · exact prime_twelveJ_3
      · exact prime_twelveJ_491357
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 47170273) ^ 23585136 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (7 : ZMod 47170273) ^ 15723424 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (7 : ZMod 47170273) ^ 96 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide

private theorem prime_twelveJ_36049308021433051 : Nat.Prime 36049308021433051 := by
  apply lucas_primality 36049308021433051 (3 : ZMod 36049308021433051)
  · rw [← twelveJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (5, 2), (5094919, 1), (47170273, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (5, 2), (5094919, 1), (47170273, 1)] : List FactorBlock).map factorBlockValue).prod = 36049308021433051 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twelveJ_2
      · exact prime_twelveJ_3
      · exact prime_twelveJ_5
      · exact prime_twelveJ_5094919
      · exact prime_twelveJ_47170273
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 36049308021433051) ^ 18024654010716525 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (3 : ZMod 36049308021433051) ^ 12016436007144350 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (3 : ZMod 36049308021433051) ^ 7209861604286610 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (3 : ZMod 36049308021433051) ^ 7075540950 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (3 : ZMod 36049308021433051) ^ 764237850 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide

private theorem prime_twelveJ_20980697268474035683 : Nat.Prime 20980697268474035683 := by
  apply lucas_primality 20980697268474035683 (2 : ZMod 20980697268474035683)
  · rw [← twelveJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (97, 1), (36049308021433051, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (97, 1), (36049308021433051, 1)] : List FactorBlock).map factorBlockValue).prod = 20980697268474035683 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twelveJ_2
      · exact prime_twelveJ_3
      · exact prime_twelveJ_97
      · exact prime_twelveJ_36049308021433051
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 20980697268474035683) ^ 10490348634237017841 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (2 : ZMod 20980697268474035683) ^ 6993565756158011894 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (2 : ZMod 20980697268474035683) ^ 216295848128598306 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (2 : ZMod 20980697268474035683) ^ 582 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide

private theorem prime_twelveJ_97523 : Nat.Prime 97523 := by norm_num
private theorem prime_twelveJ_467 : Nat.Prime 467 := by norm_num
private theorem prime_twelveJ_1123 : Nat.Prime 1123 := by norm_num
private theorem prime_twelveJ_5826967 : Nat.Prime 5826967 := by norm_num
private theorem prime_twelveJ_138448735921 : Nat.Prime 138448735921 := by
  apply lucas_primality 138448735921 (14 : ZMod 138448735921)
  · rw [← twelveJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 4), (3, 3), (5, 1), (11, 1), (5826967, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 4), (3, 3), (5, 1), (11, 1), (5826967, 1)] : List FactorBlock).map factorBlockValue).prod = 138448735921 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twelveJ_2
      · exact prime_twelveJ_3
      · exact prime_twelveJ_5
      · exact prime_twelveJ_11
      · exact prime_twelveJ_5826967
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (14 : ZMod 138448735921) ^ 69224367960 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (14 : ZMod 138448735921) ^ 46149578640 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (14 : ZMod 138448735921) ^ 27689747184 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (14 : ZMod 138448735921) ^ 12586248720 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (14 : ZMod 138448735921) ^ 23760 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide

private theorem prime_twelveJ_621911721757133 : Nat.Prime 621911721757133 := by
  apply lucas_primality 621911721757133 (2 : ZMod 621911721757133)
  · rw [← twelveJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (1123, 1), (138448735921, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (1123, 1), (138448735921, 1)] : List FactorBlock).map factorBlockValue).prod = 621911721757133 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twelveJ_2
      · exact prime_twelveJ_1123
      · exact prime_twelveJ_138448735921
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 621911721757133) ^ 310955860878566 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (2 : ZMod 621911721757133) ^ 553794943684 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (2 : ZMod 621911721757133) ^ 4492 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide

private theorem prime_twelveJ_3463701263446490329787 : Nat.Prime 3463701263446490329787 := by
  apply lucas_primality 3463701263446490329787 (2 : ZMod 3463701263446490329787)
  · rw [← twelveJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (67, 1), (89, 1), (467, 1), (621911721757133, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (67, 1), (89, 1), (467, 1), (621911721757133, 1)] : List FactorBlock).map factorBlockValue).prod = 3463701263446490329787 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twelveJ_2
      · exact prime_twelveJ_67
      · exact prime_twelveJ_89
      · exact prime_twelveJ_467
      · exact prime_twelveJ_621911721757133
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 3463701263446490329787) ^ 1731850631723245164893 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (2 : ZMod 3463701263446490329787) ^ 51697033782783437758 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (2 : ZMod 3463701263446490329787) ^ 38917991724117868874 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (2 : ZMod 3463701263446490329787) ^ 7416919193675568158 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (2 : ZMod 3463701263446490329787) ^ 5569442 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide

private theorem prime_twelveJ_709 : Nat.Prime 709 := by norm_num
private theorem prime_twelveJ_342833 : Nat.Prime 342833 := by norm_num
private theorem prime_twelveJ_188621231273 : Nat.Prime 188621231273 := by
  apply lucas_primality 188621231273 (3 : ZMod 188621231273)
  · rw [← twelveJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (97, 1), (709, 1), (342833, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (97, 1), (709, 1), (342833, 1)] : List FactorBlock).map factorBlockValue).prod = 188621231273 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twelveJ_2
      · exact prime_twelveJ_97
      · exact prime_twelveJ_709
      · exact prime_twelveJ_342833
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 188621231273) ^ 94310615636 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (3 : ZMod 188621231273) ^ 1944548776 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (3 : ZMod 188621231273) ^ 266038408 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (3 : ZMod 188621231273) ^ 550184 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide

private theorem prime_twelveJ_8299334176013 : Nat.Prime 8299334176013 := by
  apply lucas_primality 8299334176013 (2 : ZMod 8299334176013)
  · rw [← twelveJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (11, 1), (188621231273, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (11, 1), (188621231273, 1)] : List FactorBlock).map factorBlockValue).prod = 8299334176013 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twelveJ_2
      · exact prime_twelveJ_11
      · exact prime_twelveJ_188621231273
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 8299334176013) ^ 4149667088006 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (2 : ZMod 8299334176013) ^ 754484925092 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (2 : ZMod 8299334176013) ^ 44 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide

private theorem prime_twelveJ_2341 : Nat.Prime 2341 := by norm_num
private theorem prime_twelveJ_45599 : Nat.Prime 45599 := by norm_num
private theorem prime_twelveJ_451754400089 : Nat.Prime 451754400089 := by
  apply lucas_primality 451754400089 (3 : ZMod 451754400089)
  · rw [← twelveJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (23, 2), (2341, 1), (45599, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (23, 2), (2341, 1), (45599, 1)] : List FactorBlock).map factorBlockValue).prod = 451754400089 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twelveJ_2
      · exact prime_twelveJ_23
      · exact prime_twelveJ_2341
      · exact prime_twelveJ_45599
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 451754400089) ^ 225877200044 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (3 : ZMod 451754400089) ^ 19641495656 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (3 : ZMod 451754400089) ^ 192974968 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (3 : ZMod 451754400089) ^ 9907112 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide

private theorem prime_twelveJ_903508800179 : Nat.Prime 903508800179 := by
  apply lucas_primality 903508800179 (2 : ZMod 903508800179)
  · rw [← twelveJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (451754400089, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (451754400089, 1)] : List FactorBlock).map factorBlockValue).prod = 903508800179 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_twelveJ_2
      · exact prime_twelveJ_451754400089
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 903508800179) ^ 451754400089 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (2 : ZMod 903508800179) ^ 2 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide

private theorem prime_twelveJ_39754387207877 : Nat.Prime 39754387207877 := by
  apply lucas_primality 39754387207877 (2 : ZMod 39754387207877)
  · rw [← twelveJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (11, 1), (903508800179, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (11, 1), (903508800179, 1)] : List FactorBlock).map factorBlockValue).prod = 39754387207877 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twelveJ_2
      · exact prime_twelveJ_11
      · exact prime_twelveJ_903508800179
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 39754387207877) ^ 19877193603938 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (2 : ZMod 39754387207877) ^ 3614035200716 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (2 : ZMod 39754387207877) ^ 44 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide

private theorem prime_twelveJ_4637 : Nat.Prime 4637 := by norm_num
private theorem prime_twelveJ_13311821 : Nat.Prime 13311821 := by norm_num
private theorem prime_twelveJ_2076644077 : Nat.Prime 2076644077 := by
  apply lucas_primality 2076644077 (2 : ZMod 2076644077)
  · rw [← twelveJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (13, 1), (13311821, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (13, 1), (13311821, 1)] : List FactorBlock).map factorBlockValue).prod = 2076644077 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twelveJ_2
      · exact prime_twelveJ_3
      · exact prime_twelveJ_13
      · exact prime_twelveJ_13311821
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 2076644077) ^ 1038322038 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (2 : ZMod 2076644077) ^ 692214692 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (2 : ZMod 2076644077) ^ 159741852 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (2 : ZMod 2076644077) ^ 156 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide

private theorem prime_twelveJ_809 : Nat.Prime 809 := by norm_num
private theorem prime_twelveJ_1873 : Nat.Prime 1873 := by norm_num
private theorem prime_twelveJ_14851 : Nat.Prime 14851 := by norm_num
private theorem prime_twelveJ_166895539 : Nat.Prime 166895539 := by
  apply lucas_primality 166895539 (2 : ZMod 166895539)
  · rw [← twelveJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (1873, 1), (14851, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (1873, 1), (14851, 1)] : List FactorBlock).map factorBlockValue).prod = 166895539 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twelveJ_2
      · exact prime_twelveJ_3
      · exact prime_twelveJ_1873
      · exact prime_twelveJ_14851
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 166895539) ^ 83447769 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (2 : ZMod 166895539) ^ 55631846 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (2 : ZMod 166895539) ^ 89106 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (2 : ZMod 166895539) ^ 11238 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide

private theorem prime_twelveJ_33484585780649 : Nat.Prime 33484585780649 := by
  apply lucas_primality 33484585780649 (3 : ZMod 33484585780649)
  · rw [← twelveJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (31, 1), (809, 1), (166895539, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (31, 1), (809, 1), (166895539, 1)] : List FactorBlock).map factorBlockValue).prod = 33484585780649 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twelveJ_2
      · exact prime_twelveJ_31
      · exact prime_twelveJ_809
      · exact prime_twelveJ_166895539
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 33484585780649) ^ 16742292890324 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (3 : ZMod 33484585780649) ^ 1080147928408 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (3 : ZMod 33484585780649) ^ 41390093672 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (3 : ZMod 33484585780649) ^ 200632 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide

private theorem prime_twelveJ_22397 : Nat.Prime 22397 := by norm_num
private theorem prime_twelveJ_73771 : Nat.Prime 73771 := by norm_num
private theorem prime_twelveJ_139 : Nat.Prime 139 := by norm_num
private theorem prime_twelveJ_3477841 : Nat.Prime 3477841 := by norm_num
private theorem prime_twelveJ_41734093 : Nat.Prime 41734093 := by
  apply lucas_primality 41734093 (2 : ZMod 41734093)
  · rw [← twelveJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (3477841, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (3477841, 1)] : List FactorBlock).map factorBlockValue).prod = 41734093 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twelveJ_2
      · exact prime_twelveJ_3
      · exact prime_twelveJ_3477841
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 41734093) ^ 20867046 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (2 : ZMod 41734093) ^ 13911364 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (2 : ZMod 41734093) ^ 12 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide

private theorem prime_twelveJ_82299631397 : Nat.Prime 82299631397 := by
  apply lucas_primality 82299631397 (2 : ZMod 82299631397)
  · rw [← twelveJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (17, 1), (29, 1), (41734093, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (17, 1), (29, 1), (41734093, 1)] : List FactorBlock).map factorBlockValue).prod = 82299631397 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twelveJ_2
      · exact prime_twelveJ_17
      · exact prime_twelveJ_29
      · exact prime_twelveJ_41734093
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 82299631397) ^ 41149815698 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (2 : ZMod 82299631397) ^ 4841154788 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (2 : ZMod 82299631397) ^ 2837918324 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (2 : ZMod 82299631397) ^ 1972 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide

private theorem prime_twelveJ_493797788383 : Nat.Prime 493797788383 := by
  apply lucas_primality 493797788383 (3 : ZMod 493797788383)
  · rw [← twelveJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (82299631397, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (82299631397, 1)] : List FactorBlock).map factorBlockValue).prod = 493797788383 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twelveJ_2
      · exact prime_twelveJ_3
      · exact prime_twelveJ_82299631397
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 493797788383) ^ 246898894191 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (3 : ZMod 493797788383) ^ 164599262794 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (3 : ZMod 493797788383) ^ 6 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide

private theorem prime_twelveJ_4937977883831 : Nat.Prime 4937977883831 := by
  apply lucas_primality 4937977883831 (11 : ZMod 4937977883831)
  · rw [← twelveJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 1), (493797788383, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 1), (493797788383, 1)] : List FactorBlock).map factorBlockValue).prod = 4937977883831 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twelveJ_2
      · exact prime_twelveJ_5
      · exact prime_twelveJ_493797788383
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (11 : ZMod 4937977883831) ^ 2468988941915 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (11 : ZMod 4937977883831) ^ 987595576766 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (11 : ZMod 4937977883831) ^ 10 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide

private theorem prime_twelveJ_190813341386997503 : Nat.Prime 190813341386997503 := by
  apply lucas_primality 190813341386997503 (5 : ZMod 190813341386997503)
  · rw [← twelveJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (139, 2), (4937977883831, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (139, 2), (4937977883831, 1)] : List FactorBlock).map factorBlockValue).prod = 190813341386997503 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twelveJ_2
      · exact prime_twelveJ_139
      · exact prime_twelveJ_4937977883831
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 190813341386997503) ^ 95406670693498751 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (5 : ZMod 190813341386997503) ^ 1372757851705018 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (5 : ZMod 190813341386997503) ^ 38642 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide

private theorem prime_twelveJ_953 : Nat.Prime 953 := by norm_num
private theorem prime_twelveJ_34157 : Nat.Prime 34157 := by norm_num
private theorem prime_twelveJ_387017 : Nat.Prime 387017 := by norm_num
private theorem prime_twelveJ_485319319 : Nat.Prime 485319319 := by
  apply lucas_primality 485319319 (6 : ZMod 485319319)
  · rw [← twelveJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (11, 1), (19, 1), (387017, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (11, 1), (19, 1), (387017, 1)] : List FactorBlock).map factorBlockValue).prod = 485319319 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twelveJ_2
      · exact prime_twelveJ_3
      · exact prime_twelveJ_11
      · exact prime_twelveJ_19
      · exact prime_twelveJ_387017
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 485319319) ^ 242659659 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (6 : ZMod 485319319) ^ 161773106 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (6 : ZMod 485319319) ^ 44119938 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (6 : ZMod 485319319) ^ 25543122 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (6 : ZMod 485319319) ^ 1254 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide

private theorem prime_twelveJ_578209 : Nat.Prime 578209 := by norm_num
private theorem prime_twelveJ_848810813 : Nat.Prime 848810813 := by
  apply lucas_primality 848810813 (2 : ZMod 848810813)
  · rw [← twelveJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (367, 1), (578209, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (367, 1), (578209, 1)] : List FactorBlock).map factorBlockValue).prod = 848810813 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twelveJ_2
      · exact prime_twelveJ_367
      · exact prime_twelveJ_578209
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 848810813) ^ 424405406 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (2 : ZMod 848810813) ^ 2312836 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (2 : ZMod 848810813) ^ 1468 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide

private theorem prime_twelveJ_178831 : Nat.Prime 178831 := by norm_num
private theorem prime_twelveJ_27961 : Nat.Prime 27961 := by norm_num
private theorem prime_twelveJ_175961 : Nat.Prime 175961 := by norm_num
private theorem prime_twelveJ_319291274130817 : Nat.Prime 319291274130817 := by
  apply lucas_primality 319291274130817 (5 : ZMod 319291274130817)
  · rw [← twelveJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 7), (3, 1), (13, 2), (27961, 1), (175961, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 7), (3, 1), (13, 2), (27961, 1), (175961, 1)] : List FactorBlock).map factorBlockValue).prod = 319291274130817 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twelveJ_2
      · exact prime_twelveJ_3
      · exact prime_twelveJ_13
      · exact prime_twelveJ_27961
      · exact prime_twelveJ_175961
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 319291274130817) ^ 159645637065408 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (5 : ZMod 319291274130817) ^ 106430424710272 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (5 : ZMod 319291274130817) ^ 24560867240832 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (5 : ZMod 319291274130817) ^ 11419165056 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (5 : ZMod 319291274130817) ^ 1814557056 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide

private theorem prime_twelveJ_1687936513605305378671 : Nat.Prime 1687936513605305378671 := by
  apply lucas_primality 1687936513605305378671 (3 : ZMod 1687936513605305378671)
  · rw [← twelveJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 2), (5, 1), (151, 1), (389, 1), (319291274130817, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 2), (5, 1), (151, 1), (389, 1), (319291274130817, 1)] : List FactorBlock).map factorBlockValue).prod = 1687936513605305378671 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_twelveJ_2
      · exact prime_twelveJ_3
      · exact prime_twelveJ_5
      · exact prime_twelveJ_151
      · exact prime_twelveJ_389
      · exact prime_twelveJ_319291274130817
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1687936513605305378671) ^ 843968256802652689335 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (3 : ZMod 1687936513605305378671) ^ 562645504535101792890 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (3 : ZMod 1687936513605305378671) ^ 337587302721061075734 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (3 : ZMod 1687936513605305378671) ^ 11178387507319903170 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (3 : ZMod 1687936513605305378671) ^ 4339168415437803030 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (3 : ZMod 1687936513605305378671) ^ 5286510 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide

private theorem prime_twelveJ_18959 : Nat.Prime 18959 := by norm_num
private theorem prime_twelveJ_20930737 : Nat.Prime 20930737 := by
  apply lucas_primality 20930737 (5 : ZMod 20930737)
  · rw [← twelveJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 4), (3, 1), (23, 1), (18959, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 4), (3, 1), (23, 1), (18959, 1)] : List FactorBlock).map factorBlockValue).prod = 20930737 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twelveJ_2
      · exact prime_twelveJ_3
      · exact prime_twelveJ_23
      · exact prime_twelveJ_18959
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 20930737) ^ 10465368 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (5 : ZMod 20930737) ^ 6976912 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (5 : ZMod 20930737) ^ 910032 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (5 : ZMod 20930737) ^ 1104 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide

private theorem prime_twelveJ_28807 : Nat.Prime 28807 := by norm_num
private theorem prime_twelveJ_1849103 : Nat.Prime 1849103 := by norm_num
private theorem prime_twelveJ_456818736397697 : Nat.Prime 456818736397697 := by
  apply lucas_primality 456818736397697 (3 : ZMod 456818736397697)
  · rw [← twelveJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 7), (67, 1), (28807, 1), (1849103, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 7), (67, 1), (28807, 1), (1849103, 1)] : List FactorBlock).map factorBlockValue).prod = 456818736397697 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twelveJ_2
      · exact prime_twelveJ_67
      · exact prime_twelveJ_28807
      · exact prime_twelveJ_1849103
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 456818736397697) ^ 228409368198848 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (3 : ZMod 456818736397697) ^ 6818190095488 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (3 : ZMod 456818736397697) ^ 15857907328 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (3 : ZMod 456818736397697) ^ 247048832 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide

private theorem prime_twelveJ_6395462309567759 : Nat.Prime 6395462309567759 := by
  apply lucas_primality 6395462309567759 (7 : ZMod 6395462309567759)
  · rw [← twelveJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (7, 1), (456818736397697, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (7, 1), (456818736397697, 1)] : List FactorBlock).map factorBlockValue).prod = 6395462309567759 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twelveJ_2
      · exact prime_twelveJ_7
      · exact prime_twelveJ_456818736397697
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 6395462309567759) ^ 3197731154783879 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (7 : ZMod 6395462309567759) ^ 913637472795394 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (7 : ZMod 6395462309567759) ^ 14 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide

private theorem prime_twelveJ_14121180779525611873 : Nat.Prime 14121180779525611873 := by
  apply lucas_primality 14121180779525611873 (5 : ZMod 14121180779525611873)
  · rw [← twelveJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 5), (3, 1), (23, 1), (6395462309567759, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 5), (3, 1), (23, 1), (6395462309567759, 1)] : List FactorBlock).map factorBlockValue).prod = 14121180779525611873 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twelveJ_2
      · exact prime_twelveJ_3
      · exact prime_twelveJ_23
      · exact prime_twelveJ_6395462309567759
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 14121180779525611873) ^ 7060590389762805936 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (5 : ZMod 14121180779525611873) ^ 4707060259841870624 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (5 : ZMod 14121180779525611873) ^ 613964381718504864 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (5 : ZMod 14121180779525611873) ^ 2208 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide

private theorem prime_twelveJ_1951321 : Nat.Prime 1951321 := by norm_num
private theorem prime_twelveJ_18382753 : Nat.Prime 18382753 := by norm_num
private theorem prime_twelveJ_2861 : Nat.Prime 2861 := by norm_num
private theorem prime_twelveJ_603802607 : Nat.Prime 603802607 := by
  apply lucas_primality 603802607 (5 : ZMod 603802607)
  · rw [← twelveJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (11, 1), (53, 1), (181, 1), (2861, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (11, 1), (53, 1), (181, 1), (2861, 1)] : List FactorBlock).map factorBlockValue).prod = 603802607 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twelveJ_2
      · exact prime_twelveJ_11
      · exact prime_twelveJ_53
      · exact prime_twelveJ_181
      · exact prime_twelveJ_2861
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 603802607) ^ 301901303 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (5 : ZMod 603802607) ^ 54891146 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (5 : ZMod 603802607) ^ 11392502 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (5 : ZMod 603802607) ^ 3335926 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (5 : ZMod 603802607) ^ 211046 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide

private theorem prime_twelveJ_8071633250377 : Nat.Prime 8071633250377 := by
  apply lucas_primality 8071633250377 (5 : ZMod 8071633250377)
  · rw [← twelveJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (3, 1), (557, 1), (603802607, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (3, 1), (557, 1), (603802607, 1)] : List FactorBlock).map factorBlockValue).prod = 8071633250377 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twelveJ_2
      · exact prime_twelveJ_3
      · exact prime_twelveJ_557
      · exact prime_twelveJ_603802607
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 8071633250377) ^ 4035816625188 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (5 : ZMod 8071633250377) ^ 2690544416792 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (5 : ZMod 8071633250377) ^ 14491262568 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (5 : ZMod 8071633250377) ^ 13368 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide

private theorem prime_twelveJ_489673 : Nat.Prime 489673 := by norm_num
private theorem prime_twelveJ_6911 : Nat.Prime 6911 := by norm_num
private theorem prime_twelveJ_8377 : Nat.Prime 8377 := by norm_num
private theorem prime_twelveJ_46649 : Nat.Prime 46649 := by norm_num
private theorem prime_twelveJ_54319 : Nat.Prime 54319 := by norm_num
private theorem prime_twelveJ_1466977702710658571 : Nat.Prime 1466977702710658571 := by
  apply lucas_primality 1466977702710658571 (2 : ZMod 1466977702710658571)
  · rw [← twelveJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 1), (6911, 1), (8377, 1), (46649, 1), (54319, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 1), (6911, 1), (8377, 1), (46649, 1), (54319, 1)] : List FactorBlock).map factorBlockValue).prod = 1466977702710658571 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_twelveJ_2
      · exact prime_twelveJ_5
      · exact prime_twelveJ_6911
      · exact prime_twelveJ_8377
      · exact prime_twelveJ_46649
      · exact prime_twelveJ_54319
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1466977702710658571) ^ 733488851355329285 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (2 : ZMod 1466977702710658571) ^ 293395540542131714 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (2 : ZMod 1466977702710658571) ^ 212267067386870 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (2 : ZMod 1466977702710658571) ^ 175119697112410 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (2 : ZMod 1466977702710658571) ^ 31447141475930 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (2 : ZMod 1466977702710658571) ^ 27006714091030 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide

private theorem prime_twelveJ_73 : Nat.Prime 73 := by norm_num
private theorem prime_twelveJ_1609 : Nat.Prime 1609 := by norm_num
private theorem prime_twelveJ_29021 : Nat.Prime 29021 := by norm_num
private theorem prime_twelveJ_2685877 : Nat.Prime 2685877 := by norm_num
private theorem prime_twelveJ_1709 : Nat.Prime 1709 := by norm_num
private theorem prime_twelveJ_14431 : Nat.Prime 14431 := by norm_num
private theorem prime_twelveJ_30384297329 : Nat.Prime 30384297329 := by
  apply lucas_primality 30384297329 (3 : ZMod 30384297329)
  · rw [← twelveJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 4), (7, 1), (11, 1), (1709, 1), (14431, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 4), (7, 1), (11, 1), (1709, 1), (14431, 1)] : List FactorBlock).map factorBlockValue).prod = 30384297329 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twelveJ_2
      · exact prime_twelveJ_7
      · exact prime_twelveJ_11
      · exact prime_twelveJ_1709
      · exact prime_twelveJ_14431
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 30384297329) ^ 15192148664 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (3 : ZMod 30384297329) ^ 4340613904 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (3 : ZMod 30384297329) ^ 2762208848 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (3 : ZMod 30384297329) ^ 17778992 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (3 : ZMod 30384297329) ^ 2105488 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide

private theorem prime_twelveJ_272830819408343600194929601 : Nat.Prime 272830819408343600194929601 := by
  apply lucas_primality 272830819408343600194929601 (39 : ZMod 272830819408343600194929601)
  · rw [← twelveJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 6), (3, 4), (5, 2), (7, 2), (11, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 6), (3, 4), (5, 2), (7, 2), (11, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod = 272830819408343600194929601 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_twelveJ_2
      · exact prime_twelveJ_3
      · exact prime_twelveJ_5
      · exact prime_twelveJ_7
      · exact prime_twelveJ_11
      · exact prime_twelveJ_17
      · exact prime_twelveJ_19
      · exact prime_twelveJ_23
      · exact prime_twelveJ_29
      · exact prime_twelveJ_31
      · exact prime_twelveJ_37
      · exact prime_twelveJ_41
      · exact prime_twelveJ_43
      · exact prime_twelveJ_47
      · exact prime_twelveJ_53
      · exact prime_twelveJ_59
      · exact prime_twelveJ_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (39 : ZMod 272830819408343600194929601) ^ 136415409704171800097464800 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (39 : ZMod 272830819408343600194929601) ^ 90943606469447866731643200 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (39 : ZMod 272830819408343600194929601) ^ 54566163881668720038985920 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (39 : ZMod 272830819408343600194929601) ^ 38975831344049085742132800 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (39 : ZMod 272830819408343600194929601) ^ 24802801764394872744993600 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (39 : ZMod 272830819408343600194929601) ^ 16048871729902564717348800 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (39 : ZMod 272830819408343600194929601) ^ 14359516810965452641838400 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (39 : ZMod 272830819408343600194929601) ^ 11862209539493200008475200 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (39 : ZMod 272830819408343600194929601) ^ 9407959289942882765342400 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (39 : ZMod 272830819408343600194929601) ^ 8800994174462696780481600 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (39 : ZMod 272830819408343600194929601) ^ 7373805929955232437700800 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (39 : ZMod 272830819408343600194929601) ^ 6654410229471795126705600 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (39 : ZMod 272830819408343600194929601) ^ 6344902776938223260347200 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (39 : ZMod 272830819408343600194929601) ^ 5804911051241353195636800 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (39 : ZMod 272830819408343600194929601) ^ 5147751309591388682923200 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (39 : ZMod 272830819408343600194929601) ^ 4624251176412603393134400 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (39 : ZMod 272830819408343600194929601) ^ 4472636383743337708113600 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide

private theorem prime_twelveJ_712739 : Nat.Prime 712739 := by norm_num
private theorem prime_twelveJ_142759 : Nat.Prime 142759 := by norm_num
private theorem prime_twelveJ_61671889 : Nat.Prime 61671889 := by
  apply lucas_primality 61671889 (7 : ZMod 61671889)
  · rw [← twelveJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 4), (3, 3), (142759, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 4), (3, 3), (142759, 1)] : List FactorBlock).map factorBlockValue).prod = 61671889 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twelveJ_2
      · exact prime_twelveJ_3
      · exact prime_twelveJ_142759
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 61671889) ^ 30835944 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (7 : ZMod 61671889) ^ 20557296 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (7 : ZMod 61671889) ^ 432 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide

private theorem prime_twelveJ_487 : Nat.Prime 487 := by norm_num
private theorem prime_twelveJ_8117 : Nat.Prime 8117 := by norm_num
private theorem prime_twelveJ_178638937 : Nat.Prime 178638937 := by
  apply lucas_primality 178638937 (5 : ZMod 178638937)
  · rw [← twelveJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (3, 1), (7, 1), (131, 1), (8117, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (3, 1), (7, 1), (131, 1), (8117, 1)] : List FactorBlock).map factorBlockValue).prod = 178638937 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twelveJ_2
      · exact prime_twelveJ_3
      · exact prime_twelveJ_7
      · exact prime_twelveJ_131
      · exact prime_twelveJ_8117
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 178638937) ^ 89319468 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (5 : ZMod 178638937) ^ 59546312 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (5 : ZMod 178638937) ^ 25519848 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (5 : ZMod 178638937) ^ 1363656 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (5 : ZMod 178638937) ^ 22008 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide

private theorem prime_twelveJ_6089801362331 : Nat.Prime 6089801362331 := by
  apply lucas_primality 6089801362331 (6 : ZMod 6089801362331)
  · rw [← twelveJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 1), (7, 1), (487, 1), (178638937, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 1), (7, 1), (487, 1), (178638937, 1)] : List FactorBlock).map factorBlockValue).prod = 6089801362331 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twelveJ_2
      · exact prime_twelveJ_5
      · exact prime_twelveJ_7
      · exact prime_twelveJ_487
      · exact prime_twelveJ_178638937
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 6089801362331) ^ 3044900681165 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (6 : ZMod 6089801362331) ^ 1217960272466 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (6 : ZMod 6089801362331) ^ 869971623190 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (6 : ZMod 6089801362331) ^ 12504725590 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (6 : ZMod 6089801362331) ^ 34090 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide

private theorem prime_twelveJ_491 : Nat.Prime 491 := by norm_num
private theorem prime_twelveJ_1061 : Nat.Prime 1061 := by norm_num
private theorem prime_twelveJ_9492089 : Nat.Prime 9492089 := by norm_num
private theorem prime_twelveJ_1307 : Nat.Prime 1307 := by norm_num
private theorem prime_twelveJ_205253 : Nat.Prime 205253 := by norm_num
private theorem prime_twelveJ_792993323477 : Nat.Prime 792993323477 := by
  apply lucas_primality 792993323477 (2 : ZMod 792993323477)
  · rw [← twelveJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (739, 1), (1307, 1), (205253, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (739, 1), (1307, 1), (205253, 1)] : List FactorBlock).map factorBlockValue).prod = 792993323477 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twelveJ_2
      · exact prime_twelveJ_739
      · exact prime_twelveJ_1307
      · exact prime_twelveJ_205253
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 792993323477) ^ 396496661738 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (2 : ZMod 792993323477) ^ 1073062684 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (2 : ZMod 792993323477) ^ 606727868 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (2 : ZMod 792993323477) ^ 3863492 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide

private theorem prime_twelveJ_4831901 : Nat.Prime 4831901 := by norm_num
private theorem prime_twelveJ_1213 : Nat.Prime 1213 := by norm_num
private theorem prime_twelveJ_14797 : Nat.Prime 14797 := by norm_num
private theorem prime_twelveJ_4164112553 : Nat.Prime 4164112553 := by
  apply lucas_primality 4164112553 (3 : ZMod 4164112553)
  · rw [← twelveJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (29, 1), (1213, 1), (14797, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (29, 1), (1213, 1), (14797, 1)] : List FactorBlock).map factorBlockValue).prod = 4164112553 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twelveJ_2
      · exact prime_twelveJ_29
      · exact prime_twelveJ_1213
      · exact prime_twelveJ_14797
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 4164112553) ^ 2082056276 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (3 : ZMod 4164112553) ^ 143590088 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (3 : ZMod 4164112553) ^ 3432904 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (3 : ZMod 4164112553) ^ 281416 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide

private theorem prime_twelveJ_43049 : Nat.Prime 43049 := by norm_num
private theorem prime_twelveJ_12820164397 : Nat.Prime 12820164397 := by
  apply lucas_primality 12820164397 (7 : ZMod 12820164397)
  · rw [← twelveJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (13, 1), (23, 1), (83, 1), (43049, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (13, 1), (23, 1), (83, 1), (43049, 1)] : List FactorBlock).map factorBlockValue).prod = 12820164397 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_twelveJ_2
      · exact prime_twelveJ_3
      · exact prime_twelveJ_13
      · exact prime_twelveJ_23
      · exact prime_twelveJ_83
      · exact prime_twelveJ_43049
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 12820164397) ^ 6410082198 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (7 : ZMod 12820164397) ^ 4273388132 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (7 : ZMod 12820164397) ^ 986166492 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (7 : ZMod 12820164397) ^ 557398452 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (7 : ZMod 12820164397) ^ 154459812 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (7 : ZMod 12820164397) ^ 297804 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide

private theorem prime_twelveJ_339389 : Nat.Prime 339389 := by norm_num
private theorem prime_twelveJ_545911 : Nat.Prime 545911 := by norm_num
private theorem prime_twelveJ_2940799 : Nat.Prime 2940799 := by norm_num
private theorem prime_twelveJ_1723 : Nat.Prime 1723 := by norm_num
private theorem prime_twelveJ_464968781 : Nat.Prime 464968781 := by
  apply lucas_primality 464968781 (2 : ZMod 464968781)
  · rw [← twelveJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (5, 1), (103, 1), (131, 1), (1723, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (5, 1), (103, 1), (131, 1), (1723, 1)] : List FactorBlock).map factorBlockValue).prod = 464968781 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twelveJ_2
      · exact prime_twelveJ_5
      · exact prime_twelveJ_103
      · exact prime_twelveJ_131
      · exact prime_twelveJ_1723
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 464968781) ^ 232484390 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (2 : ZMod 464968781) ^ 92993756 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (2 : ZMod 464968781) ^ 4514260 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (2 : ZMod 464968781) ^ 3549380 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (2 : ZMod 464968781) ^ 269860 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide

private theorem prime_twelveJ_463 : Nat.Prime 463 := by norm_num
private theorem prime_twelveJ_177409 : Nat.Prime 177409 := by norm_num
private theorem prime_twelveJ_6514591 : Nat.Prime 6514591 := by norm_num
private theorem prime_twelveJ_563 : Nat.Prime 563 := by norm_num
private theorem prime_twelveJ_2903 : Nat.Prime 2903 := by norm_num
private theorem prime_twelveJ_143826233 : Nat.Prime 143826233 := by
  apply lucas_primality 143826233 (3 : ZMod 143826233)
  · rw [← twelveJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (11, 1), (563, 1), (2903, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (11, 1), (563, 1), (2903, 1)] : List FactorBlock).map factorBlockValue).prod = 143826233 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twelveJ_2
      · exact prime_twelveJ_11
      · exact prime_twelveJ_563
      · exact prime_twelveJ_2903
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 143826233) ^ 71913116 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (3 : ZMod 143826233) ^ 13075112 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (3 : ZMod 143826233) ^ 255464 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (3 : ZMod 143826233) ^ 49544 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide

private theorem prime_twelveJ_3030158014634483503 : Nat.Prime 3030158014634483503 := by
  apply lucas_primality 3030158014634483503 (3 : ZMod 3030158014634483503)
  · rw [← twelveJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (7, 2), (11, 1), (6514591, 1), (143826233, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (7, 2), (11, 1), (6514591, 1), (143826233, 1)] : List FactorBlock).map factorBlockValue).prod = 3030158014634483503 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_twelveJ_2
      · exact prime_twelveJ_3
      · exact prime_twelveJ_7
      · exact prime_twelveJ_11
      · exact prime_twelveJ_6514591
      · exact prime_twelveJ_143826233
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 3030158014634483503) ^ 1515079007317241751 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (3 : ZMod 3030158014634483503) ^ 1010052671544827834 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (3 : ZMod 3030158014634483503) ^ 432879716376354786 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (3 : ZMod 3030158014634483503) ^ 275468910421316682 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (3 : ZMod 3030158014634483503) ^ 465134037522 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (3 : ZMod 3030158014634483503) ^ 21068187294 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide

private theorem prime_twelveJ_1417679 : Nat.Prime 1417679 := by norm_num
private theorem prime_twelveJ_59553859433 : Nat.Prime 59553859433 := by
  apply lucas_primality 59553859433 (3 : ZMod 59553859433)
  · rw [← twelveJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (59, 1), (89, 1), (1417679, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (59, 1), (89, 1), (1417679, 1)] : List FactorBlock).map factorBlockValue).prod = 59553859433 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twelveJ_2
      · exact prime_twelveJ_59
      · exact prime_twelveJ_89
      · exact prime_twelveJ_1417679
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 59553859433) ^ 29776929716 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (3 : ZMod 59553859433) ^ 1009387448 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (3 : ZMod 59553859433) ^ 669144488 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (3 : ZMod 59553859433) ^ 42008 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide

private theorem prime_twelveJ_499 : Nat.Prime 499 := by norm_num
private theorem prime_twelveJ_647 : Nat.Prime 647 := by norm_num
private theorem prime_twelveJ_9521 : Nat.Prime 9521 := by norm_num
private theorem prime_twelveJ_61600871 : Nat.Prime 61600871 := by
  apply lucas_primality 61600871 (13 : ZMod 61600871)
  · rw [← twelveJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 1), (647, 1), (9521, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 1), (647, 1), (9521, 1)] : List FactorBlock).map factorBlockValue).prod = 61600871 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twelveJ_2
      · exact prime_twelveJ_5
      · exact prime_twelveJ_647
      · exact prime_twelveJ_9521
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (13 : ZMod 61600871) ^ 30800435 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (13 : ZMod 61600871) ^ 12320174 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (13 : ZMod 61600871) ^ 95210 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (13 : ZMod 61600871) ^ 6470 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide

private theorem prime_twelveJ_5225601886931 : Nat.Prime 5225601886931 := by
  apply lucas_primality 5225601886931 (2 : ZMod 5225601886931)
  · rw [← twelveJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 1), (17, 1), (499, 1), (61600871, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 1), (17, 1), (499, 1), (61600871, 1)] : List FactorBlock).map factorBlockValue).prod = 5225601886931 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twelveJ_2
      · exact prime_twelveJ_5
      · exact prime_twelveJ_17
      · exact prime_twelveJ_499
      · exact prime_twelveJ_61600871
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 5225601886931) ^ 2612800943465 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (2 : ZMod 5225601886931) ^ 1045120377386 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (2 : ZMod 5225601886931) ^ 307388346290 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (2 : ZMod 5225601886931) ^ 10472148070 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (2 : ZMod 5225601886931) ^ 84830 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide

private theorem prime_twelveJ_31353611321587 : Nat.Prime 31353611321587 := by
  apply lucas_primality 31353611321587 (2 : ZMod 31353611321587)
  · rw [← twelveJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (5225601886931, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (5225601886931, 1)] : List FactorBlock).map factorBlockValue).prod = 31353611321587 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twelveJ_2
      · exact prime_twelveJ_3
      · exact prime_twelveJ_5225601886931
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 31353611321587) ^ 15676805660793 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (2 : ZMod 31353611321587) ^ 10451203773862 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (2 : ZMod 31353611321587) ^ 6 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide

private theorem prime_twelveJ_38039 : Nat.Prime 38039 := by norm_num
private theorem prime_twelveJ_14947 : Nat.Prime 14947 := by norm_num
private theorem prime_twelveJ_9437 : Nat.Prime 9437 := by norm_num
private theorem prime_twelveJ_16363549 : Nat.Prime 16363549 := by norm_num
private theorem prime_twelveJ_65454197 : Nat.Prime 65454197 := by
  apply lucas_primality 65454197 (2 : ZMod 65454197)
  · rw [← twelveJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (16363549, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (16363549, 1)] : List FactorBlock).map factorBlockValue).prod = 65454197 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_twelveJ_2
      · exact prime_twelveJ_16363549
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 65454197) ^ 32727098 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (2 : ZMod 65454197) ^ 4 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide

private theorem prime_twelveJ_11118442627603 : Nat.Prime 11118442627603 := by
  apply lucas_primality 11118442627603 (2 : ZMod 11118442627603)
  · rw [← twelveJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 2), (9437, 1), (65454197, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 2), (9437, 1), (65454197, 1)] : List FactorBlock).map factorBlockValue).prod = 11118442627603 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twelveJ_2
      · exact prime_twelveJ_3
      · exact prime_twelveJ_9437
      · exact prime_twelveJ_65454197
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 11118442627603) ^ 5559221313801 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (2 : ZMod 11118442627603) ^ 3706147542534 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (2 : ZMod 11118442627603) ^ 1178175546 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (2 : ZMod 11118442627603) ^ 169866 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide

private theorem prime_twelveJ_6321434874035999275559 : Nat.Prime 6321434874035999275559 := by
  apply lucas_primality 6321434874035999275559 (7 : ZMod 6321434874035999275559)
  · rw [← twelveJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (7, 1), (11, 1), (13, 1), (19, 1), (14947, 1), (11118442627603, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (7, 1), (11, 1), (13, 1), (19, 1), (14947, 1), (11118442627603, 1)] : List FactorBlock).map factorBlockValue).prod = 6321434874035999275559 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_twelveJ_2
      · exact prime_twelveJ_7
      · exact prime_twelveJ_11
      · exact prime_twelveJ_13
      · exact prime_twelveJ_19
      · exact prime_twelveJ_14947
      · exact prime_twelveJ_11118442627603
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 6321434874035999275559) ^ 3160717437017999637779 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (7 : ZMod 6321434874035999275559) ^ 903062124862285610794 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (7 : ZMod 6321434874035999275559) ^ 574675897639636297778 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (7 : ZMod 6321434874035999275559) ^ 486264221079692251966 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (7 : ZMod 6321434874035999275559) ^ 332707098633473646082 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (7 : ZMod 6321434874035999275559) ^ 422923320668762914 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (7 : ZMod 6321434874035999275559) ^ 568553986 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide

private theorem prime_twelveJ_1355153 : Nat.Prime 1355153 := by norm_num
private theorem prime_twelveJ_626080687 : Nat.Prime 626080687 := by
  apply lucas_primality 626080687 (5 : ZMod 626080687)
  · rw [← twelveJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (7, 1), (11, 1), (1355153, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (7, 1), (11, 1), (1355153, 1)] : List FactorBlock).map factorBlockValue).prod = 626080687 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twelveJ_2
      · exact prime_twelveJ_3
      · exact prime_twelveJ_7
      · exact prime_twelveJ_11
      · exact prime_twelveJ_1355153
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 626080687) ^ 313040343 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (5 : ZMod 626080687) ^ 208693562 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (5 : ZMod 626080687) ^ 89440098 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (5 : ZMod 626080687) ^ 56916426 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (5 : ZMod 626080687) ^ 462 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide

private theorem prime_twelveJ_5037757 : Nat.Prime 5037757 := by norm_num
private theorem prime_twelveJ_14751743 : Nat.Prime 14751743 := by norm_num
private theorem prime_twelveJ_377672369920211983 : Nat.Prime 377672369920211983 := by
  apply lucas_primality 377672369920211983 (3 : ZMod 377672369920211983)
  · rw [← twelveJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (7, 1), (11, 2), (5037757, 1), (14751743, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (7, 1), (11, 2), (5037757, 1), (14751743, 1)] : List FactorBlock).map factorBlockValue).prod = 377672369920211983 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_twelveJ_2
      · exact prime_twelveJ_3
      · exact prime_twelveJ_7
      · exact prime_twelveJ_11
      · exact prime_twelveJ_5037757
      · exact prime_twelveJ_14751743
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 377672369920211983) ^ 188836184960105991 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (3 : ZMod 377672369920211983) ^ 125890789973403994 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (3 : ZMod 377672369920211983) ^ 53953195702887426 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (3 : ZMod 377672369920211983) ^ 34333851810928362 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (3 : ZMod 377672369920211983) ^ 74968357926 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (3 : ZMod 377672369920211983) ^ 25601881074 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide

private theorem prime_twelveJ_2437 : Nat.Prime 2437 := by norm_num
private theorem prime_twelveJ_16741 : Nat.Prime 16741 := by norm_num
private theorem prime_twelveJ_1169417 : Nat.Prime 1169417 := by norm_num
private theorem prime_twelveJ_58562064527 : Nat.Prime 58562064527 := by
  apply lucas_primality 58562064527 (5 : ZMod 58562064527)
  · rw [← twelveJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (7, 3), (73, 1), (1169417, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (7, 3), (73, 1), (1169417, 1)] : List FactorBlock).map factorBlockValue).prod = 58562064527 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twelveJ_2
      · exact prime_twelveJ_7
      · exact prime_twelveJ_73
      · exact prime_twelveJ_1169417
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 58562064527) ^ 29281032263 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (5 : ZMod 58562064527) ^ 8366009218 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (5 : ZMod 58562064527) ^ 802220062 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (5 : ZMod 58562064527) ^ 50078 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide

private theorem prime_twelveJ_95435819431536134928973 : Nat.Prime 95435819431536134928973 := by
  apply lucas_primality 95435819431536134928973 (2 : ZMod 95435819431536134928973)
  · rw [← twelveJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (7, 1), (29, 1), (89, 1), (449, 1), (16741, 1), (58562064527, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (7, 1), (29, 1), (89, 1), (449, 1), (16741, 1), (58562064527, 1)] : List FactorBlock).map factorBlockValue).prod = 95435819431536134928973 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_twelveJ_2
      · exact prime_twelveJ_3
      · exact prime_twelveJ_7
      · exact prime_twelveJ_29
      · exact prime_twelveJ_89
      · exact prime_twelveJ_449
      · exact prime_twelveJ_16741
      · exact prime_twelveJ_58562064527
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 95435819431536134928973) ^ 47717909715768067464486 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (2 : ZMod 95435819431536134928973) ^ 31811939810512044976324 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (2 : ZMod 95435819431536134928973) ^ 13633688490219447846996 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (2 : ZMod 95435819431536134928973) ^ 3290890325225383963068 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (2 : ZMod 95435819431536134928973) ^ 1072312577882428482348 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (2 : ZMod 95435819431536134928973) ^ 212551936373131703628 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (2 : ZMod 95435819431536134928973) ^ 5700723937132556892 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (2 : ZMod 95435819431536134928973) ^ 1629652578036 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide

private theorem prime_twelveJ_3449 : Nat.Prime 3449 := by norm_num
private theorem prime_twelveJ_83243 : Nat.Prime 83243 := by norm_num
private theorem prime_twelveJ_1722630643 : Nat.Prime 1722630643 := by
  apply lucas_primality 1722630643 (3 : ZMod 1722630643)
  · rw [← twelveJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (3449, 1), (83243, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (3449, 1), (83243, 1)] : List FactorBlock).map factorBlockValue).prod = 1722630643 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twelveJ_2
      · exact prime_twelveJ_3
      · exact prime_twelveJ_3449
      · exact prime_twelveJ_83243
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1722630643) ^ 861315321 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (3 : ZMod 1722630643) ^ 574210214 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (3 : ZMod 1722630643) ^ 499458 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (3 : ZMod 1722630643) ^ 20694 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide

private theorem prime_twelveJ_172263064301 : Nat.Prime 172263064301 := by
  apply lucas_primality 172263064301 (2 : ZMod 172263064301)
  · rw [← twelveJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (5, 2), (1722630643, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (5, 2), (1722630643, 1)] : List FactorBlock).map factorBlockValue).prod = 172263064301 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twelveJ_2
      · exact prime_twelveJ_5
      · exact prime_twelveJ_1722630643
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 172263064301) ^ 86131532150 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (2 : ZMod 172263064301) ^ 34452612860 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (2 : ZMod 172263064301) ^ 100 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide

private theorem prime_twelveJ_379 : Nat.Prime 379 := by norm_num
private theorem prime_twelveJ_2113 : Nat.Prime 2113 := by norm_num
private theorem prime_twelveJ_5881 : Nat.Prime 5881 := by norm_num
private theorem prime_twelveJ_198824849 : Nat.Prime 198824849 := by
  apply lucas_primality 198824849 (3 : ZMod 198824849)
  · rw [← twelveJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 4), (2113, 1), (5881, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 4), (2113, 1), (5881, 1)] : List FactorBlock).map factorBlockValue).prod = 198824849 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twelveJ_2
      · exact prime_twelveJ_2113
      · exact prime_twelveJ_5881
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 198824849) ^ 99412424 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (3 : ZMod 198824849) ^ 94096 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (3 : ZMod 198824849) ^ 33808 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide

private theorem prime_twelveJ_11755320372277 : Nat.Prime 11755320372277 := by
  apply lucas_primality 11755320372277 (6 : ZMod 11755320372277)
  · rw [← twelveJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (13, 1), (379, 1), (198824849, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (13, 1), (379, 1), (198824849, 1)] : List FactorBlock).map factorBlockValue).prod = 11755320372277 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twelveJ_2
      · exact prime_twelveJ_3
      · exact prime_twelveJ_13
      · exact prime_twelveJ_379
      · exact prime_twelveJ_198824849
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 11755320372277) ^ 5877660186138 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (6 : ZMod 11755320372277) ^ 3918440124092 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (6 : ZMod 11755320372277) ^ 904255413252 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (6 : ZMod 11755320372277) ^ 31016676444 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (6 : ZMod 11755320372277) ^ 59124 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide

private theorem prime_twelveJ_49627 : Nat.Prime 49627 := by norm_num
private theorem prime_twelveJ_55843 : Nat.Prime 55843 := by norm_num
private theorem prime_twelveJ_160736592539 : Nat.Prime 160736592539 := by
  apply lucas_primality 160736592539 (2 : ZMod 160736592539)
  · rw [← twelveJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (29, 1), (49627, 1), (55843, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (29, 1), (49627, 1), (55843, 1)] : List FactorBlock).map factorBlockValue).prod = 160736592539 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twelveJ_2
      · exact prime_twelveJ_29
      · exact prime_twelveJ_49627
      · exact prime_twelveJ_55843
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 160736592539) ^ 80368296269 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (2 : ZMod 160736592539) ^ 5542641122 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (2 : ZMod 160736592539) ^ 3238894 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (2 : ZMod 160736592539) ^ 2878366 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide

private theorem prime_twelveJ_321473185079 : Nat.Prime 321473185079 := by
  apply lucas_primality 321473185079 (7 : ZMod 321473185079)
  · rw [← twelveJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (160736592539, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (160736592539, 1)] : List FactorBlock).map factorBlockValue).prod = 321473185079 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_twelveJ_2
      · exact prime_twelveJ_160736592539
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (7 : ZMod 321473185079) ^ 160736592539 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (7 : ZMod 321473185079) ^ 2 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide

private theorem prime_twelveJ_6997 : Nat.Prime 6997 := by norm_num
private theorem prime_twelveJ_4384091 : Nat.Prime 4384091 := by norm_num
private theorem prime_twelveJ_2024581991983 : Nat.Prime 2024581991983 := by
  apply lucas_primality 2024581991983 (3 : ZMod 2024581991983)
  · rw [← twelveJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (11, 1), (6997, 1), (4384091, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (11, 1), (6997, 1), (4384091, 1)] : List FactorBlock).map factorBlockValue).prod = 2024581991983 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twelveJ_2
      · exact prime_twelveJ_3
      · exact prime_twelveJ_11
      · exact prime_twelveJ_6997
      · exact prime_twelveJ_4384091
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 2024581991983) ^ 1012290995991 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (3 : ZMod 2024581991983) ^ 674860663994 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (3 : ZMod 2024581991983) ^ 184052908362 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (3 : ZMod 2024581991983) ^ 289350006 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (3 : ZMod 2024581991983) ^ 461802 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide

private theorem prime_twelveJ_700505369226119 : Nat.Prime 700505369226119 := by
  apply lucas_primality 700505369226119 (7 : ZMod 700505369226119)
  · rw [← twelveJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (173, 1), (2024581991983, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (173, 1), (2024581991983, 1)] : List FactorBlock).map factorBlockValue).prod = 700505369226119 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twelveJ_2
      · exact prime_twelveJ_173
      · exact prime_twelveJ_2024581991983
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 700505369226119) ^ 350252684613059 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (7 : ZMod 700505369226119) ^ 4049163983966 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (7 : ZMod 700505369226119) ^ 346 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide

private theorem prime_twelveJ_197 : Nat.Prime 197 := by norm_num
private theorem prime_twelveJ_271 : Nat.Prime 271 := by norm_num
private theorem prime_twelveJ_152441 : Nat.Prime 152441 := by norm_num
private theorem prime_twelveJ_82529 : Nat.Prime 82529 := by norm_num
private theorem prime_twelveJ_1244879 : Nat.Prime 1244879 := by norm_num
private theorem prime_twelveJ_27238268144131903 : Nat.Prime 27238268144131903 := by
  apply lucas_primality 27238268144131903 (3 : ZMod 27238268144131903)
  · rw [← twelveJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 2), (11, 1), (13, 1), (103, 1), (82529, 1), (1244879, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 2), (11, 1), (13, 1), (103, 1), (82529, 1), (1244879, 1)] : List FactorBlock).map factorBlockValue).prod = 27238268144131903 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_twelveJ_2
      · exact prime_twelveJ_3
      · exact prime_twelveJ_11
      · exact prime_twelveJ_13
      · exact prime_twelveJ_103
      · exact prime_twelveJ_82529
      · exact prime_twelveJ_1244879
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 27238268144131903) ^ 13619134072065951 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (3 : ZMod 27238268144131903) ^ 9079422714710634 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (3 : ZMod 27238268144131903) ^ 2476206194921082 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (3 : ZMod 27238268144131903) ^ 2095251395702454 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (3 : ZMod 27238268144131903) ^ 264449205282834 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (3 : ZMod 27238268144131903) ^ 330044810238 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (3 : ZMod 27238268144131903) ^ 21880253538 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide

private theorem prime_twelveJ_8581 : Nat.Prime 8581 := by norm_num
private theorem prime_twelveJ_121843 : Nat.Prime 121843 := by norm_num
private theorem prime_twelveJ_96499657 : Nat.Prime 96499657 := by
  apply lucas_primality 96499657 (10 : ZMod 96499657)
  · rw [← twelveJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (3, 2), (11, 1), (121843, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (3, 2), (11, 1), (121843, 1)] : List FactorBlock).map factorBlockValue).prod = 96499657 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twelveJ_2
      · exact prime_twelveJ_3
      · exact prime_twelveJ_11
      · exact prime_twelveJ_121843
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (10 : ZMod 96499657) ^ 48249828 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (10 : ZMod 96499657) ^ 32166552 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (10 : ZMod 96499657) ^ 8772696 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (10 : ZMod 96499657) ^ 792 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide

private theorem prime_twelveJ_8722410996917 : Nat.Prime 8722410996917 := by
  apply lucas_primality 8722410996917 (2 : ZMod 8722410996917)
  · rw [← twelveJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (59, 1), (383, 1), (96499657, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (59, 1), (383, 1), (96499657, 1)] : List FactorBlock).map factorBlockValue).prod = 8722410996917 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twelveJ_2
      · exact prime_twelveJ_59
      · exact prime_twelveJ_383
      · exact prime_twelveJ_96499657
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 8722410996917) ^ 4361205498458 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (2 : ZMod 8722410996917) ^ 147837474524 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (2 : ZMod 8722410996917) ^ 22773919052 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (2 : ZMod 8722410996917) ^ 90388 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide

private theorem prime_twelveJ_1046689319630041 : Nat.Prime 1046689319630041 := by
  apply lucas_primality 1046689319630041 (7 : ZMod 1046689319630041)
  · rw [← twelveJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (3, 1), (5, 1), (8722410996917, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (3, 1), (5, 1), (8722410996917, 1)] : List FactorBlock).map factorBlockValue).prod = 1046689319630041 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twelveJ_2
      · exact prime_twelveJ_3
      · exact prime_twelveJ_5
      · exact prime_twelveJ_8722410996917
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 1046689319630041) ^ 523344659815020 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (7 : ZMod 1046689319630041) ^ 348896439876680 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (7 : ZMod 1046689319630041) ^ 209337863926008 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (7 : ZMod 1046689319630041) ^ 120 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide

private theorem prime_twelveJ_29307300949641149 : Nat.Prime 29307300949641149 := by
  apply lucas_primality 29307300949641149 (2 : ZMod 29307300949641149)
  · rw [← twelveJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (7, 1), (1046689319630041, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (7, 1), (1046689319630041, 1)] : List FactorBlock).map factorBlockValue).prod = 29307300949641149 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twelveJ_2
      · exact prime_twelveJ_7
      · exact prime_twelveJ_1046689319630041
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 29307300949641149) ^ 14653650474820574 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (2 : ZMod 29307300949641149) ^ 4186757278520164 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (2 : ZMod 29307300949641149) ^ 28 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide

private theorem prime_twelveJ_25435806494193553217101 : Nat.Prime 25435806494193553217101 := by
  apply lucas_primality 25435806494193553217101 (7 : ZMod 25435806494193553217101)
  · rw [← twelveJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (5, 2), (11, 1), (263, 1), (29307300949641149, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (5, 2), (11, 1), (263, 1), (29307300949641149, 1)] : List FactorBlock).map factorBlockValue).prod = 25435806494193553217101 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_twelveJ_2
      · exact prime_twelveJ_3
      · exact prime_twelveJ_5
      · exact prime_twelveJ_11
      · exact prime_twelveJ_263
      · exact prime_twelveJ_29307300949641149
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 25435806494193553217101) ^ 12717903247096776608550 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (7 : ZMod 25435806494193553217101) ^ 8478602164731184405700 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (7 : ZMod 25435806494193553217101) ^ 5087161298838710643420 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (7 : ZMod 25435806494193553217101) ^ 2312346044926686656100 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (7 : ZMod 25435806494193553217101) ^ 96714093133815791700 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (7 : ZMod 25435806494193553217101) ^ 867900 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide

private theorem prime_twelveJ_214957615291422230456611201 : Nat.Prime 214957615291422230456611201 := by
  apply lucas_primality 214957615291422230456611201 (11 : ZMod 214957615291422230456611201)
  · rw [← twelveJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 7), (3, 3), (5, 2), (7, 2), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 7), (3, 3), (5, 2), (7, 2), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod = 214957615291422230456611201 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_twelveJ_2
      · exact prime_twelveJ_3
      · exact prime_twelveJ_5
      · exact prime_twelveJ_7
      · exact prime_twelveJ_13
      · exact prime_twelveJ_17
      · exact prime_twelveJ_19
      · exact prime_twelveJ_23
      · exact prime_twelveJ_29
      · exact prime_twelveJ_31
      · exact prime_twelveJ_37
      · exact prime_twelveJ_41
      · exact prime_twelveJ_43
      · exact prime_twelveJ_47
      · exact prime_twelveJ_53
      · exact prime_twelveJ_59
      · exact prime_twelveJ_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 214957615291422230456611201) ^ 107478807645711115228305600 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (11 : ZMod 214957615291422230456611201) ^ 71652538430474076818870400 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (11 : ZMod 214957615291422230456611201) ^ 42991523058284446091322240 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (11 : ZMod 214957615291422230456611201) ^ 30708230755917461493801600 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (11 : ZMod 214957615291422230456611201) ^ 16535201176263248496662400 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (11 : ZMod 214957615291422230456611201) ^ 12644565605377778262153600 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (11 : ZMod 214957615291422230456611201) ^ 11313558699548538445084800 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (11 : ZMod 214957615291422230456611201) ^ 9345983273540096976374400 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (11 : ZMod 214957615291422230456611201) ^ 7412331561773180360572800 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (11 : ZMod 214957615291422230456611201) ^ 6934116622303942917955200 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (11 : ZMod 214957615291422230456611201) ^ 5809665278146546769097600 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (11 : ZMod 214957615291422230456611201) ^ 5242868665644444645283200 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (11 : ZMod 214957615291422230456611201) ^ 4999014309102842568758400 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (11 : ZMod 214957615291422230456611201) ^ 4573566282796217669289600 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (11 : ZMod 214957615291422230456611201) ^ 4055804062102306235030400 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (11 : ZMod 214957615291422230456611201) ^ 3643349411719020855196800 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (11 : ZMod 214957615291422230456611201) ^ 3523895332646266073059200 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide

private theorem prime_twelveJ_257171 : Nat.Prime 257171 := by norm_num
private theorem prime_twelveJ_62057 : Nat.Prime 62057 := by norm_num
private theorem prime_twelveJ_283 : Nat.Prime 283 := by norm_num
private theorem prime_twelveJ_751 : Nat.Prime 751 := by norm_num
private theorem prime_twelveJ_258197 : Nat.Prime 258197 := by norm_num
private theorem prime_twelveJ_1167050441 : Nat.Prime 1167050441 := by
  apply lucas_primality 1167050441 (3 : ZMod 1167050441)
  · rw [← twelveJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (5, 1), (113, 1), (258197, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (5, 1), (113, 1), (258197, 1)] : List FactorBlock).map factorBlockValue).prod = 1167050441 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twelveJ_2
      · exact prime_twelveJ_5
      · exact prime_twelveJ_113
      · exact prime_twelveJ_258197
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1167050441) ^ 583525220 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (3 : ZMod 1167050441) ^ 233410088 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (3 : ZMod 1167050441) ^ 10327880 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (3 : ZMod 1167050441) ^ 4520 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide

private theorem prime_twelveJ_55560227828459873 : Nat.Prime 55560227828459873 := by
  apply lucas_primality 55560227828459873 (6 : ZMod 55560227828459873)
  · rw [← twelveJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 5), (7, 1), (283, 1), (751, 1), (1167050441, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 5), (7, 1), (283, 1), (751, 1), (1167050441, 1)] : List FactorBlock).map factorBlockValue).prod = 55560227828459873 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twelveJ_2
      · exact prime_twelveJ_7
      · exact prime_twelveJ_283
      · exact prime_twelveJ_751
      · exact prime_twelveJ_1167050441
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 55560227828459873) ^ 27780113914229936 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (6 : ZMod 55560227828459873) ^ 7937175404065696 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (6 : ZMod 55560227828459873) ^ 196325893386784 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (6 : ZMod 55560227828459873) ^ 73981661555872 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (6 : ZMod 55560227828459873) ^ 47607392 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide

private theorem prime_twelveJ_55166416933611749420177 : Nat.Prime 55166416933611749420177 := by
  apply lucas_primality 55166416933611749420177 (3 : ZMod 55166416933611749420177)
  · rw [← twelveJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 4), (62057, 1), (55560227828459873, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 4), (62057, 1), (55560227828459873, 1)] : List FactorBlock).map factorBlockValue).prod = 55166416933611749420177 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twelveJ_2
      · exact prime_twelveJ_62057
      · exact prime_twelveJ_55560227828459873
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 55166416933611749420177) ^ 27583208466805874710088 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (3 : ZMod 55166416933611749420177) ^ 888963645255357968 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (3 : ZMod 55166416933611749420177) ^ 992912 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide

private theorem prime_twelveJ_208635332488733341325534401 : Nat.Prime 208635332488733341325534401 := by
  apply lucas_primality 208635332488733341325534401 (79 : ZMod 208635332488733341325534401)
  · rw [← twelveJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 6), (3, 4), (5, 2), (7, 2), (11, 1), (13, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 6), (3, 4), (5, 2), (7, 2), (11, 1), (13, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod = 208635332488733341325534401 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_twelveJ_2
      · exact prime_twelveJ_3
      · exact prime_twelveJ_5
      · exact prime_twelveJ_7
      · exact prime_twelveJ_11
      · exact prime_twelveJ_13
      · exact prime_twelveJ_19
      · exact prime_twelveJ_23
      · exact prime_twelveJ_29
      · exact prime_twelveJ_31
      · exact prime_twelveJ_37
      · exact prime_twelveJ_41
      · exact prime_twelveJ_43
      · exact prime_twelveJ_47
      · exact prime_twelveJ_53
      · exact prime_twelveJ_59
      · exact prime_twelveJ_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (79 : ZMod 208635332488733341325534401) ^ 104317666244366670662767200 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (79 : ZMod 208635332488733341325534401) ^ 69545110829577780441844800 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (79 : ZMod 208635332488733341325534401) ^ 41727066497746668265106880 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (79 : ZMod 208635332488733341325534401) ^ 29805047498390477332219200 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (79 : ZMod 208635332488733341325534401) ^ 18966848408066667393230400 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (79 : ZMod 208635332488733341325534401) ^ 16048871729902564717348800 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (79 : ZMod 208635332488733341325534401) ^ 10980806973091228490817600 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (79 : ZMod 208635332488733341325534401) ^ 9071101412553623535892800 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (79 : ZMod 208635332488733341325534401) ^ 7194321809956322114673600 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (79 : ZMod 208635332488733341325534401) ^ 6730172015765591655662400 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (79 : ZMod 208635332488733341325534401) ^ 5638792769965765981771200 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (79 : ZMod 208635332488733341325534401) ^ 5088666646066666861598400 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (79 : ZMod 208635332488733341325534401) ^ 4851984476482170728500800 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (79 : ZMod 208635332488733341325534401) ^ 4439049627419858326075200 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (79 : ZMod 208635332488733341325534401) ^ 3936515707334591345764800 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (79 : ZMod 208635332488733341325534401) ^ 3536192076080226124161600 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (79 : ZMod 208635332488733341325534401) ^ 3420251352274317070910400 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide

private theorem prime_twelveJ_2213 : Nat.Prime 2213 := by norm_num
private theorem prime_twelveJ_31723 : Nat.Prime 31723 := by norm_num
private theorem prime_twelveJ_244140209 : Nat.Prime 244140209 := by
  apply lucas_primality 244140209 (3 : ZMod 244140209)
  · rw [← twelveJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 4), (13, 1), (37, 1), (31723, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 4), (13, 1), (37, 1), (31723, 1)] : List FactorBlock).map factorBlockValue).prod = 244140209 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twelveJ_2
      · exact prime_twelveJ_13
      · exact prime_twelveJ_37
      · exact prime_twelveJ_31723
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 244140209) ^ 122070104 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (3 : ZMod 244140209) ^ 18780016 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (3 : ZMod 244140209) ^ 6598384 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (3 : ZMod 244140209) ^ 7696 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide

private theorem prime_twelveJ_2837 : Nat.Prime 2837 := by norm_num
private theorem prime_twelveJ_158077 : Nat.Prime 158077 := by norm_num
private theorem prime_twelveJ_5381573389 : Nat.Prime 5381573389 := by
  apply lucas_primality 5381573389 (2 : ZMod 5381573389)
  · rw [← twelveJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (2837, 1), (158077, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (2837, 1), (158077, 1)] : List FactorBlock).map factorBlockValue).prod = 5381573389 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twelveJ_2
      · exact prime_twelveJ_3
      · exact prime_twelveJ_2837
      · exact prime_twelveJ_158077
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 5381573389) ^ 2690786694 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (2 : ZMod 5381573389) ^ 1793857796 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (2 : ZMod 5381573389) ^ 1896924 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (2 : ZMod 5381573389) ^ 34044 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide

private theorem prime_twelveJ_34890825049700005681357 : Nat.Prime 34890825049700005681357 := by
  apply lucas_primality 34890825049700005681357 (2 : ZMod 34890825049700005681357)
  · rw [← twelveJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (2213, 1), (244140209, 1), (5381573389, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (2213, 1), (244140209, 1), (5381573389, 1)] : List FactorBlock).map factorBlockValue).prod = 34890825049700005681357 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twelveJ_2
      · exact prime_twelveJ_3
      · exact prime_twelveJ_2213
      · exact prime_twelveJ_244140209
      · exact prime_twelveJ_5381573389
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 34890825049700005681357) ^ 17445412524850002840678 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (2 : ZMod 34890825049700005681357) ^ 11630275016566668560452 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (2 : ZMod 34890825049700005681357) ^ 15766301423271579612 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (2 : ZMod 34890825049700005681357) ^ 142913062918284 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (2 : ZMod 34890825049700005681357) ^ 6483387390204 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide

private theorem prime_twelveJ_419 : Nat.Prime 419 := by norm_num
private theorem prime_twelveJ_10156273 : Nat.Prime 10156273 := by norm_num
private theorem prime_twelveJ_25532870323 : Nat.Prime 25532870323 := by
  apply lucas_primality 25532870323 (2 : ZMod 25532870323)
  · rw [← twelveJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (419, 1), (10156273, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (419, 1), (10156273, 1)] : List FactorBlock).map factorBlockValue).prod = 25532870323 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twelveJ_2
      · exact prime_twelveJ_3
      · exact prime_twelveJ_419
      · exact prime_twelveJ_10156273
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 25532870323) ^ 12766435161 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (2 : ZMod 25532870323) ^ 8510956774 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (2 : ZMod 25532870323) ^ 60937638 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (2 : ZMod 25532870323) ^ 2514 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide

private theorem prime_twelveJ_75037 : Nat.Prime 75037 := by norm_num
private theorem prime_twelveJ_1399271 : Nat.Prime 1399271 := by norm_num
private theorem prime_twelveJ_8819756234269 : Nat.Prime 8819756234269 := by
  apply lucas_primality 8819756234269 (2 : ZMod 8819756234269)
  · rw [← twelveJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (7, 1), (75037, 1), (1399271, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (7, 1), (75037, 1), (1399271, 1)] : List FactorBlock).map factorBlockValue).prod = 8819756234269 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twelveJ_2
      · exact prime_twelveJ_3
      · exact prime_twelveJ_7
      · exact prime_twelveJ_75037
      · exact prime_twelveJ_1399271
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 8819756234269) ^ 4409878117134 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (2 : ZMod 8819756234269) ^ 2939918744756 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (2 : ZMod 8819756234269) ^ 1259965176324 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (2 : ZMod 8819756234269) ^ 117538764 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (2 : ZMod 8819756234269) ^ 6303108 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide

private theorem prime_twelveJ_1322963435140351 : Nat.Prime 1322963435140351 := by
  apply lucas_primality 1322963435140351 (6 : ZMod 1322963435140351)
  · rw [← twelveJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (5, 2), (8819756234269, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (5, 2), (8819756234269, 1)] : List FactorBlock).map factorBlockValue).prod = 1322963435140351 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twelveJ_2
      · exact prime_twelveJ_3
      · exact prime_twelveJ_5
      · exact prime_twelveJ_8819756234269
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 1322963435140351) ^ 661481717570175 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (6 : ZMod 1322963435140351) ^ 440987811713450 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (6 : ZMod 1322963435140351) ^ 264592687028070 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (6 : ZMod 1322963435140351) ^ 150 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide

private theorem prime_twelveJ_7937780610842107 : Nat.Prime 7937780610842107 := by
  apply lucas_primality 7937780610842107 (2 : ZMod 7937780610842107)
  · rw [← twelveJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (1322963435140351, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (1322963435140351, 1)] : List FactorBlock).map factorBlockValue).prod = 7937780610842107 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twelveJ_2
      · exact prime_twelveJ_3
      · exact prime_twelveJ_1322963435140351
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 7937780610842107) ^ 3968890305421053 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (2 : ZMod 7937780610842107) ^ 2645926870280702 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (2 : ZMod 7937780610842107) ^ 6 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide

private theorem prime_twelveJ_1303 : Nat.Prime 1303 := by norm_num
private theorem prime_twelveJ_5081 : Nat.Prime 5081 := by norm_num
private theorem prime_twelveJ_6983 : Nat.Prime 6983 := by norm_num
private theorem prime_twelveJ_515507 : Nat.Prime 515507 := by norm_num
private theorem prime_twelveJ_27837379 : Nat.Prime 27837379 := by
  apply lucas_primality 27837379 (3 : ZMod 27837379)
  · rw [← twelveJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 3), (515507, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 3), (515507, 1)] : List FactorBlock).map factorBlockValue).prod = 27837379 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twelveJ_2
      · exact prime_twelveJ_3
      · exact prime_twelveJ_515507
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 27837379) ^ 13918689 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (3 : ZMod 27837379) ^ 9279126 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (3 : ZMod 27837379) ^ 54 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide

private theorem prime_twelveJ_10477 : Nat.Prime 10477 := by norm_num
private theorem prime_twelveJ_38953487 : Nat.Prime 38953487 := by
  apply lucas_primality 38953487 (5 : ZMod 38953487)
  · rw [← twelveJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (11, 1), (13, 2), (10477, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (11, 1), (13, 2), (10477, 1)] : List FactorBlock).map factorBlockValue).prod = 38953487 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twelveJ_2
      · exact prime_twelveJ_11
      · exact prime_twelveJ_13
      · exact prime_twelveJ_10477
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 38953487) ^ 19476743 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (5 : ZMod 38953487) ^ 3541226 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (5 : ZMod 38953487) ^ 2996422 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (5 : ZMod 38953487) ^ 3718 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide

private theorem prime_twelveJ_45127 : Nat.Prime 45127 := by norm_num
private theorem prime_twelveJ_1823 : Nat.Prime 1823 := by norm_num
private theorem prime_twelveJ_3271 : Nat.Prime 3271 := by norm_num
private theorem prime_twelveJ_908317 : Nat.Prime 908317 := by norm_num
private theorem prime_twelveJ_118081211 : Nat.Prime 118081211 := by
  apply lucas_primality 118081211 (14 : ZMod 118081211)
  · rw [← twelveJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 1), (13, 1), (908317, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 1), (13, 1), (908317, 1)] : List FactorBlock).map factorBlockValue).prod = 118081211 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twelveJ_2
      · exact prime_twelveJ_5
      · exact prime_twelveJ_13
      · exact prime_twelveJ_908317
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (14 : ZMod 118081211) ^ 59040605 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (14 : ZMod 118081211) ^ 23616242 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (14 : ZMod 118081211) ^ 9083170 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (14 : ZMod 118081211) ^ 130 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide

private theorem prime_twelveJ_10675900157669865007 : Nat.Prime 10675900157669865007 := by
  apply lucas_primality 10675900157669865007 (10 : ZMod 10675900157669865007)
  · rw [← twelveJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (7, 1), (19, 2), (1823, 1), (3271, 1), (118081211, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (7, 1), (19, 2), (1823, 1), (3271, 1), (118081211, 1)] : List FactorBlock).map factorBlockValue).prod = 10675900157669865007 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_twelveJ_2
      · exact prime_twelveJ_3
      · exact prime_twelveJ_7
      · exact prime_twelveJ_19
      · exact prime_twelveJ_1823
      · exact prime_twelveJ_3271
      · exact prime_twelveJ_118081211
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 10675900157669865007) ^ 5337950078834932503 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (10 : ZMod 10675900157669865007) ^ 3558633385889955002 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (10 : ZMod 10675900157669865007) ^ 1525128593952837858 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (10 : ZMod 10675900157669865007) ^ 561889481982624474 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (10 : ZMod 10675900157669865007) ^ 5856226087586322 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (10 : ZMod 10675900157669865007) ^ 3263803166514786 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (10 : ZMod 10675900157669865007) ^ 90411506346 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide

private theorem prime_twelveJ_797 : Nat.Prime 797 := by norm_num
private theorem prime_twelveJ_2397591191 : Nat.Prime 2397591191 := by
  apply lucas_primality 2397591191 (7 : ZMod 2397591191)
  · rw [← twelveJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 1), (19, 1), (71, 1), (223, 1), (797, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 1), (19, 1), (71, 1), (223, 1), (797, 1)] : List FactorBlock).map factorBlockValue).prod = 2397591191 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_twelveJ_2
      · exact prime_twelveJ_5
      · exact prime_twelveJ_19
      · exact prime_twelveJ_71
      · exact prime_twelveJ_223
      · exact prime_twelveJ_797
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 2397591191) ^ 1198795595 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (7 : ZMod 2397591191) ^ 479518238 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (7 : ZMod 2397591191) ^ 126189010 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (7 : ZMod 2397591191) ^ 33768890 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (7 : ZMod 2397591191) ^ 10751530 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (7 : ZMod 2397591191) ^ 3008270 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide

private theorem prime_twelveJ_2048239 : Nat.Prime 2048239 := by norm_num
private theorem prime_twelveJ_4875119 : Nat.Prime 4875119 := by norm_num
private theorem prime_twelveJ_2525311643 : Nat.Prime 2525311643 := by
  apply lucas_primality 2525311643 (2 : ZMod 2525311643)
  · rw [← twelveJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (7, 1), (37, 1), (4875119, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (7, 1), (37, 1), (4875119, 1)] : List FactorBlock).map factorBlockValue).prod = 2525311643 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twelveJ_2
      · exact prime_twelveJ_7
      · exact prime_twelveJ_37
      · exact prime_twelveJ_4875119
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 2525311643) ^ 1262655821 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (2 : ZMod 2525311643) ^ 360758806 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (2 : ZMod 2525311643) ^ 68251666 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (2 : ZMod 2525311643) ^ 518 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide

private theorem prime_twelveJ_111113712293 : Nat.Prime 111113712293 := by
  apply lucas_primality 111113712293 (2 : ZMod 111113712293)
  · rw [← twelveJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (11, 1), (2525311643, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (11, 1), (2525311643, 1)] : List FactorBlock).map factorBlockValue).prod = 111113712293 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twelveJ_2
      · exact prime_twelveJ_11
      · exact prime_twelveJ_2525311643
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 111113712293) ^ 55556856146 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (2 : ZMod 111113712293) ^ 10101246572 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (2 : ZMod 111113712293) ^ 44 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide

private theorem prime_twelveJ_5917273412785852703 : Nat.Prime 5917273412785852703 := by
  apply lucas_primality 5917273412785852703 (5 : ZMod 5917273412785852703)
  · rw [← twelveJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (13, 1), (2048239, 1), (111113712293, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (13, 1), (2048239, 1), (111113712293, 1)] : List FactorBlock).map factorBlockValue).prod = 5917273412785852703 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twelveJ_2
      · exact prime_twelveJ_13
      · exact prime_twelveJ_2048239
      · exact prime_twelveJ_111113712293
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 5917273412785852703) ^ 2958636706392926351 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (5 : ZMod 5917273412785852703) ^ 455174877906604054 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (5 : ZMod 5917273412785852703) ^ 2888956519618 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (5 : ZMod 5917273412785852703) ^ 53254214 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide

private theorem prime_twelveJ_14939 : Nat.Prime 14939 := by norm_num
private theorem prime_twelveJ_97303 : Nat.Prime 97303 := by norm_num
private theorem prime_twelveJ_15555937 : Nat.Prime 15555937 := by norm_num
private theorem prime_twelveJ_2281 : Nat.Prime 2281 := by norm_num
private theorem prime_twelveJ_132751 : Nat.Prime 132751 := by norm_num
private theorem prime_twelveJ_8478540869 : Nat.Prime 8478540869 := by
  apply lucas_primality 8478540869 (2 : ZMod 8478540869)
  · rw [← twelveJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (7, 1), (2281, 1), (132751, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (7, 1), (2281, 1), (132751, 1)] : List FactorBlock).map factorBlockValue).prod = 8478540869 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twelveJ_2
      · exact prime_twelveJ_7
      · exact prime_twelveJ_2281
      · exact prime_twelveJ_132751
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 8478540869) ^ 4239270434 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (2 : ZMod 8478540869) ^ 1211220124 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (2 : ZMod 8478540869) ^ 3717028 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (2 : ZMod 8478540869) ^ 63868 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide

private theorem prime_twelveJ_222107 : Nat.Prime 222107 := by norm_num
private theorem prime_twelveJ_116384069 : Nat.Prime 116384069 := by
  apply lucas_primality 116384069 (2 : ZMod 116384069)
  · rw [← twelveJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (131, 1), (222107, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (131, 1), (222107, 1)] : List FactorBlock).map factorBlockValue).prod = 116384069 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twelveJ_2
      · exact prime_twelveJ_131
      · exact prime_twelveJ_222107
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 116384069) ^ 58192034 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (2 : ZMod 116384069) ^ 888428 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (2 : ZMod 116384069) ^ 524 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide

private theorem prime_twelveJ_865483 : Nat.Prime 865483 := by norm_num
private theorem prime_twelveJ_15587213 : Nat.Prime 15587213 := by norm_num
private theorem prime_twelveJ_469486855561 : Nat.Prime 469486855561 := by
  apply lucas_primality 469486855561 (7 : ZMod 469486855561)
  · rw [← twelveJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (3, 1), (5, 1), (251, 1), (15587213, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (3, 1), (5, 1), (251, 1), (15587213, 1)] : List FactorBlock).map factorBlockValue).prod = 469486855561 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twelveJ_2
      · exact prime_twelveJ_3
      · exact prime_twelveJ_5
      · exact prime_twelveJ_251
      · exact prime_twelveJ_15587213
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 469486855561) ^ 234743427780 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (7 : ZMod 469486855561) ^ 156495618520 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (7 : ZMod 469486855561) ^ 93897371112 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (7 : ZMod 469486855561) ^ 1870465560 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (7 : ZMod 469486855561) ^ 30120 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide

private theorem prime_twelveJ_1625331568846003853 : Nat.Prime 1625331568846003853 := by
  apply lucas_primality 1625331568846003853 (2 : ZMod 1625331568846003853)
  · rw [← twelveJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (865483, 1), (469486855561, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (865483, 1), (469486855561, 1)] : List FactorBlock).map factorBlockValue).prod = 1625331568846003853 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twelveJ_2
      · exact prime_twelveJ_865483
      · exact prime_twelveJ_469486855561
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 1625331568846003853) ^ 812665784423001926 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (2 : ZMod 1625331568846003853) ^ 1877947422244 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (2 : ZMod 1625331568846003853) ^ 3461932 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide

private theorem prime_twelveJ_17885311 : Nat.Prime 17885311 := by norm_num
private theorem prime_twelveJ_321935599 : Nat.Prime 321935599 := by
  apply lucas_primality 321935599 (6 : ZMod 321935599)
  · rw [← twelveJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 2), (17885311, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 2), (17885311, 1)] : List FactorBlock).map factorBlockValue).prod = 321935599 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twelveJ_2
      · exact prime_twelveJ_3
      · exact prime_twelveJ_17885311
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (6 : ZMod 321935599) ^ 160967799 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (6 : ZMod 321935599) ^ 107311866 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (6 : ZMod 321935599) ^ 18 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide

private theorem prime_twelveJ_10531 : Nat.Prime 10531 := by norm_num
private theorem prime_twelveJ_418069 : Nat.Prime 418069 := by norm_num
private theorem prime_twelveJ_7316849 : Nat.Prime 7316849 := by norm_num
private theorem prime_twelveJ_579848016567285199 : Nat.Prime 579848016567285199 := by
  apply lucas_primality 579848016567285199 (3 : ZMod 579848016567285199)
  · rw [← twelveJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 2), (10531, 1), (418069, 1), (7316849, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 2), (10531, 1), (418069, 1), (7316849, 1)] : List FactorBlock).map factorBlockValue).prod = 579848016567285199 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twelveJ_2
      · exact prime_twelveJ_3
      · exact prime_twelveJ_10531
      · exact prime_twelveJ_418069
      · exact prime_twelveJ_7316849
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 579848016567285199) ^ 289924008283642599 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (3 : ZMod 579848016567285199) ^ 193282672189095066 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (3 : ZMod 579848016567285199) ^ 55061059402458 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (3 : ZMod 579848016567285199) ^ 1386967262742 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (3 : ZMod 579848016567285199) ^ 79248323502 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide

private theorem prime_twelveJ_184249384535504768962809601 : Nat.Prime 184249384535504768962809601 := by
  apply lucas_primality 184249384535504768962809601 (33 : ZMod 184249384535504768962809601)
  · rw [← twelveJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 8), (3, 4), (5, 2), (7, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 8), (3, 4), (5, 2), (7, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod = 184249384535504768962809601 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_twelveJ_2
      · exact prime_twelveJ_3
      · exact prime_twelveJ_5
      · exact prime_twelveJ_7
      · exact prime_twelveJ_13
      · exact prime_twelveJ_17
      · exact prime_twelveJ_19
      · exact prime_twelveJ_23
      · exact prime_twelveJ_29
      · exact prime_twelveJ_31
      · exact prime_twelveJ_37
      · exact prime_twelveJ_41
      · exact prime_twelveJ_43
      · exact prime_twelveJ_47
      · exact prime_twelveJ_53
      · exact prime_twelveJ_59
      · exact prime_twelveJ_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (33 : ZMod 184249384535504768962809601) ^ 92124692267752384481404800 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (33 : ZMod 184249384535504768962809601) ^ 61416461511834922987603200 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (33 : ZMod 184249384535504768962809601) ^ 36849876907100953792561920 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (33 : ZMod 184249384535504768962809601) ^ 26321340647929252708972800 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (33 : ZMod 184249384535504768962809601) ^ 14173029579654212997139200 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (33 : ZMod 184249384535504768962809601) ^ 10838199090323809938988800 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (33 : ZMod 184249384535504768962809601) ^ 9697336028184461524358400 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (33 : ZMod 184249384535504768962809601) ^ 8010842805891511694035200 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (33 : ZMod 184249384535504768962809601) ^ 6353427052948440309062400 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (33 : ZMod 184249384535504768962809601) ^ 5943528533403379643961600 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (33 : ZMod 184249384535504768962809601) ^ 4979713095554182944940800 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (33 : ZMod 184249384535504768962809601) ^ 4493887427695238267385600 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (33 : ZMod 184249384535504768962809601) ^ 4284869407802436487507200 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (33 : ZMod 184249384535504768962809601) ^ 3920199670968186573676800 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (33 : ZMod 184249384535504768962809601) ^ 3476403481801976772883200 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (33 : ZMod 184249384535504768962809601) ^ 3122870924330589304454400 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (33 : ZMod 184249384535504768962809601) ^ 3020481713696799491193600 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide

private theorem prime_twelveJ_433 : Nat.Prime 433 := by norm_num
private theorem prime_twelveJ_4013 : Nat.Prime 4013 := by norm_num
private theorem prime_twelveJ_5717 : Nat.Prime 5717 := by norm_num
private theorem prime_twelveJ_137653927 : Nat.Prime 137653927 := by
  apply lucas_primality 137653927 (3 : ZMod 137653927)
  · rw [← twelveJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (4013, 1), (5717, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (4013, 1), (5717, 1)] : List FactorBlock).map factorBlockValue).prod = 137653927 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twelveJ_2
      · exact prime_twelveJ_3
      · exact prime_twelveJ_4013
      · exact prime_twelveJ_5717
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 137653927) ^ 68826963 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (3 : ZMod 137653927) ^ 45884642 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (3 : ZMod 137653927) ^ 34302 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (3 : ZMod 137653927) ^ 24078 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide

private theorem prime_twelveJ_4887540332063 : Nat.Prime 4887540332063 := by
  apply lucas_primality 4887540332063 (5 : ZMod 4887540332063)
  · rw [← twelveJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (41, 1), (433, 1), (137653927, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (41, 1), (433, 1), (137653927, 1)] : List FactorBlock).map factorBlockValue).prod = 4887540332063 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twelveJ_2
      · exact prime_twelveJ_41
      · exact prime_twelveJ_433
      · exact prime_twelveJ_137653927
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 4887540332063) ^ 2443770166031 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (5 : ZMod 4887540332063) ^ 119208300782 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (5 : ZMod 4887540332063) ^ 11287622014 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (5 : ZMod 4887540332063) ^ 35506 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide

private theorem prime_twelveJ_18757 : Nat.Prime 18757 := by norm_num
private theorem prime_twelveJ_24195499 : Nat.Prime 24195499 := by
  apply lucas_primality 24195499 (2 : ZMod 24195499)
  · rw [← twelveJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (43, 1), (191, 1), (491, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (43, 1), (191, 1), (491, 1)] : List FactorBlock).map factorBlockValue).prod = 24195499 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twelveJ_2
      · exact prime_twelveJ_3
      · exact prime_twelveJ_43
      · exact prime_twelveJ_191
      · exact prime_twelveJ_491
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 24195499) ^ 12097749 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (2 : ZMod 24195499) ^ 8065166 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (2 : ZMod 24195499) ^ 562686 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (2 : ZMod 24195499) ^ 126678 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (2 : ZMod 24195499) ^ 49278 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide

private theorem prime_twelveJ_37214467928927 : Nat.Prime 37214467928927 := by
  apply lucas_primality 37214467928927 (5 : ZMod 37214467928927)
  · rw [← twelveJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (41, 1), (18757, 1), (24195499, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (41, 1), (18757, 1), (24195499, 1)] : List FactorBlock).map factorBlockValue).prod = 37214467928927 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twelveJ_2
      · exact prime_twelveJ_41
      · exact prime_twelveJ_18757
      · exact prime_twelveJ_24195499
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 37214467928927) ^ 18607233964463 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (5 : ZMod 37214467928927) ^ 907669949486 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (5 : ZMod 37214467928927) ^ 1984030918 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (5 : ZMod 37214467928927) ^ 1538074 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide

private theorem prime_twelveJ_641 : Nat.Prime 641 := by norm_num
private theorem prime_twelveJ_118061 : Nat.Prime 118061 := by norm_num
private theorem prime_twelveJ_47543 : Nat.Prime 47543 := by norm_num
private theorem prime_twelveJ_12830619583 : Nat.Prime 12830619583 := by
  apply lucas_primality 12830619583 (5 : ZMod 12830619583)
  · rw [← twelveJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 2), (11, 1), (29, 1), (47, 1), (47543, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 2), (11, 1), (29, 1), (47, 1), (47543, 1)] : List FactorBlock).map factorBlockValue).prod = 12830619583 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_twelveJ_2
      · exact prime_twelveJ_3
      · exact prime_twelveJ_11
      · exact prime_twelveJ_29
      · exact prime_twelveJ_47
      · exact prime_twelveJ_47543
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 12830619583) ^ 6415309791 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (5 : ZMod 12830619583) ^ 4276873194 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (5 : ZMod 12830619583) ^ 1166419962 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (5 : ZMod 12830619583) ^ 442435158 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (5 : ZMod 12830619583) ^ 272991906 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (5 : ZMod 12830619583) ^ 269874 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide

private theorem prime_twelveJ_601 : Nat.Prime 601 := by norm_num
private theorem prime_twelveJ_35543 : Nat.Prime 35543 := by norm_num
private theorem prime_twelveJ_14611158613 : Nat.Prime 14611158613 := by
  apply lucas_primality 14611158613 (5 : ZMod 14611158613)
  · rw [← twelveJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 2), (19, 1), (601, 1), (35543, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 2), (19, 1), (601, 1), (35543, 1)] : List FactorBlock).map factorBlockValue).prod = 14611158613 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twelveJ_2
      · exact prime_twelveJ_3
      · exact prime_twelveJ_19
      · exact prime_twelveJ_601
      · exact prime_twelveJ_35543
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 14611158613) ^ 7305579306 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (5 : ZMod 14611158613) ^ 4870386204 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (5 : ZMod 14611158613) ^ 769008348 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (5 : ZMod 14611158613) ^ 24311412 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (5 : ZMod 14611158613) ^ 411084 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide

private theorem prime_twelveJ_157 : Nat.Prime 157 := by norm_num
private theorem prime_twelveJ_8179 : Nat.Prime 8179 := by norm_num
private theorem prime_twelveJ_7290853 : Nat.Prime 7290853 := by norm_num
private theorem prime_twelveJ_192263 : Nat.Prime 192263 := by norm_num
private theorem prime_twelveJ_14615833261 : Nat.Prime 14615833261 := by
  apply lucas_primality 14615833261 (6 : ZMod 14615833261)
  · rw [← twelveJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (5, 1), (7, 1), (181, 1), (192263, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (5, 1), (7, 1), (181, 1), (192263, 1)] : List FactorBlock).map factorBlockValue).prod = 14615833261 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_twelveJ_2
      · exact prime_twelveJ_3
      · exact prime_twelveJ_5
      · exact prime_twelveJ_7
      · exact prime_twelveJ_181
      · exact prime_twelveJ_192263
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 14615833261) ^ 7307916630 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (6 : ZMod 14615833261) ^ 4871944420 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (6 : ZMod 14615833261) ^ 2923166652 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (6 : ZMod 14615833261) ^ 2087976180 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (6 : ZMod 14615833261) ^ 80750460 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (6 : ZMod 14615833261) ^ 76020 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide

private theorem prime_twelveJ_175389999133 : Nat.Prime 175389999133 := by
  apply lucas_primality 175389999133 (2 : ZMod 175389999133)
  · rw [← twelveJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (14615833261, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (14615833261, 1)] : List FactorBlock).map factorBlockValue).prod = 175389999133 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twelveJ_2
      · exact prime_twelveJ_3
      · exact prime_twelveJ_14615833261
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 175389999133) ^ 87694999566 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (2 : ZMod 175389999133) ^ 58463333044 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (2 : ZMod 175389999133) ^ 12 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide

private theorem prime_twelveJ_1052339994799 : Nat.Prime 1052339994799 := by
  apply lucas_primality 1052339994799 (6 : ZMod 1052339994799)
  · rw [← twelveJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (175389999133, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (175389999133, 1)] : List FactorBlock).map factorBlockValue).prod = 1052339994799 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twelveJ_2
      · exact prime_twelveJ_3
      · exact prime_twelveJ_175389999133
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (6 : ZMod 1052339994799) ^ 526169997399 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (6 : ZMod 1052339994799) ^ 350779998266 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (6 : ZMod 1052339994799) ^ 6 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide

private theorem prime_twelveJ_138104211745804923847 : Nat.Prime 138104211745804923847 := by
  apply lucas_primality 138104211745804923847 (5 : ZMod 138104211745804923847)
  · rw [← twelveJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 2), (7290853, 1), (1052339994799, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 2), (7290853, 1), (1052339994799, 1)] : List FactorBlock).map factorBlockValue).prod = 138104211745804923847 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twelveJ_2
      · exact prime_twelveJ_3
      · exact prime_twelveJ_7290853
      · exact prime_twelveJ_1052339994799
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 138104211745804923847) ^ 69052105872902461923 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (5 : ZMod 138104211745804923847) ^ 46034737248601641282 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (5 : ZMod 138104211745804923847) ^ 18942119906382 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (5 : ZMod 138104211745804923847) ^ 131235354 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide

private theorem prime_twelveJ_29717 : Nat.Prime 29717 := by norm_num
private theorem prime_twelveJ_8761 : Nat.Prime 8761 := by norm_num
private theorem prime_twelveJ_9043 : Nat.Prime 9043 := by norm_num
private theorem prime_twelveJ_402625124287 : Nat.Prime 402625124287 := by
  apply lucas_primality 402625124287 (6 : ZMod 402625124287)
  · rw [← twelveJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (7, 1), (11, 2), (8761, 1), (9043, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (7, 1), (11, 2), (8761, 1), (9043, 1)] : List FactorBlock).map factorBlockValue).prod = 402625124287 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_twelveJ_2
      · exact prime_twelveJ_3
      · exact prime_twelveJ_7
      · exact prime_twelveJ_11
      · exact prime_twelveJ_8761
      · exact prime_twelveJ_9043
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 402625124287) ^ 201312562143 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (6 : ZMod 402625124287) ^ 134208374762 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (6 : ZMod 402625124287) ^ 57517874898 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (6 : ZMod 402625124287) ^ 36602284026 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (6 : ZMod 402625124287) ^ 45956526 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (6 : ZMod 402625124287) ^ 44523402 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide

private theorem prime_twelveJ_9663002982889 : Nat.Prime 9663002982889 := by
  apply lucas_primality 9663002982889 (41 : ZMod 9663002982889)
  · rw [← twelveJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (3, 1), (402625124287, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (3, 1), (402625124287, 1)] : List FactorBlock).map factorBlockValue).prod = 9663002982889 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twelveJ_2
      · exact prime_twelveJ_3
      · exact prime_twelveJ_402625124287
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (41 : ZMod 9663002982889) ^ 4831501491444 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (41 : ZMod 9663002982889) ^ 3221000994296 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (41 : ZMod 9663002982889) ^ 24 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide

private theorem prime_twelveJ_212586065623559 : Nat.Prime 212586065623559 := by
  apply lucas_primality 212586065623559 (11 : ZMod 212586065623559)
  · rw [← twelveJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (11, 1), (9663002982889, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (11, 1), (9663002982889, 1)] : List FactorBlock).map factorBlockValue).prod = 212586065623559 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twelveJ_2
      · exact prime_twelveJ_11
      · exact prime_twelveJ_9663002982889
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (11 : ZMod 212586065623559) ^ 106293032811779 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (11 : ZMod 212586065623559) ^ 19326005965778 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (11 : ZMod 212586065623559) ^ 22 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide

private theorem prime_twelveJ_5893954621823010734653 : Nat.Prime 5893954621823010734653 := by
  apply lucas_primality 5893954621823010734653 (5 : ZMod 5893954621823010734653)
  · rw [← twelveJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (17, 1), (19, 1), (23, 1), (311, 1), (212586065623559, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (17, 1), (19, 1), (23, 1), (311, 1), (212586065623559, 1)] : List FactorBlock).map factorBlockValue).prod = 5893954621823010734653 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_twelveJ_2
      · exact prime_twelveJ_3
      · exact prime_twelveJ_17
      · exact prime_twelveJ_19
      · exact prime_twelveJ_23
      · exact prime_twelveJ_311
      · exact prime_twelveJ_212586065623559
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 5893954621823010734653) ^ 2946977310911505367326 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (5 : ZMod 5893954621823010734653) ^ 1964651540607670244884 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (5 : ZMod 5893954621823010734653) ^ 346703213048412396156 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (5 : ZMod 5893954621823010734653) ^ 310208137990684775508 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (5 : ZMod 5893954621823010734653) ^ 256258896601000466724 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (5 : ZMod 5893954621823010734653) ^ 18951622578209037732 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (5 : ZMod 5893954621823010734653) ^ 27725028 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide

private theorem prime_twelveJ_201386659 : Nat.Prime 201386659 := by
  apply lucas_primality 201386659 (2 : ZMod 201386659)
  · rw [← twelveJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (11, 1), (17, 1), (239, 1), (751, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (11, 1), (17, 1), (239, 1), (751, 1)] : List FactorBlock).map factorBlockValue).prod = 201386659 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_twelveJ_2
      · exact prime_twelveJ_3
      · exact prime_twelveJ_11
      · exact prime_twelveJ_17
      · exact prime_twelveJ_239
      · exact prime_twelveJ_751
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 201386659) ^ 100693329 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (2 : ZMod 201386659) ^ 67128886 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (2 : ZMod 201386659) ^ 18307878 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (2 : ZMod 201386659) ^ 11846274 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (2 : ZMod 201386659) ^ 842622 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (2 : ZMod 201386659) ^ 268158 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide

private theorem prime_twelveJ_22943 : Nat.Prime 22943 := by norm_num
private theorem prime_twelveJ_2297 : Nat.Prime 2297 := by norm_num
private theorem prime_twelveJ_4027 : Nat.Prime 4027 := by norm_num
private theorem prime_twelveJ_74000153 : Nat.Prime 74000153 := by
  apply lucas_primality 74000153 (3 : ZMod 74000153)
  · rw [← twelveJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (2297, 1), (4027, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (2297, 1), (4027, 1)] : List FactorBlock).map factorBlockValue).prod = 74000153 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twelveJ_2
      · exact prime_twelveJ_2297
      · exact prime_twelveJ_4027
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 74000153) ^ 37000076 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (3 : ZMod 74000153) ^ 32216 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (3 : ZMod 74000153) ^ 18376 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide

private theorem prime_twelveJ_859116819482400139 : Nat.Prime 859116819482400139 := by
  apply lucas_primality 859116819482400139 (2 : ZMod 859116819482400139)
  · rw [← twelveJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (11, 2), (17, 1), (41, 1), (22943, 1), (74000153, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (11, 2), (17, 1), (41, 1), (22943, 1), (74000153, 1)] : List FactorBlock).map factorBlockValue).prod = 859116819482400139 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_twelveJ_2
      · exact prime_twelveJ_3
      · exact prime_twelveJ_11
      · exact prime_twelveJ_17
      · exact prime_twelveJ_41
      · exact prime_twelveJ_22943
      · exact prime_twelveJ_74000153
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 859116819482400139) ^ 429558409741200069 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (2 : ZMod 859116819482400139) ^ 286372273160800046 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (2 : ZMod 859116819482400139) ^ 78101529043854558 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (2 : ZMod 859116819482400139) ^ 50536283498964714 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (2 : ZMod 859116819482400139) ^ 20954068767863418 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (2 : ZMod 859116819482400139) ^ 37445705421366 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (2 : ZMod 859116819482400139) ^ 11609662746 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide

private theorem prime_twelveJ_1427 : Nat.Prime 1427 := by norm_num
private theorem prime_twelveJ_26177 : Nat.Prime 26177 := by norm_num
private theorem prime_twelveJ_373545791 : Nat.Prime 373545791 := by
  apply lucas_primality 373545791 (11 : ZMod 373545791)
  · rw [← twelveJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 1), (1427, 1), (26177, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 1), (1427, 1), (26177, 1)] : List FactorBlock).map factorBlockValue).prod = 373545791 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twelveJ_2
      · exact prime_twelveJ_5
      · exact prime_twelveJ_1427
      · exact prime_twelveJ_26177
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 373545791) ^ 186772895 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (11 : ZMod 373545791) ^ 74709158 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (11 : ZMod 373545791) ^ 261770 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (11 : ZMod 373545791) ^ 14270 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide

private theorem prime_twelveJ_1619 : Nat.Prime 1619 := by norm_num
private theorem prime_twelveJ_569 : Nat.Prime 569 := by norm_num
private theorem prime_twelveJ_49193569 : Nat.Prime 49193569 := by
  apply lucas_primality 49193569 (11 : ZMod 49193569)
  · rw [← twelveJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 5), (3, 4), (18979, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 5), (3, 4), (18979, 1)] : List FactorBlock).map factorBlockValue).prod = 49193569 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twelveJ_2
      · exact prime_twelveJ_3
      · exact prime_twelveJ_18979
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (11 : ZMod 49193569) ^ 24596784 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (11 : ZMod 49193569) ^ 16397856 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (11 : ZMod 49193569) ^ 2592 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide

private theorem prime_twelveJ_2519202668491 : Nat.Prime 2519202668491 := by
  apply lucas_primality 2519202668491 (2 : ZMod 2519202668491)
  · rw [← twelveJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 2), (5, 1), (569, 1), (49193569, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 2), (5, 1), (569, 1), (49193569, 1)] : List FactorBlock).map factorBlockValue).prod = 2519202668491 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twelveJ_2
      · exact prime_twelveJ_3
      · exact prime_twelveJ_5
      · exact prime_twelveJ_569
      · exact prime_twelveJ_49193569
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 2519202668491) ^ 1259601334245 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (2 : ZMod 2519202668491) ^ 839734222830 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (2 : ZMod 2519202668491) ^ 503840533698 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (2 : ZMod 2519202668491) ^ 4427421210 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (2 : ZMod 2519202668491) ^ 51210 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide

private theorem prime_twelveJ_32628712962295433 : Nat.Prime 32628712962295433 := by
  apply lucas_primality 32628712962295433 (3 : ZMod 32628712962295433)
  · rw [← twelveJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (1619, 1), (2519202668491, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (1619, 1), (2519202668491, 1)] : List FactorBlock).map factorBlockValue).prod = 32628712962295433 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twelveJ_2
      · exact prime_twelveJ_1619
      · exact prime_twelveJ_2519202668491
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 32628712962295433) ^ 16314356481147716 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (3 : ZMod 32628712962295433) ^ 20153621347928 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (3 : ZMod 32628712962295433) ^ 12952 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide

private theorem prime_twelveJ_37979821888111884013 : Nat.Prime 37979821888111884013 := by
  apply lucas_primality 37979821888111884013 (2 : ZMod 37979821888111884013)
  · rw [← twelveJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (97, 1), (32628712962295433, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (97, 1), (32628712962295433, 1)] : List FactorBlock).map factorBlockValue).prod = 37979821888111884013 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twelveJ_2
      · exact prime_twelveJ_3
      · exact prime_twelveJ_97
      · exact prime_twelveJ_32628712962295433
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 37979821888111884013) ^ 18989910944055942006 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (2 : ZMod 37979821888111884013) ^ 12659940629370628004 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (2 : ZMod 37979821888111884013) ^ 391544555547545196 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (2 : ZMod 37979821888111884013) ^ 1164 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide

private theorem prime_twelveJ_461 : Nat.Prime 461 := by norm_num
private theorem prime_twelveJ_13492702567 : Nat.Prime 13492702567 := by
  apply lucas_primality 13492702567 (3 : ZMod 13492702567)
  · rw [← twelveJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 2), (7, 1), (23, 2), (47, 1), (59, 1), (73, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 2), (7, 1), (23, 2), (47, 1), (59, 1), (73, 1)] : List FactorBlock).map factorBlockValue).prod = 13492702567 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_twelveJ_2
      · exact prime_twelveJ_3
      · exact prime_twelveJ_7
      · exact prime_twelveJ_23
      · exact prime_twelveJ_47
      · exact prime_twelveJ_59
      · exact prime_twelveJ_73
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 13492702567) ^ 6746351283 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (3 : ZMod 13492702567) ^ 4497567522 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (3 : ZMod 13492702567) ^ 1927528938 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (3 : ZMod 13492702567) ^ 586639242 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (3 : ZMod 13492702567) ^ 287078778 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (3 : ZMod 13492702567) ^ 228689874 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (3 : ZMod 13492702567) ^ 184831542 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide

private theorem prime_twelveJ_34361 : Nat.Prime 34361 := by norm_num
private theorem prime_twelveJ_98729 : Nat.Prime 98729 := by norm_num
private theorem prime_twelveJ_590282327407 : Nat.Prime 590282327407 := by
  apply lucas_primality 590282327407 (3 : ZMod 590282327407)
  · rw [← twelveJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (29, 1), (34361, 1), (98729, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (29, 1), (34361, 1), (98729, 1)] : List FactorBlock).map factorBlockValue).prod = 590282327407 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twelveJ_2
      · exact prime_twelveJ_3
      · exact prime_twelveJ_29
      · exact prime_twelveJ_34361
      · exact prime_twelveJ_98729
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 590282327407) ^ 295141163703 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (3 : ZMod 590282327407) ^ 196760775802 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (3 : ZMod 590282327407) ^ 20354563014 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (3 : ZMod 590282327407) ^ 17178846 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (3 : ZMod 590282327407) ^ 5978814 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide

private theorem prime_twelveJ_27152987060723 : Nat.Prime 27152987060723 := by
  apply lucas_primality 27152987060723 (2 : ZMod 27152987060723)
  · rw [← twelveJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (23, 1), (590282327407, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (23, 1), (590282327407, 1)] : List FactorBlock).map factorBlockValue).prod = 27152987060723 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twelveJ_2
      · exact prime_twelveJ_23
      · exact prime_twelveJ_590282327407
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 27152987060723) ^ 13576493530361 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (2 : ZMod 27152987060723) ^ 1180564654814 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (2 : ZMod 27152987060723) ^ 46 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide

private theorem prime_twelveJ_10831 : Nat.Prime 10831 := by norm_num
private theorem prime_twelveJ_38303 : Nat.Prime 38303 := by norm_num
private theorem prime_twelveJ_513643231 : Nat.Prime 513643231 := by
  apply lucas_primality 513643231 (3 : ZMod 513643231)
  · rw [← twelveJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 2), (5, 1), (149, 1), (38303, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 2), (5, 1), (149, 1), (38303, 1)] : List FactorBlock).map factorBlockValue).prod = 513643231 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twelveJ_2
      · exact prime_twelveJ_3
      · exact prime_twelveJ_5
      · exact prime_twelveJ_149
      · exact prime_twelveJ_38303
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 513643231) ^ 256821615 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (3 : ZMod 513643231) ^ 171214410 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (3 : ZMod 513643231) ^ 102728646 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (3 : ZMod 513643231) ^ 3447270 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (3 : ZMod 513643231) ^ 13410 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide

private theorem prime_twelveJ_6430433 : Nat.Prime 6430433 := by norm_num
private theorem prime_twelveJ_1157477941 : Nat.Prime 1157477941 := by
  apply lucas_primality 1157477941 (2 : ZMod 1157477941)
  · rw [← twelveJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 2), (5, 1), (6430433, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 2), (5, 1), (6430433, 1)] : List FactorBlock).map factorBlockValue).prod = 1157477941 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twelveJ_2
      · exact prime_twelveJ_3
      · exact prime_twelveJ_5
      · exact prime_twelveJ_6430433
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1157477941) ^ 578738970 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (2 : ZMod 1157477941) ^ 385825980 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (2 : ZMod 1157477941) ^ 231495588 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (2 : ZMod 1157477941) ^ 180 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide

private theorem prime_twelveJ_125007617629 : Nat.Prime 125007617629 := by
  apply lucas_primality 125007617629 (2 : ZMod 125007617629)
  · rw [← twelveJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 3), (1157477941, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 3), (1157477941, 1)] : List FactorBlock).map factorBlockValue).prod = 125007617629 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twelveJ_2
      · exact prime_twelveJ_3
      · exact prime_twelveJ_1157477941
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 125007617629) ^ 62503808814 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (2 : ZMod 125007617629) ^ 41669205876 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (2 : ZMod 125007617629) ^ 108 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide

private theorem prime_twelveJ_30001828230961 : Nat.Prime 30001828230961 := by
  apply lucas_primality 30001828230961 (14 : ZMod 30001828230961)
  · rw [← twelveJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 4), (3, 1), (5, 1), (125007617629, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 4), (3, 1), (5, 1), (125007617629, 1)] : List FactorBlock).map factorBlockValue).prod = 30001828230961 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twelveJ_2
      · exact prime_twelveJ_3
      · exact prime_twelveJ_5
      · exact prime_twelveJ_125007617629
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (14 : ZMod 30001828230961) ^ 15000914115480 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (14 : ZMod 30001828230961) ^ 10000609410320 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (14 : ZMod 30001828230961) ^ 6000365646192 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (14 : ZMod 30001828230961) ^ 240 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide

private theorem prime_twelveJ_4733 : Nat.Prime 4733 := by norm_num
private theorem prime_twelveJ_455527 : Nat.Prime 455527 := by norm_num
private theorem prime_twelveJ_40086377 : Nat.Prime 40086377 := by
  apply lucas_primality 40086377 (3 : ZMod 40086377)
  · rw [← twelveJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (11, 1), (455527, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (11, 1), (455527, 1)] : List FactorBlock).map factorBlockValue).prod = 40086377 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twelveJ_2
      · exact prime_twelveJ_11
      · exact prime_twelveJ_455527
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 40086377) ^ 20043188 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (3 : ZMod 40086377) ^ 3644216 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (3 : ZMod 40086377) ^ 88 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide

private theorem prime_twelveJ_14166409 : Nat.Prime 14166409 := by norm_num
private theorem prime_twelveJ_869490835208461 : Nat.Prime 869490835208461 := by
  apply lucas_primality 869490835208461 (6 : ZMod 869490835208461)
  · rw [← twelveJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 5), (5, 1), (73, 1), (173, 1), (14166409, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 5), (5, 1), (73, 1), (173, 1), (14166409, 1)] : List FactorBlock).map factorBlockValue).prod = 869490835208461 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_twelveJ_2
      · exact prime_twelveJ_3
      · exact prime_twelveJ_5
      · exact prime_twelveJ_73
      · exact prime_twelveJ_173
      · exact prime_twelveJ_14166409
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 869490835208461) ^ 434745417604230 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (6 : ZMod 869490835208461) ^ 289830278402820 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (6 : ZMod 869490835208461) ^ 173898167041692 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (6 : ZMod 869490835208461) ^ 11910833359020 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (6 : ZMod 869490835208461) ^ 5025958585020 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (6 : ZMod 869490835208461) ^ 61376940 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide

private theorem prime_twelveJ_15535361 : Nat.Prime 15535361 := by norm_num
private theorem prime_twelveJ_671903 : Nat.Prime 671903 := by norm_num
private theorem prime_twelveJ_685369 : Nat.Prime 685369 := by norm_num
private theorem prime_twelveJ_28785499 : Nat.Prime 28785499 := by
  apply lucas_primality 28785499 (2 : ZMod 28785499)
  · rw [← twelveJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (7, 1), (685369, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (7, 1), (685369, 1)] : List FactorBlock).map factorBlockValue).prod = 28785499 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twelveJ_2
      · exact prime_twelveJ_3
      · exact prime_twelveJ_7
      · exact prime_twelveJ_685369
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 28785499) ^ 14392749 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (2 : ZMod 28785499) ^ 9595166 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (2 : ZMod 28785499) ^ 4112214 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (2 : ZMod 28785499) ^ 42 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide

private theorem prime_twelveJ_10496781784408483841 : Nat.Prime 10496781784408483841 := by
  apply lucas_primality 10496781784408483841 (3 : ZMod 10496781784408483841)
  · rw [← twelveJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 11), (5, 1), (53, 1), (671903, 1), (28785499, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 11), (5, 1), (53, 1), (671903, 1), (28785499, 1)] : List FactorBlock).map factorBlockValue).prod = 10496781784408483841 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twelveJ_2
      · exact prime_twelveJ_5
      · exact prime_twelveJ_53
      · exact prime_twelveJ_671903
      · exact prime_twelveJ_28785499
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 10496781784408483841) ^ 5248390892204241920 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (3 : ZMod 10496781784408483841) ^ 2099356356881696768 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (3 : ZMod 10496781784408483841) ^ 198052486498273280 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (3 : ZMod 10496781784408483841) ^ 15622466017280 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (3 : ZMod 10496781784408483841) ^ 364655196160 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide

private theorem prime_twelveJ_3823 : Nat.Prime 3823 := by norm_num
private theorem prime_twelveJ_204749 : Nat.Prime 204749 := by norm_num
private theorem prime_twelveJ_4696532563 : Nat.Prime 4696532563 := by
  apply lucas_primality 4696532563 (2 : ZMod 4696532563)
  · rw [← twelveJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (3823, 1), (204749, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (3823, 1), (204749, 1)] : List FactorBlock).map factorBlockValue).prod = 4696532563 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twelveJ_2
      · exact prime_twelveJ_3
      · exact prime_twelveJ_3823
      · exact prime_twelveJ_204749
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 4696532563) ^ 2348266281 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (2 : ZMod 4696532563) ^ 1565510854 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (2 : ZMod 4696532563) ^ 1228494 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (2 : ZMod 4696532563) ^ 22938 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide

private theorem prime_twelveJ_1933 : Nat.Prime 1933 := by norm_num
private theorem prime_twelveJ_3363887 : Nat.Prime 3363887 := by norm_num
private theorem prime_twelveJ_7776862710917 : Nat.Prime 7776862710917 := by
  apply lucas_primality 7776862710917 (2 : ZMod 7776862710917)
  · rw [← twelveJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (13, 1), (23, 1), (1933, 1), (3363887, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (13, 1), (23, 1), (1933, 1), (3363887, 1)] : List FactorBlock).map factorBlockValue).prod = 7776862710917 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twelveJ_2
      · exact prime_twelveJ_13
      · exact prime_twelveJ_23
      · exact prime_twelveJ_1933
      · exact prime_twelveJ_3363887
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 7776862710917) ^ 3888431355458 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (2 : ZMod 7776862710917) ^ 598220208532 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (2 : ZMod 7776862710917) ^ 338124465692 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (2 : ZMod 7776862710917) ^ 4023208852 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (2 : ZMod 7776862710917) ^ 2311868 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide

private theorem prime_twelveJ_73048577919604292180543 : Nat.Prime 73048577919604292180543 := by
  apply lucas_primality 73048577919604292180543 (5 : ZMod 73048577919604292180543)
  · rw [← twelveJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (4696532563, 1), (7776862710917, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (4696532563, 1), (7776862710917, 1)] : List FactorBlock).map factorBlockValue).prod = 73048577919604292180543 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twelveJ_2
      · exact prime_twelveJ_4696532563
      · exact prime_twelveJ_7776862710917
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 73048577919604292180543) ^ 36524288959802146090271 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (5 : ZMod 73048577919604292180543) ^ 15553725421834 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (5 : ZMod 73048577919604292180543) ^ 9393065126 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide

private theorem prime_twelveJ_147089 : Nat.Prime 147089 := by norm_num
private theorem prime_twelveJ_22357529 : Nat.Prime 22357529 := by
  apply lucas_primality 22357529 (3 : ZMod 22357529)
  · rw [← twelveJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (19, 1), (147089, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (19, 1), (147089, 1)] : List FactorBlock).map factorBlockValue).prod = 22357529 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twelveJ_2
      · exact prime_twelveJ_19
      · exact prime_twelveJ_147089
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 22357529) ^ 11178764 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (3 : ZMod 22357529) ^ 1176712 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (3 : ZMod 22357529) ^ 152 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide

private theorem prime_twelveJ_1453171 : Nat.Prime 1453171 := by norm_num
private theorem prime_twelveJ_7225166213 : Nat.Prime 7225166213 := by
  apply lucas_primality 7225166213 (2 : ZMod 7225166213)
  · rw [← twelveJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (11, 1), (113, 1), (1453171, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (11, 1), (113, 1), (1453171, 1)] : List FactorBlock).map factorBlockValue).prod = 7225166213 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twelveJ_2
      · exact prime_twelveJ_11
      · exact prime_twelveJ_113
      · exact prime_twelveJ_1453171
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 7225166213) ^ 3612583106 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (2 : ZMod 7225166213) ^ 656833292 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (2 : ZMod 7225166213) ^ 63939524 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (2 : ZMod 7225166213) ^ 4972 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide

private theorem prime_twelveJ_173403989113 : Nat.Prime 173403989113 := by
  apply lucas_primality 173403989113 (5 : ZMod 173403989113)
  · rw [← twelveJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (3, 1), (7225166213, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (3, 1), (7225166213, 1)] : List FactorBlock).map factorBlockValue).prod = 173403989113 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twelveJ_2
      · exact prime_twelveJ_3
      · exact prime_twelveJ_7225166213
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 173403989113) ^ 86701994556 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (5 : ZMod 173403989113) ^ 57801329704 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (5 : ZMod 173403989113) ^ 24 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide

private theorem prime_twelveJ_82006951498461660174198493 : Nat.Prime 82006951498461660174198493 := by
  apply lucas_primality 82006951498461660174198493 (13 : ZMod 82006951498461660174198493)
  · rw [← twelveJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (7, 1), (419, 1), (601, 1), (22357529, 1), (173403989113, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (7, 1), (419, 1), (601, 1), (22357529, 1), (173403989113, 1)] : List FactorBlock).map factorBlockValue).prod = 82006951498461660174198493 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_twelveJ_2
      · exact prime_twelveJ_3
      · exact prime_twelveJ_7
      · exact prime_twelveJ_419
      · exact prime_twelveJ_601
      · exact prime_twelveJ_22357529
      · exact prime_twelveJ_173403989113
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 82006951498461660174198493) ^ 41003475749230830087099246 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (13 : ZMod 82006951498461660174198493) ^ 27335650499487220058066164 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (13 : ZMod 82006951498461660174198493) ^ 11715278785494522882028356 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (13 : ZMod 82006951498461660174198493) ^ 195720647967688926430068 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (13 : ZMod 82006951498461660174198493) ^ 136450834440036040223292 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (13 : ZMod 82006951498461660174198493) ^ 3667979207293509948 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (13 : ZMod 82006951498461660174198493) ^ 472924250001084 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide

private theorem prime_twelveJ_623279 : Nat.Prime 623279 := by norm_num
private theorem prime_twelveJ_337 : Nat.Prime 337 := by norm_num
private theorem prime_twelveJ_40739 : Nat.Prime 40739 := by norm_num
private theorem prime_twelveJ_115901 : Nat.Prime 115901 := by norm_num
private theorem prime_twelveJ_132233 : Nat.Prime 132233 := by norm_num
private theorem prime_twelveJ_252913357496471033039 : Nat.Prime 252913357496471033039 := by
  apply lucas_primality 252913357496471033039 (13 : ZMod 252913357496471033039)
  · rw [← twelveJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (337, 1), (601, 1), (40739, 1), (115901, 1), (132233, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (337, 1), (601, 1), (40739, 1), (115901, 1), (132233, 1)] : List FactorBlock).map factorBlockValue).prod = 252913357496471033039 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_twelveJ_2
      · exact prime_twelveJ_337
      · exact prime_twelveJ_601
      · exact prime_twelveJ_40739
      · exact prime_twelveJ_115901
      · exact prime_twelveJ_132233
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 252913357496471033039) ^ 126456678748235516519 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (13 : ZMod 252913357496471033039) ^ 750484740345611374 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (13 : ZMod 252913357496471033039) ^ 420820894336890238 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (13 : ZMod 252913357496471033039) ^ 6208138577198042 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (13 : ZMod 252913357496471033039) ^ 2182149916708838 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (13 : ZMod 252913357496471033039) ^ 1912634194917086 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide

private theorem prime_twelveJ_3313 : Nat.Prime 3313 := by norm_num
private theorem prime_twelveJ_125813 : Nat.Prime 125813 := by norm_num
private theorem prime_twelveJ_186299 : Nat.Prime 186299 := by norm_num
private theorem prime_twelveJ_14946887 : Nat.Prime 14946887 := by norm_num
private theorem prime_twelveJ_424804701297537719260303 : Nat.Prime 424804701297537719260303 := by
  apply lucas_primality 424804701297537719260303 (3 : ZMod 424804701297537719260303)
  · rw [← twelveJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (61, 1), (3313, 1), (125813, 1), (186299, 1), (14946887, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (61, 1), (3313, 1), (125813, 1), (186299, 1), (14946887, 1)] : List FactorBlock).map factorBlockValue).prod = 424804701297537719260303 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_twelveJ_2
      · exact prime_twelveJ_3
      · exact prime_twelveJ_61
      · exact prime_twelveJ_3313
      · exact prime_twelveJ_125813
      · exact prime_twelveJ_186299
      · exact prime_twelveJ_14946887
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 424804701297537719260303) ^ 212402350648768859630151 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (3 : ZMod 424804701297537719260303) ^ 141601567099179239753434 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (3 : ZMod 424804701297537719260303) ^ 6964011496680946217382 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (3 : ZMod 424804701297537719260303) ^ 128223574191831487854 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (3 : ZMod 424804701297537719260303) ^ 3376477003946632854 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (3 : ZMod 424804701297537719260303) ^ 2280230711370097098 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (3 : ZMod 424804701297537719260303) ^ 28420948207980546 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide

private theorem prime_twelveJ_5171 : Nat.Prime 5171 := by norm_num
private theorem prime_twelveJ_979501163 : Nat.Prime 979501163 := by
  apply lucas_primality 979501163 (2 : ZMod 979501163)
  · rw [← twelveJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (53, 1), (1787, 1), (5171, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (53, 1), (1787, 1), (5171, 1)] : List FactorBlock).map factorBlockValue).prod = 979501163 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twelveJ_2
      · exact prime_twelveJ_53
      · exact prime_twelveJ_1787
      · exact prime_twelveJ_5171
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 979501163) ^ 489750581 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (2 : ZMod 979501163) ^ 18481154 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (2 : ZMod 979501163) ^ 548126 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (2 : ZMod 979501163) ^ 189422 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide

private theorem prime_twelveJ_4657 : Nat.Prime 4657 := by norm_num
private theorem prime_twelveJ_761 : Nat.Prime 761 := by norm_num
private theorem prime_twelveJ_11641387 : Nat.Prime 11641387 := by norm_num
private theorem prime_twelveJ_318927438253 : Nat.Prime 318927438253 := by
  apply lucas_primality 318927438253 (5 : ZMod 318927438253)
  · rw [← twelveJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 2), (761, 1), (11641387, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 2), (761, 1), (11641387, 1)] : List FactorBlock).map factorBlockValue).prod = 318927438253 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twelveJ_2
      · exact prime_twelveJ_3
      · exact prime_twelveJ_761
      · exact prime_twelveJ_11641387
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 318927438253) ^ 159463719126 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (5 : ZMod 318927438253) ^ 106309146084 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (5 : ZMod 318927438253) ^ 419089932 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (5 : ZMod 318927438253) ^ 27396 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide

private theorem prime_twelveJ_157435978474087427 : Nat.Prime 157435978474087427 := by
  apply lucas_primality 157435978474087427 (2 : ZMod 157435978474087427)
  · rw [← twelveJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (53, 1), (4657, 1), (318927438253, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (53, 1), (4657, 1), (318927438253, 1)] : List FactorBlock).map factorBlockValue).prod = 157435978474087427 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twelveJ_2
      · exact prime_twelveJ_53
      · exact prime_twelveJ_4657
      · exact prime_twelveJ_318927438253
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 157435978474087427) ^ 78717989237043713 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (2 : ZMod 157435978474087427) ^ 2970490159888442 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (2 : ZMod 157435978474087427) ^ 33806308454818 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (2 : ZMod 157435978474087427) ^ 493642 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide

private theorem prime_twelveJ_152550565690686744195014401 : Nat.Prime 152550565690686744195014401 := by
  apply lucas_primality 152550565690686744195014401 (113 : ZMod 152550565690686744195014401)
  · rw [← twelveJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 8), (3, 3), (5, 2), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 8), (3, 3), (5, 2), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod = 152550565690686744195014401 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_twelveJ_2
      · exact prime_twelveJ_3
      · exact prime_twelveJ_5
      · exact prime_twelveJ_7
      · exact prime_twelveJ_11
      · exact prime_twelveJ_13
      · exact prime_twelveJ_17
      · exact prime_twelveJ_19
      · exact prime_twelveJ_23
      · exact prime_twelveJ_29
      · exact prime_twelveJ_37
      · exact prime_twelveJ_41
      · exact prime_twelveJ_43
      · exact prime_twelveJ_47
      · exact prime_twelveJ_53
      · exact prime_twelveJ_59
      · exact prime_twelveJ_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (113 : ZMod 152550565690686744195014401) ^ 76275282845343372097507200 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (113 : ZMod 152550565690686744195014401) ^ 50850188563562248065004800 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (113 : ZMod 152550565690686744195014401) ^ 30510113138137348839002880 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (113 : ZMod 152550565690686744195014401) ^ 21792937955812392027859200 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (113 : ZMod 152550565690686744195014401) ^ 13868233244607885835910400 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (113 : ZMod 152550565690686744195014401) ^ 11734658899283595707308800 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (113 : ZMod 152550565690686744195014401) ^ 8973562687687455540883200 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (113 : ZMod 152550565690686744195014401) ^ 8028977141615091799737600 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (113 : ZMod 152550565690686744195014401) ^ 6632633290899423660652800 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (113 : ZMod 152550565690686744195014401) ^ 5260364334161611868793600 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (113 : ZMod 152550565690686744195014401) ^ 4122988261910452545811200 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (113 : ZMod 152550565690686744195014401) ^ 3720745504650896199878400 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (113 : ZMod 152550565690686744195014401) ^ 3547687574202017306860800 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (113 : ZMod 152550565690686744195014401) ^ 3245756716823122216915200 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (113 : ZMod 152550565690686744195014401) ^ 2878312560201636682924800 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (113 : ZMod 152550565690686744195014401) ^ 2585602808316724477881600 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (113 : ZMod 152550565690686744195014401) ^ 2500828945748963019590400 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide

private theorem prime_twelveJ_23879 : Nat.Prime 23879 := by norm_num
private theorem prime_twelveJ_9096713 : Nat.Prime 9096713 := by norm_num
private theorem prime_twelveJ_15887 : Nat.Prime 15887 := by norm_num
private theorem prime_twelveJ_58369 : Nat.Prime 58369 := by norm_num
private theorem prime_twelveJ_3115755898081 : Nat.Prime 3115755898081 := by
  apply lucas_primality 3115755898081 (13 : ZMod 3115755898081)
  · rw [← twelveJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 5), (3, 1), (5, 1), (7, 1), (15887, 1), (58369, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 5), (3, 1), (5, 1), (7, 1), (15887, 1), (58369, 1)] : List FactorBlock).map factorBlockValue).prod = 3115755898081 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_twelveJ_2
      · exact prime_twelveJ_3
      · exact prime_twelveJ_5
      · exact prime_twelveJ_7
      · exact prime_twelveJ_15887
      · exact prime_twelveJ_58369
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 3115755898081) ^ 1557877949040 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (13 : ZMod 3115755898081) ^ 1038585299360 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (13 : ZMod 3115755898081) ^ 623151179616 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (13 : ZMod 3115755898081) ^ 445107985440 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (13 : ZMod 3115755898081) ^ 196119840 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide
    · change (13 : ZMod 3115755898081) ^ 53380320 ≠ 1
      rw [← twelveJFastPow_eq_pow]
      decide

private theorem phi_twelveJ_14187202609233867210136339196 : Nat.totient 14187202609233867210136339196 = 7091792231120772871953438720 := by
  rw [← show ((([(2, 2), (3923, 1), (8197093, 1), (110295707065568641, 1)] : List FactorBlock).map factorBlockValue).prod) = 14187202609233867210136339196 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twelveJ_2, prime_twelveJ_3923, prime_twelveJ_8197093, prime_twelveJ_110295707065568641]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twelveJ_14187202609233867210136339197 : Nat.totient 14187202609233867210136339197 = 9457537686649636689178586112 := by
  rw [← show ((([(3, 1), (18713, 1), (109469, 1), (1701179, 1), (1357034643673, 1)] : List FactorBlock).map factorBlockValue).prod) = 14187202609233867210136339197 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twelveJ_3, prime_twelveJ_18713, prime_twelveJ_109469, prime_twelveJ_1701179, prime_twelveJ_1357034643673]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twelveJ_14187202609233867210136339198 : Nat.totient 14187202609233867210136339198 = 6993090232947421333663502080 := by
  rw [← show ((([(2, 1), (71, 1), (11633, 1), (8588487709947216218393, 1)] : List FactorBlock).map factorBlockValue).prod) = 14187202609233867210136339198 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twelveJ_2, prime_twelveJ_71, prime_twelveJ_11633, prime_twelveJ_8588487709947216218393]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twelveJ_14187202609233867210136339199 : Nat.totient 14187202609233867210136339199 = 14187202217963476445475459240 := by
  rw [← show ((([(36259331, 1), (391270390764624620629, 1)] : List FactorBlock).map factorBlockValue).prod) = 14187202609233867210136339199 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twelveJ_36259331, prime_twelveJ_391270390764624620629]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twelveJ_14187202609233867210136339200 : Nat.totient 14187202609233867210136339200 = 1866856421512327672627200000 := by
  rw [← show ((([(2, 8), (3, 4), (5, 2), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 14187202609233867210136339200 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twelveJ_2, prime_twelveJ_3, prime_twelveJ_5, prime_twelveJ_7, prime_twelveJ_11, prime_twelveJ_13, prime_twelveJ_17, prime_twelveJ_19, prime_twelveJ_23, prime_twelveJ_29, prime_twelveJ_31, prime_twelveJ_37, prime_twelveJ_41, prime_twelveJ_43, prime_twelveJ_47, prime_twelveJ_53, prime_twelveJ_59, prime_twelveJ_61]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twelveJ_14187202609233867210136339201 : Nat.totient 14187202609233867210136339201 = 14064312954898694022213634560 := by
  rw [← show ((([(181, 1), (317, 1), (247262885986263959602913, 1)] : List FactorBlock).map factorBlockValue).prod) = 14187202609233867210136339201 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twelveJ_181, prime_twelveJ_317, prime_twelveJ_247262885986263959602913]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twelveJ_14187202609233867210136339202 : Nat.totient 14187202609233867210136339202 = 7093540101479519638185792480 := by
  rw [← show ((([(2, 1), (115903, 1), (32244294937, 1), (1898100541591, 1)] : List FactorBlock).map factorBlockValue).prod) = 14187202609233867210136339202 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twelveJ_2, prime_twelveJ_115903, prime_twelveJ_32244294937, prime_twelveJ_1898100541591]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twelveJ_14187202609233867210136339203 : Nat.totient 14187202609233867210136339203 = 9433519265891016348115968000 := by
  rw [← show ((([(3, 1), (401, 1), (11069, 1), (53269, 1), (20000838920189041, 1)] : List FactorBlock).map factorBlockValue).prod) = 14187202609233867210136339203 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twelveJ_3, prime_twelveJ_401, prime_twelveJ_11069, prime_twelveJ_53269, prime_twelveJ_20000838920189041]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twelveJ_14187202609233867210136339204 : Nat.totient 14187202609233867210136339204 = 7093601304383813978677452200 := by
  rw [← show ((([(2, 2), (30429025931, 1), (116559782766332771, 1)] : List FactorBlock).map factorBlockValue).prod) = 14187202609233867210136339204 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twelveJ_2, prime_twelveJ_30429025931, prime_twelveJ_116559782766332771]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twelveJ_14187202609233867210136339205 : Nat.totient 14187202609233867210136339205 = 11349762087385306169741002768 := by
  rw [← show ((([(5, 1), (6442029294047, 1), (440457562723103, 1)] : List FactorBlock).map factorBlockValue).prod) = 14187202609233867210136339205 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twelveJ_5, prime_twelveJ_6442029294047, prime_twelveJ_440457562723103]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twelveJ_14187202609233867210136339206 : Nat.totient 14187202609233867210136339206 = 4729045037719437242015215104 := by
  rw [← show ((([(2, 1), (3, 1), (210193, 1), (11249345925914014905457, 1)] : List FactorBlock).map factorBlockValue).prod) = 14187202609233867210136339206 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twelveJ_2, prime_twelveJ_3, prime_twelveJ_210193, prime_twelveJ_11249345925914014905457]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twelveJ_14187202609233867210136339207 : Nat.totient 14187202609233867210136339207 = 12023739222634282607417865600 := by
  rw [← show ((([(7, 1), (109, 1), (479, 1), (8596663, 1), (20538307, 1), (219857951, 1)] : List FactorBlock).map factorBlockValue).prod) = 14187202609233867210136339207 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twelveJ_7, prime_twelveJ_109, prime_twelveJ_479, prime_twelveJ_8596663, prime_twelveJ_20538307, prime_twelveJ_219857951]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twelveJ_14187202609233867210136339208 : Nat.totient 14187202609233867210136339208 = 7092663234788967769154350080 := by
  rw [← show ((([(2, 3), (8233, 1), (93811, 1), (8274073, 1), (277508030299, 1)] : List FactorBlock).map factorBlockValue).prod) = 14187202609233867210136339208 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twelveJ_2, prime_twelveJ_8233, prime_twelveJ_93811, prime_twelveJ_8274073, prime_twelveJ_277508030299]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twelveJ_14187202609233867210136339209 : Nat.totient 14187202609233867210136339209 = 9458135072822578140090892800 := by
  rw [← show ((([(3, 2), (1576355845470429690015148801, 1)] : List FactorBlock).map factorBlockValue).prod) = 14187202609233867210136339209 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twelveJ_3, prime_twelveJ_1576355845470429690015148801]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twelveJ_14187202609233867210136339210 : Nat.totient 14187202609233867210136339210 = 5669430579905049339327700992 := by
  rw [← show ((([(2, 1), (5, 1), (1049, 1), (139537, 1), (175593973, 1), (55197867029, 1)] : List FactorBlock).map factorBlockValue).prod) = 14187202609233867210136339210 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twelveJ_2, prime_twelveJ_5, prime_twelveJ_1049, prime_twelveJ_139537, prime_twelveJ_175593973, prime_twelveJ_55197867029]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twelveJ_14187202609233867210136339211 : Nat.totient 14187202609233867210136339211 = 12897362947627791912700125000 := by
  rw [← show ((([(11, 1), (137251, 1), (9396985754191469517451, 1)] : List FactorBlock).map factorBlockValue).prod) = 14187202609233867210136339211 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twelveJ_11, prime_twelveJ_137251, prime_twelveJ_9396985754191469517451]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twelveJ_14187202609233867210136339212 : Nat.totient 14187202609233867210136339212 = 4682219311413182558003904768 := by
  rw [← show ((([(2, 2), (3, 1), (103, 1), (5009, 1), (2291539082278737626663, 1)] : List FactorBlock).map factorBlockValue).prod) = 14187202609233867210136339212 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twelveJ_2, prime_twelveJ_3, prime_twelveJ_103, prime_twelveJ_5009, prime_twelveJ_2291539082278737626663]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twelveJ_14187202609233867210136339213 : Nat.totient 14187202609233867210136339213 = 13064366850383300752330490880 := by
  rw [← show ((([(13, 1), (431, 1), (11719, 1), (1228273, 1), (9574219, 1), (18373307, 1)] : List FactorBlock).map factorBlockValue).prod) = 14187202609233867210136339213 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twelveJ_13, prime_twelveJ_431, prime_twelveJ_11719, prime_twelveJ_1228273, prime_twelveJ_9574219, prime_twelveJ_18373307]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twelveJ_14187202609233867210136339214 : Nat.totient 14187202609233867210136339214 = 6061010105625022236121773120 := by
  rw [← show ((([(2, 1), (7, 1), (331, 1), (7129, 1), (429449525106920937499, 1)] : List FactorBlock).map factorBlockValue).prod) = 14187202609233867210136339214 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twelveJ_2, prime_twelveJ_7, prime_twelveJ_331, prime_twelveJ_7129, prime_twelveJ_429449525106920937499]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twelveJ_14187202609233867210136339215 : Nat.totient 14187202609233867210136339215 = 7488393379571239139119808000 := by
  rw [← show ((([(3, 1), (5, 1), (107, 1), (1013, 1), (144417341, 1), (60421700572451, 1)] : List FactorBlock).map factorBlockValue).prod) = 14187202609233867210136339215 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twelveJ_3, prime_twelveJ_5, prime_twelveJ_107, prime_twelveJ_1013, prime_twelveJ_144417341, prime_twelveJ_60421700572451]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twelveJ_14187202609233867210136339216 : Nat.totient 14187202609233867210136339216 = 7080246641613070805070643200 := by
  rw [← show ((([(2, 4), (769, 1), (2143, 1), (8597, 1), (9792301, 1), (6391408799, 1)] : List FactorBlock).map factorBlockValue).prod) = 14187202609233867210136339216 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twelveJ_2, prime_twelveJ_769, prime_twelveJ_2143, prime_twelveJ_8597, prime_twelveJ_9792301, prime_twelveJ_6391408799]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twelveJ_14187202609233867210136339217 : Nat.totient 14187202609233867210136339217 = 13330663443608576742587343360 := by
  rw [← show ((([(17, 1), (607, 1), (324023303, 1), (4243096546919081, 1)] : List FactorBlock).map factorBlockValue).prod) = 14187202609233867210136339217 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twelveJ_17, prime_twelveJ_607, prime_twelveJ_324023303, prime_twelveJ_4243096546919081]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twelveJ_14187202609233867210136339218 : Nat.totient 14187202609233867210136339218 = 4714649187782696736432768000 := by
  rw [← show ((([(2, 1), (3, 2), (421, 1), (1483, 1), (2072201, 1), (2567179, 1), (237308333, 1)] : List FactorBlock).map factorBlockValue).prod) = 14187202609233867210136339218 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twelveJ_2, prime_twelveJ_3, prime_twelveJ_421, prime_twelveJ_1483, prime_twelveJ_2072201, prime_twelveJ_2567179, prime_twelveJ_237308333]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twelveJ_14187202609233867210136339219 : Nat.totient 14187202609233867210136339219 = 13240450668486914686476748800 := by
  rw [← show ((([(19, 2), (101, 1), (199, 1), (119737, 1), (21706837, 1), (752298509, 1)] : List FactorBlock).map factorBlockValue).prod) = 14187202609233867210136339219 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twelveJ_19, prime_twelveJ_101, prime_twelveJ_199, prime_twelveJ_119737, prime_twelveJ_21706837, prime_twelveJ_752298509]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twelveJ_14187202609233867210136339220 : Nat.totient 14187202609233867210136339220 = 5647033928394127664705157120 := by
  rw [← show ((([(2, 2), (5, 1), (281, 1), (739, 1), (3540386347, 1), (964862349257, 1)] : List FactorBlock).map factorBlockValue).prod) = 14187202609233867210136339220 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twelveJ_2, prime_twelveJ_5, prime_twelveJ_281, prime_twelveJ_739, prime_twelveJ_3540386347, prime_twelveJ_964862349257]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twelveJ_14187202609233867210136339221 : Nat.totient 14187202609233867210136339221 = 8099514802800883054387193904 := by
  rw [← show ((([(3, 1), (7, 1), (1087, 1), (621509730110564998034623, 1)] : List FactorBlock).map factorBlockValue).prod) = 14187202609233867210136339221 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twelveJ_3, prime_twelveJ_7, prime_twelveJ_1087, prime_twelveJ_621509730110564998034623]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twelveJ_14187202609233867210136339222 : Nat.totient 14187202609233867210136339222 = 6448629667797616587757691040 := by
  rw [← show ((([(2, 1), (11, 1), (97327, 1), (208223, 1), (4129087, 1), (7706514863, 1)] : List FactorBlock).map factorBlockValue).prod) = 14187202609233867210136339222 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twelveJ_2, prime_twelveJ_11, prime_twelveJ_97327, prime_twelveJ_208223, prime_twelveJ_4129087, prime_twelveJ_7706514863]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twelveJ_14187202609233867210136339223 : Nat.totient 14187202609233867210136339223 = 13515729490456587620938973184 := by
  rw [← show ((([(23, 1), (449, 1), (557, 1), (128239, 1), (73816529, 1), (260551547, 1)] : List FactorBlock).map factorBlockValue).prod) = 14187202609233867210136339223 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twelveJ_23, prime_twelveJ_449, prime_twelveJ_557, prime_twelveJ_128239, prime_twelveJ_73816529, prime_twelveJ_260551547]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twelveJ_14187202609233867210136339224 : Nat.totient 14187202609233867210136339224 = 4729067532543297963057648800 := by
  rw [← show ((([(2, 3), (3, 1), (1222615931, 1), (483498887150858771, 1)] : List FactorBlock).map factorBlockValue).prod) = 14187202609233867210136339224 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twelveJ_2, prime_twelveJ_3, prime_twelveJ_1222615931, prime_twelveJ_483498887150858771]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twelveJ_14187202609233867210136339225 : Nat.totient 14187202609233867210136339225 = 11349587821513406361671801600 := by
  rw [← show ((([(5, 2), (65129, 1), (8713293684370321798361, 1)] : List FactorBlock).map factorBlockValue).prod) = 14187202609233867210136339225 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twelveJ_5, prime_twelveJ_65129, prime_twelveJ_8713293684370321798361]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twelveJ_14187202609233867210136339226 : Nat.totient 14187202609233867210136339226 = 6547939665800246404678310400 := by
  rw [← show ((([(2, 1), (13, 1), (545661638816687200389859201, 1)] : List FactorBlock).map factorBlockValue).prod) = 14187202609233867210136339226 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twelveJ_2, prime_twelveJ_13, prime_twelveJ_545661638816687200389859201]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twelveJ_14187202609233867210136339227 : Nat.totient 14187202609233867210136339227 = 9458135072822578140090892800 := by
  rw [← show ((([(3, 3), (525451948490143230005049601, 1)] : List FactorBlock).map factorBlockValue).prod) = 14187202609233867210136339227 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twelveJ_3, prime_twelveJ_525451948490143230005049601]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twelveJ_14187202609233867210136339228 : Nat.totient 14187202609233867210136339228 = 6071866087062023771393572416 := by
  rw [← show ((([(2, 2), (7, 1), (727, 1), (40346827, 1), (17274080639688469, 1)] : List FactorBlock).map factorBlockValue).prod) = 14187202609233867210136339228 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twelveJ_2, prime_twelveJ_7, prime_twelveJ_727, prime_twelveJ_40346827, prime_twelveJ_17274080639688469]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twelveJ_14187202609233867210136339229 : Nat.totient 14187202609233867210136339229 = 13696936356894101396859977280 := by
  rw [← show ((([(29, 1), (16831, 1), (57427, 1), (506142404437043173, 1)] : List FactorBlock).map factorBlockValue).prod) = 14187202609233867210136339229 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twelveJ_29, prime_twelveJ_16831, prime_twelveJ_57427, prime_twelveJ_506142404437043173]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twelveJ_14187202609233867210136339230 : Nat.totient 14187202609233867210136339230 = 3766550734750699236795076224 := by
  rw [← show ((([(2, 1), (3, 1), (5, 1), (239, 1), (4327, 1), (1214459, 1), (376537177183483, 1)] : List FactorBlock).map factorBlockValue).prod) = 14187202609233867210136339230 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twelveJ_2, prime_twelveJ_3, prime_twelveJ_5, prime_twelveJ_239, prime_twelveJ_4327, prime_twelveJ_1214459, prime_twelveJ_376537177183483]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twelveJ_14187202609233867210136339231 : Nat.totient 14187202609233867210136339231 = 13587707080306578714386976000 := by
  rw [← show ((([(31, 1), (97, 1), (44983, 1), (104885372978717557351, 1)] : List FactorBlock).map factorBlockValue).prod) = 14187202609233867210136339231 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twelveJ_31, prime_twelveJ_97, prime_twelveJ_44983, prime_twelveJ_104885372978717557351]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twelveJ_14187202609233867210136339232 : Nat.totient 14187202609233867210136339232 = 7074401428646019176591278080 := by
  rw [← show ((([(2, 5), (373, 1), (55249, 1), (157429, 1), (773027, 1), (176780411, 1)] : List FactorBlock).map factorBlockValue).prod) = 14187202609233867210136339232 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twelveJ_2, prime_twelveJ_373, prime_twelveJ_55249, prime_twelveJ_157429, prime_twelveJ_773027, prime_twelveJ_176780411]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twelveJ_14187202609233867210136339233 : Nat.totient 14187202609233867210136339233 = 8596761758684795040349213440 := by
  rw [← show ((([(3, 1), (11, 2), (5573, 1), (3198253273, 1), (2192745608479, 1)] : List FactorBlock).map factorBlockValue).prod) = 14187202609233867210136339233 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twelveJ_3, prime_twelveJ_11, prime_twelveJ_5573, prime_twelveJ_3198253273, prime_twelveJ_2192745608479]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twelveJ_14187202609233867210136339234 : Nat.totient 14187202609233867210136339234 = 6597102979194737368650812928 := by
  rw [← show ((([(2, 1), (17, 1), (89, 1), (1567, 1), (2991981134619696139127, 1)] : List FactorBlock).map factorBlockValue).prod) = 14187202609233867210136339234 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twelveJ_2, prime_twelveJ_17, prime_twelveJ_89, prime_twelveJ_1567, prime_twelveJ_2991981134619696139127]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twelveJ_14187202609233867210136339235 : Nat.totient 14187202609233867210136339235 = 9727404584786789319616661088 := by
  rw [← show ((([(5, 1), (7, 1), (10103, 1), (40121611994270067476807, 1)] : List FactorBlock).map factorBlockValue).prod) = 14187202609233867210136339235 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twelveJ_5, prime_twelveJ_7, prime_twelveJ_10103, prime_twelveJ_40121611994270067476807]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twelveJ_14187202609233867210136339236 : Nat.totient 14187202609233867210136339236 = 4729067536411289070045446400 := by
  rw [← show ((([(2, 2), (3, 2), (394088961367607422503787201, 1)] : List FactorBlock).map factorBlockValue).prod) = 14187202609233867210136339236 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twelveJ_2, prime_twelveJ_3, prime_twelveJ_394088961367607422503787201]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twelveJ_14187202609233867210136339237 : Nat.totient 14187202609233867210136339237 = 13803763337469637436943091152 := by
  rw [← show ((([(37, 1), (10124467, 1), (37872404380168564603, 1)] : List FactorBlock).map factorBlockValue).prod) = 14187202609233867210136339237 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twelveJ_37, prime_twelveJ_10124467, prime_twelveJ_37872404380168564603]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twelveJ_14187202609233867210136339238 : Nat.totient 14187202609233867210136339238 = 6720251389869997214810758656 := by
  rw [← show ((([(2, 1), (19, 1), (2712337, 1), (137647879701195599473, 1)] : List FactorBlock).map factorBlockValue).prod) = 14187202609233867210136339238 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twelveJ_2, prime_twelveJ_19, prime_twelveJ_2712337, prime_twelveJ_137647879701195599473]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twelveJ_14187202609233867210136339239 : Nat.totient 14187202609233867210136339239 = 8695803009030871719360300000 := by
  rw [← show ((([(3, 1), (13, 1), (251, 1), (1449300501505145286560051, 1)] : List FactorBlock).map factorBlockValue).prod) = 14187202609233867210136339239 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twelveJ_3, prime_twelveJ_13, prime_twelveJ_251, prime_twelveJ_1449300501505145286560051]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twelveJ_14187202609233867210136339240 : Nat.totient 14187202609233867210136339240 = 5674849609656314391671395072 := by
  rw [← show ((([(2, 3), (5, 1), (180533, 1), (1964627327030773765757, 1)] : List FactorBlock).map factorBlockValue).prod) = 14187202609233867210136339240 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twelveJ_2, prime_twelveJ_5, prime_twelveJ_180533, prime_twelveJ_1964627327030773765757]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twelveJ_14187202609233867210136339241 : Nat.totient 14187202609233867210136339241 = 13841172438073443123926510880 := by
  rw [← show ((([(41, 1), (16492747, 1), (20980697268474035683, 1)] : List FactorBlock).map factorBlockValue).prod) = 14187202609233867210136339241 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twelveJ_41, prime_twelveJ_16492747, prime_twelveJ_20980697268474035683]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twelveJ_14187202609233867210136339242 : Nat.totient 14187202609233867210136339242 = 4053444895365943559296683504 := by
  rw [← show ((([(2, 1), (3, 1), (7, 1), (97523, 1), (3463701263446490329787, 1)] : List FactorBlock).map factorBlockValue).prod) = 14187202609233867210136339242 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twelveJ_2, prime_twelveJ_3, prime_twelveJ_7, prime_twelveJ_97523, prime_twelveJ_3463701263446490329787]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twelveJ_14187202609233867210136339243 : Nat.totient 14187202609233867210136339243 = 13857267664831061344300161504 := by
  rw [← show ((([(43, 1), (8299334176013, 1), (39754387207877, 1)] : List FactorBlock).map factorBlockValue).prod) = 14187202609233867210136339243 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twelveJ_43, prime_twelveJ_8299334176013, prime_twelveJ_39754387207877]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twelveJ_14187202609233867210136339244 : Nat.totient 14187202609233867210136339244 = 6447337744303139910336514560 := by
  rw [← show ((([(2, 2), (11, 1), (4637, 1), (2076644077, 1), (33484585780649, 1)] : List FactorBlock).map factorBlockValue).prod) = 14187202609233867210136339244 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twelveJ_2, prime_twelveJ_11, prime_twelveJ_4637, prime_twelveJ_2076644077, prime_twelveJ_33484585780649]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twelveJ_14187202609233867210136339245 : Nat.totient 14187202609233867210136339245 = 7566067659539634551088140160 := by
  rw [← show ((([(3, 2), (5, 1), (22397, 1), (73771, 1), (190813341386997503, 1)] : List FactorBlock).map factorBlockValue).prod) = 14187202609233867210136339245 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twelveJ_3, prime_twelveJ_5, prime_twelveJ_22397, prime_twelveJ_73771, prime_twelveJ_190813341386997503]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twelveJ_14187202609233867210136339246 : Nat.totient 14187202609233867210136339246 = 6777865580963869085497047552 := by
  rw [← show ((([(2, 1), (23, 2), (953, 1), (34157, 1), (485319319, 1), (848810813, 1)] : List FactorBlock).map factorBlockValue).prod) = 14187202609233867210136339246 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twelveJ_2, prime_twelveJ_23, prime_twelveJ_953, prime_twelveJ_34157, prime_twelveJ_485319319, prime_twelveJ_848810813]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twelveJ_14187202609233867210136339247 : Nat.totient 14187202609233867210136339247 = 13885269589489690999907580600 := by
  rw [← show ((([(47, 1), (178831, 1), (1687936513605305378671, 1)] : List FactorBlock).map factorBlockValue).prod) = 14187202609233867210136339247 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twelveJ_47, prime_twelveJ_178831, prime_twelveJ_1687936513605305378671]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twelveJ_14187202609233867210136339248 : Nat.totient 14187202609233867210136339248 = 4729067310472396597300764672 := by
  rw [← show ((([(2, 4), (3, 1), (20930737, 1), (14121180779525611873, 1)] : List FactorBlock).map factorBlockValue).prod) = 14187202609233867210136339248 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twelveJ_2, prime_twelveJ_3, prime_twelveJ_20930737, prime_twelveJ_14121180779525611873]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twelveJ_14187202609233867210136339249 : Nat.totient 14187202609233867210136339249 = 12160452485916259004502650880 := by
  rw [← show ((([(7, 2), (1951321, 1), (18382753, 1), (8071633250377, 1)] : List FactorBlock).map factorBlockValue).prod) = 14187202609233867210136339249 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twelveJ_7, prime_twelveJ_1951321, prime_twelveJ_18382753, prime_twelveJ_8071633250377]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twelveJ_14187202609233867210136339250 : Nat.totient 14187202609233867210136339250 = 5603035664005522105654512000 := by
  rw [← show ((([(2, 1), (5, 3), (79, 1), (489673, 1), (1466977702710658571, 1)] : List FactorBlock).map factorBlockValue).prod) = 14187202609233867210136339250 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twelveJ_2, prime_twelveJ_5, prime_twelveJ_79, prime_twelveJ_489673, prime_twelveJ_1466977702710658571]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twelveJ_14187202609233867210136339251 : Nat.totient 14187202609233867210136339251 = 8774069760182884202690641920 := by
  rw [← show ((([(3, 1), (17, 1), (73, 1), (1609, 1), (29021, 1), (2685877, 1), (30384297329, 1)] : List FactorBlock).map factorBlockValue).prod) = 14187202609233867210136339251 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twelveJ_3, prime_twelveJ_17, prime_twelveJ_73, prime_twelveJ_1609, prime_twelveJ_29021, prime_twelveJ_2685877, prime_twelveJ_30384297329]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twelveJ_14187202609233867210136339252 : Nat.totient 14187202609233867210136339252 = 6547939665800246404678310400 := by
  rw [← show ((([(2, 2), (13, 1), (272830819408343600194929601, 1)] : List FactorBlock).map factorBlockValue).prod) = 14187202609233867210136339252 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twelveJ_2, prime_twelveJ_13, prime_twelveJ_272830819408343600194929601]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twelveJ_14187202609233867210136339253 : Nat.totient 14187202609233867210136339253 = 13919499785813531650135799040 := by
  rw [← show ((([(53, 1), (712739, 1), (61671889, 1), (6089801362331, 1)] : List FactorBlock).map factorBlockValue).prod) = 14187202609233867210136339253 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twelveJ_53, prime_twelveJ_712739, prime_twelveJ_61671889, prime_twelveJ_6089801362331]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twelveJ_14187202609233867210136339254 : Nat.totient 14187202609233867210136339254 = 4644614488941132679148313600 := by
  rw [← show ((([(2, 1), (3, 3), (67, 1), (491, 1), (1061, 1), (9492089, 1), (792993323477, 1)] : List FactorBlock).map factorBlockValue).prod) = 14187202609233867210136339254 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twelveJ_2, prime_twelveJ_3, prime_twelveJ_67, prime_twelveJ_491, prime_twelveJ_1061, prime_twelveJ_9492089, prime_twelveJ_792993323477]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twelveJ_14187202609233867210136339255 : Nat.totient 14187202609233867210136339255 = 10317963395321314067467392000 := by
  rw [← show ((([(5, 1), (11, 1), (4831901, 1), (4164112553, 1), (12820164397, 1)] : List FactorBlock).map factorBlockValue).prod) = 14187202609233867210136339255 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twelveJ_5, prime_twelveJ_11, prime_twelveJ_4831901, prime_twelveJ_4164112553, prime_twelveJ_12820164397]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twelveJ_14187202609233867210136339256 : Nat.totient 14187202609233867210136339256 = 6080198556103818538901644800 := by
  rw [← show ((([(2, 3), (7, 1), (339389, 1), (545911, 1), (2940799, 1), (464968781, 1)] : List FactorBlock).map factorBlockValue).prod) = 14187202609233867210136339256 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twelveJ_2, prime_twelveJ_7, prime_twelveJ_339389, prime_twelveJ_545911, prime_twelveJ_2940799, prime_twelveJ_464968781]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twelveJ_14187202609233867210136339257 : Nat.totient 14187202609233867210136339257 = 8940935309538484637810675712 := by
  rw [← show ((([(3, 1), (19, 1), (463, 1), (177409, 1), (3030158014634483503, 1)] : List FactorBlock).map factorBlockValue).prod) = 14187202609233867210136339257 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twelveJ_3, prime_twelveJ_19, prime_twelveJ_463, prime_twelveJ_177409, prime_twelveJ_3030158014634483503]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twelveJ_14187202609233867210136339258 : Nat.totient 14187202609233867210136339258 = 6796711963245918864328913280 := by
  rw [← show ((([(2, 1), (29, 1), (131, 1), (59553859433, 1), (31353611321587, 1)] : List FactorBlock).map factorBlockValue).prod) = 14187202609233867210136339258 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twelveJ_2, prime_twelveJ_29, prime_twelveJ_131, prime_twelveJ_59553859433, prime_twelveJ_31353611321587]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twelveJ_14187202609233867210136339259 : Nat.totient 14187202609233867210136339259 = 13946374904837717745733161832 := by
  rw [← show ((([(59, 1), (38039, 1), (6321434874035999275559, 1)] : List FactorBlock).map factorBlockValue).prod) = 14187202609233867210136339259 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twelveJ_59, prime_twelveJ_38039, prime_twelveJ_6321434874035999275559]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twelveJ_14187202609233867210136339260 : Nat.totient 14187202609233867210136339260 = 3783254023086273327295674432 := by
  rw [← show ((([(2, 2), (3, 1), (5, 1), (626080687, 1), (377672369920211983, 1)] : List FactorBlock).map factorBlockValue).prod) = 14187202609233867210136339260 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twelveJ_2, prime_twelveJ_3, prime_twelveJ_5, prime_twelveJ_626080687, prime_twelveJ_377672369920211983]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twelveJ_14187202609233867210136339261 : Nat.totient 14187202609233867210136339261 = 13948899368113321481218547520 := by
  rw [← show ((([(61, 1), (2437, 1), (95435819431536134928973, 1)] : List FactorBlock).map factorBlockValue).prod) = 14187202609233867210136339261 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twelveJ_61, prime_twelveJ_2437, prime_twelveJ_95435819431536134928973]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twelveJ_14187202609233867210136339262 : Nat.totient 14187202609233867210136339262 = 6804025230765774565165248000 := by
  rw [← show ((([(2, 1), (31, 1), (113, 1), (172263064301, 1), (11755320372277, 1)] : List FactorBlock).map factorBlockValue).prod) = 14187202609233867210136339262 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twelveJ_2, prime_twelveJ_31, prime_twelveJ_113, prime_twelveJ_172263064301, prime_twelveJ_11755320372277]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twelveJ_14187202609233867210136339263 : Nat.totient 14187202609233867210136339263 = 8106972919536980068036819344 := by
  rw [← show ((([(3, 2), (7, 1), (321473185079, 1), (700505369226119, 1)] : List FactorBlock).map factorBlockValue).prod) = 14187202609233867210136339263 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twelveJ_3, prime_twelveJ_7, prime_twelveJ_321473185079, prime_twelveJ_700505369226119]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twelveJ_14187202609233867210136339264 : Nat.totient 14187202609233867210136339264 = 7031504270546446115051827200 := by
  rw [← show ((([(2, 6), (197, 1), (271, 1), (152441, 1), (27238268144131903, 1)] : List FactorBlock).map factorBlockValue).prod) = 14187202609233867210136339264 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twelveJ_2, prime_twelveJ_197, prime_twelveJ_271, prime_twelveJ_152441, prime_twelveJ_27238268144131903]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twelveJ_14187202609233867210136339265 : Nat.totient 14187202609233867210136339265 = 10475482546568672956930464000 := by
  rw [← show ((([(5, 1), (13, 1), (8581, 1), (25435806494193553217101, 1)] : List FactorBlock).map factorBlockValue).prod) = 14187202609233867210136339265 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twelveJ_5, prime_twelveJ_13, prime_twelveJ_8581, prime_twelveJ_25435806494193553217101]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twelveJ_14187202609233867210136339266 : Nat.totient 14187202609233867210136339266 = 4299152305828444609132224000 := by
  rw [← show ((([(2, 1), (3, 1), (11, 1), (214957615291422230456611201, 1)] : List FactorBlock).map factorBlockValue).prod) = 14187202609233867210136339266 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twelveJ_2, prime_twelveJ_3, prime_twelveJ_11, prime_twelveJ_214957615291422230456611201]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twelveJ_14187202609233867210136339267 : Nat.totient 14187202609233867210136339267 = 14187147442816933598386661920 := by
  rw [← show ((([(257171, 1), (55166416933611749420177, 1)] : List FactorBlock).map factorBlockValue).prod) = 14187202609233867210136339267 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twelveJ_257171, prime_twelveJ_55166416933611749420177]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twelveJ_14187202609233867210136339268 : Nat.totient 14187202609233867210136339268 = 6676330639639466922417100800 := by
  rw [← show ((([(2, 2), (17, 1), (208635332488733341325534401, 1)] : List FactorBlock).map factorBlockValue).prod) = 14187202609233867210136339268 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twelveJ_2, prime_twelveJ_17, prime_twelveJ_208635332488733341325534401]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twelveJ_14187202609233867210136339269 : Nat.totient 14187202609233867210136339269 = 8812026774552233434883271360 := by
  rw [← show ((([(3, 1), (23, 1), (71, 1), (83, 1), (34890825049700005681357, 1)] : List FactorBlock).map factorBlockValue).prod) = 14187202609233867210136339269 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twelveJ_3, prime_twelveJ_23, prime_twelveJ_71, prime_twelveJ_83, prime_twelveJ_34890825049700005681357]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twelveJ_14187202609233867210136339270 : Nat.totient 14187202609233867210136339270 = 4864183751546818553169075168 := by
  rw [← show ((([(2, 1), (5, 1), (7, 1), (25532870323, 1), (7937780610842107, 1)] : List FactorBlock).map factorBlockValue).prod) = 14187202609233867210136339270 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twelveJ_2, prime_twelveJ_5, prime_twelveJ_7, prime_twelveJ_25532870323, prime_twelveJ_7937780610842107]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twelveJ_14187202609233867210136339271 : Nat.totient 14187202609233867210136339271 = 14121417897590447651245758720 := by
  rw [← show ((([(283, 1), (1303, 1), (5081, 1), (6983, 1), (27837379, 1), (38953487, 1)] : List FactorBlock).map factorBlockValue).prod) = 14187202609233867210136339271 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twelveJ_283, prime_twelveJ_1303, prime_twelveJ_5081, prime_twelveJ_6983, prime_twelveJ_27837379, prime_twelveJ_38953487]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twelveJ_14187202609233867210136339272 : Nat.totient 14187202609233867210136339272 = 4717400485682981134329322752 := by
  rw [← show ((([(2, 3), (3, 2), (409, 1), (45127, 1), (10675900157669865007, 1)] : List FactorBlock).map factorBlockValue).prod) = 14187202609233867210136339272 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twelveJ_2, prime_twelveJ_3, prime_twelveJ_409, prime_twelveJ_45127, prime_twelveJ_10675900157669865007]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twelveJ_14187202609233867210136339273 : Nat.totient 14187202609233867210136339273 = 14187202603316593794952895380 := by
  rw [← show ((([(2397591191, 1), (5917273412785852703, 1)] : List FactorBlock).map factorBlockValue).prod) = 14187202609233867210136339273 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twelveJ_2397591191, prime_twelveJ_5917273412785852703]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twelveJ_14187202609233867210136339274 : Nat.totient 14187202609233867210136339274 = 6901348974561722563364579328 := by
  rw [← show ((([(2, 1), (37, 1), (14939, 1), (97303, 1), (15555937, 1), (8478540869, 1)] : List FactorBlock).map factorBlockValue).prod) = 14187202609233867210136339274 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twelveJ_2, prime_twelveJ_37, prime_twelveJ_14939, prime_twelveJ_97303, prime_twelveJ_15555937, prime_twelveJ_8478540869]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twelveJ_14187202609233867210136339275 : Nat.totient 14187202609233867210136339275 = 7566507993244799753577197440 := by
  rw [← show ((([(3, 1), (5, 2), (116384069, 1), (1625331568846003853, 1)] : List FactorBlock).map factorBlockValue).prod) = 14187202609233867210136339275 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twelveJ_3, prime_twelveJ_5, prime_twelveJ_116384069, prime_twelveJ_1625331568846003853]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twelveJ_14187202609233867210136339276 : Nat.totient 14187202609233867210136339276 = 6720253846657303228368422544 := by
  rw [← show ((([(2, 2), (19, 1), (321935599, 1), (579848016567285199, 1)] : List FactorBlock).map factorBlockValue).prod) = 14187202609233867210136339276 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twelveJ_2, prime_twelveJ_19, prime_twelveJ_321935599, prime_twelveJ_579848016567285199]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twelveJ_14187202609233867210136339277 : Nat.totient 14187202609233867210136339277 = 11054963072130286137768576000 := by
  rw [← show ((([(7, 1), (11, 1), (184249384535504768962809601, 1)] : List FactorBlock).map factorBlockValue).prod) = 14187202609233867210136339277 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twelveJ_7, prime_twelveJ_11, prime_twelveJ_184249384535504768962809601]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twelveJ_14187202609233867210136339278 : Nat.totient 14187202609233867210136339278 = 4365293110532487154920609888 := by
  rw [← show ((([(2, 1), (3, 1), (13, 1), (4887540332063, 1), (37214467928927, 1)] : List FactorBlock).map factorBlockValue).prod) = 14187202609233867210136339278 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twelveJ_2, prime_twelveJ_3, prime_twelveJ_13, prime_twelveJ_4887540332063, prime_twelveJ_37214467928927]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twelveJ_14187202609233867210136339279 : Nat.totient 14187202609233867210136339279 = 14164949704833738656078745600 := by
  rw [← show ((([(641, 1), (118061, 1), (12830619583, 1), (14611158613, 1)] : List FactorBlock).map factorBlockValue).prod) = 14187202609233867210136339279 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twelveJ_641, prime_twelveJ_118061, prime_twelveJ_12830619583, prime_twelveJ_14611158613]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twelveJ_14187202609233867210136339280 : Nat.totient 14187202609233867210136339280 = 5638045888336705794725239296 := by
  rw [← show ((([(2, 4), (5, 1), (157, 1), (8179, 1), (138104211745804923847, 1)] : List FactorBlock).map factorBlockValue).prod) = 14187202609233867210136339280 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twelveJ_2, prime_twelveJ_5, prime_twelveJ_157, prime_twelveJ_8179, prime_twelveJ_138104211745804923847]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twelveJ_14187202609233867210136339281 : Nat.totient 14187202609233867210136339281 = 9457816799272999697509616928 := by
  rw [← show ((([(3, 4), (29717, 1), (5893954621823010734653, 1)] : List FactorBlock).map factorBlockValue).prod) = 14187202609233867210136339281 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twelveJ_3, prime_twelveJ_29717, prime_twelveJ_5893954621823010734653]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twelveJ_14187202609233867210136339282 : Nat.totient 14187202609233867210136339282 = 6920586604285994144422352160 := by
  rw [← show ((([(2, 1), (41, 1), (201386659, 1), (859116819482400139, 1)] : List FactorBlock).map factorBlockValue).prod) = 14187202609233867210136339282 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twelveJ_2, prime_twelveJ_41, prime_twelveJ_201386659, prime_twelveJ_859116819482400139]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twelveJ_14187202609233867210136339283 : Nat.totient 14187202609233867210136339283 = 14187202571254045321650909480 := by
  rw [← show ((([(373545791, 1), (37979821888111884013, 1)] : List FactorBlock).map factorBlockValue).prod) = 14187202609233867210136339283 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twelveJ_373545791, prime_twelveJ_37979821888111884013]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twelveJ_14187202609233867210136339284 : Nat.totient 14187202609233867210136339284 = 4044693647204004540427678080 := by
  rw [← show ((([(2, 2), (3, 1), (7, 1), (461, 1), (13492702567, 1), (27152987060723, 1)] : List FactorBlock).map factorBlockValue).prod) = 14187202609233867210136339284 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twelveJ_2, prime_twelveJ_3, prime_twelveJ_7, prime_twelveJ_461, prime_twelveJ_13492702567, prime_twelveJ_27152987060723]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twelveJ_14187202609233867210136339285 : Nat.totient 14187202609233867210136339285 = 10681142747524662575402496000 := by
  rw [← show ((([(5, 1), (17, 1), (10831, 1), (513643231, 1), (30001828230961, 1)] : List FactorBlock).map factorBlockValue).prod) = 14187202609233867210136339285 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twelveJ_5, prime_twelveJ_17, prime_twelveJ_10831, prime_twelveJ_513643231, prime_twelveJ_30001828230961]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twelveJ_14187202609233867210136339286 : Nat.totient 14187202609233867210136339286 = 6927169760638880408570154240 := by
  rw [← show ((([(2, 1), (43, 1), (4733, 1), (40086377, 1), (869490835208461, 1)] : List FactorBlock).map factorBlockValue).prod) = 14187202609233867210136339286 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twelveJ_2, prime_twelveJ_43, prime_twelveJ_4733, prime_twelveJ_40086377, prime_twelveJ_869490835208461]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twelveJ_14187202609233867210136339287 : Nat.totient 14187202609233867210136339287 = 9131991896284778276480614400 := by
  rw [← show ((([(3, 1), (29, 1), (15535361, 1), (10496781784408483841, 1)] : List FactorBlock).map factorBlockValue).prod) = 14187202609233867210136339287 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twelveJ_3, prime_twelveJ_29, prime_twelveJ_15535361, prime_twelveJ_10496781784408483841]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twelveJ_14187202609233867210136339288 : Nat.totient 14187202609233867210136339288 = 6445806515625882742011026080 := by
  rw [← show ((([(2, 3), (11, 1), (2207, 1), (73048577919604292180543, 1)] : List FactorBlock).map factorBlockValue).prod) = 14187202609233867210136339288 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twelveJ_2, prime_twelveJ_11, prime_twelveJ_2207, prime_twelveJ_73048577919604292180543]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twelveJ_14187202609233867210136339289 : Nat.totient 14187202609233867210136339289 = 14105195657735405549962140624 := by
  rw [← show ((([(173, 1), (82006951498461660174198493, 1)] : List FactorBlock).map factorBlockValue).prod) = 14187202609233867210136339289 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twelveJ_173, prime_twelveJ_82006951498461660174198493]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twelveJ_14187202609233867210136339290 : Nat.totient 14187202609233867210136339290 = 3783247959208451340716605536 := by
  rw [← show ((([(2, 1), (3, 2), (5, 1), (623279, 1), (252913357496471033039, 1)] : List FactorBlock).map factorBlockValue).prod) = 14187202609233867210136339290 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twelveJ_2, prime_twelveJ_3, prime_twelveJ_5, prime_twelveJ_623279, prime_twelveJ_252913357496471033039]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twelveJ_14187202609233867210136339291 : Nat.totient 14187202609233867210136339291 = 11194453488592713977947478304 := by
  rw [← show ((([(7, 1), (13, 1), (367, 1), (424804701297537719260303, 1)] : List FactorBlock).map factorBlockValue).prod) = 14187202609233867210136339291 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twelveJ_7, prime_twelveJ_13, prime_twelveJ_367, prime_twelveJ_424804701297537719260303]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twelveJ_14187202609233867210136339292 : Nat.totient 14187202609233867210136339292 = 6785183849662927308889916528 := by
  rw [← show ((([(2, 2), (23, 1), (979501163, 1), (157435978474087427, 1)] : List FactorBlock).map factorBlockValue).prod) = 14187202609233867210136339292 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twelveJ_2, prime_twelveJ_23, prime_twelveJ_979501163, prime_twelveJ_157435978474087427]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twelveJ_14187202609233867210136339293 : Nat.totient 14187202609233867210136339293 = 9153033941441204651700864000 := by
  rw [← show ((([(3, 1), (31, 1), (152550565690686744195014401, 1)] : List FactorBlock).map factorBlockValue).prod) = 14187202609233867210136339293 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twelveJ_3, prime_twelveJ_31, prime_twelveJ_152550565690686744195014401]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twelveJ_14187202609233867210136339294 : Nat.totient 14187202609233867210136339294 = 6911250351864593344767682560 := by
  rw [← show ((([(2, 1), (47, 1), (223, 1), (23879, 1), (9096713, 1), (3115755898081, 1)] : List FactorBlock).map factorBlockValue).prod) = 14187202609233867210136339294 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twelveJ_2, prime_twelveJ_47, prime_twelveJ_223, prime_twelveJ_23879, prime_twelveJ_9096713, prime_twelveJ_3115755898081]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

theorem freeKill_64TwelveJ : certifiedKill 1 14187202609233867210136339195 98 := by
  norm_num [certifiedKill, windowDiscrepancy, Finset.sum_range_succ,
    phi_twelveJ_14187202609233867210136339196, phi_twelveJ_14187202609233867210136339197, phi_twelveJ_14187202609233867210136339198,
    phi_twelveJ_14187202609233867210136339199, phi_twelveJ_14187202609233867210136339200, phi_twelveJ_14187202609233867210136339201,
    phi_twelveJ_14187202609233867210136339202, phi_twelveJ_14187202609233867210136339203, phi_twelveJ_14187202609233867210136339204,
    phi_twelveJ_14187202609233867210136339205, phi_twelveJ_14187202609233867210136339206, phi_twelveJ_14187202609233867210136339207,
    phi_twelveJ_14187202609233867210136339208, phi_twelveJ_14187202609233867210136339209, phi_twelveJ_14187202609233867210136339210,
    phi_twelveJ_14187202609233867210136339211, phi_twelveJ_14187202609233867210136339212, phi_twelveJ_14187202609233867210136339213,
    phi_twelveJ_14187202609233867210136339214, phi_twelveJ_14187202609233867210136339215, phi_twelveJ_14187202609233867210136339216,
    phi_twelveJ_14187202609233867210136339217, phi_twelveJ_14187202609233867210136339218, phi_twelveJ_14187202609233867210136339219,
    phi_twelveJ_14187202609233867210136339220, phi_twelveJ_14187202609233867210136339221, phi_twelveJ_14187202609233867210136339222,
    phi_twelveJ_14187202609233867210136339223, phi_twelveJ_14187202609233867210136339224, phi_twelveJ_14187202609233867210136339225,
    phi_twelveJ_14187202609233867210136339226, phi_twelveJ_14187202609233867210136339227, phi_twelveJ_14187202609233867210136339228,
    phi_twelveJ_14187202609233867210136339229, phi_twelveJ_14187202609233867210136339230, phi_twelveJ_14187202609233867210136339231,
    phi_twelveJ_14187202609233867210136339232, phi_twelveJ_14187202609233867210136339233, phi_twelveJ_14187202609233867210136339234,
    phi_twelveJ_14187202609233867210136339235, phi_twelveJ_14187202609233867210136339236, phi_twelveJ_14187202609233867210136339237,
    phi_twelveJ_14187202609233867210136339238, phi_twelveJ_14187202609233867210136339239, phi_twelveJ_14187202609233867210136339240,
    phi_twelveJ_14187202609233867210136339241, phi_twelveJ_14187202609233867210136339242, phi_twelveJ_14187202609233867210136339243,
    phi_twelveJ_14187202609233867210136339244, phi_twelveJ_14187202609233867210136339245, phi_twelveJ_14187202609233867210136339246,
    phi_twelveJ_14187202609233867210136339247, phi_twelveJ_14187202609233867210136339248, phi_twelveJ_14187202609233867210136339249,
    phi_twelveJ_14187202609233867210136339250, phi_twelveJ_14187202609233867210136339251, phi_twelveJ_14187202609233867210136339252,
    phi_twelveJ_14187202609233867210136339253, phi_twelveJ_14187202609233867210136339254, phi_twelveJ_14187202609233867210136339255,
    phi_twelveJ_14187202609233867210136339256, phi_twelveJ_14187202609233867210136339257, phi_twelveJ_14187202609233867210136339258,
    phi_twelveJ_14187202609233867210136339259, phi_twelveJ_14187202609233867210136339260, phi_twelveJ_14187202609233867210136339261,
    phi_twelveJ_14187202609233867210136339262, phi_twelveJ_14187202609233867210136339263, phi_twelveJ_14187202609233867210136339264,
    phi_twelveJ_14187202609233867210136339265, phi_twelveJ_14187202609233867210136339266, phi_twelveJ_14187202609233867210136339267,
    phi_twelveJ_14187202609233867210136339268, phi_twelveJ_14187202609233867210136339269, phi_twelveJ_14187202609233867210136339270,
    phi_twelveJ_14187202609233867210136339271, phi_twelveJ_14187202609233867210136339272, phi_twelveJ_14187202609233867210136339273,
    phi_twelveJ_14187202609233867210136339274, phi_twelveJ_14187202609233867210136339275, phi_twelveJ_14187202609233867210136339276,
    phi_twelveJ_14187202609233867210136339277, phi_twelveJ_14187202609233867210136339278, phi_twelveJ_14187202609233867210136339279,
    phi_twelveJ_14187202609233867210136339280, phi_twelveJ_14187202609233867210136339281, phi_twelveJ_14187202609233867210136339282,
    phi_twelveJ_14187202609233867210136339283, phi_twelveJ_14187202609233867210136339284, phi_twelveJ_14187202609233867210136339285,
    phi_twelveJ_14187202609233867210136339286, phi_twelveJ_14187202609233867210136339287, phi_twelveJ_14187202609233867210136339288,
    phi_twelveJ_14187202609233867210136339289, phi_twelveJ_14187202609233867210136339290, phi_twelveJ_14187202609233867210136339291,
    phi_twelveJ_14187202609233867210136339292, phi_twelveJ_14187202609233867210136339293, phi_twelveJ_14187202609233867210136339294]

end TotientTailPeriodKiller
end Erdos249257
