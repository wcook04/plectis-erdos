import Erdos249257.DiagonalPincerCertificatesT64

/- Kernel-checked off-diagonal certificate at a freely chosen position. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

private def oneHundredFourCXFastPow {M : Type*} [Monoid M] (a : M) (n : ℕ) : M :=
  Nat.binaryRec 1 (fun b _ r => if b then r * r * a else r * r) n

private theorem oneHundredFourCXFastPow_eq_pow {M : Type*} [Monoid M] (a : M) (n : ℕ) : oneHundredFourCXFastPow a n = a ^ n := by
  induction n using Nat.binaryRec with
  | zero => simp [oneHundredFourCXFastPow, Nat.binaryRec_zero]
  | bit b n ih =>
      rw [oneHundredFourCXFastPow, Nat.binaryRec_eq b n (by left; simp)]
      change (if b then oneHundredFourCXFastPow a n * oneHundredFourCXFastPow a n * a else oneHundredFourCXFastPow a n * oneHundredFourCXFastPow a n) = _
      rw [ih]
      cases b <;> simp [Nat.bit, two_mul, pow_add]

private theorem prime_oneHundredFourCX_2 : Nat.Prime 2 := by norm_num

private theorem prime_oneHundredFourCX_3 : Nat.Prime 3 := by norm_num

private theorem prime_oneHundredFourCX_5 : Nat.Prime 5 := by norm_num

private theorem prime_oneHundredFourCX_7 : Nat.Prime 7 := by norm_num

private theorem prime_oneHundredFourCX_11 : Nat.Prime 11 := by norm_num

private theorem prime_oneHundredFourCX_13 : Nat.Prime 13 := by norm_num

private theorem prime_oneHundredFourCX_17 : Nat.Prime 17 := by norm_num

private theorem prime_oneHundredFourCX_19 : Nat.Prime 19 := by norm_num

private theorem prime_oneHundredFourCX_23 : Nat.Prime 23 := by norm_num

private theorem prime_oneHundredFourCX_29 : Nat.Prime 29 := by norm_num

private theorem prime_oneHundredFourCX_31 : Nat.Prime 31 := by norm_num

private theorem prime_oneHundredFourCX_37 : Nat.Prime 37 := by norm_num

private theorem prime_oneHundredFourCX_41 : Nat.Prime 41 := by norm_num

private theorem prime_oneHundredFourCX_43 : Nat.Prime 43 := by norm_num

private theorem prime_oneHundredFourCX_47 : Nat.Prime 47 := by norm_num

private theorem prime_oneHundredFourCX_53 : Nat.Prime 53 := by norm_num

private theorem prime_oneHundredFourCX_59 : Nat.Prime 59 := by norm_num

private theorem prime_oneHundredFourCX_61 : Nat.Prime 61 := by norm_num

private theorem prime_oneHundredFourCX_67 : Nat.Prime 67 := by norm_num

private theorem prime_oneHundredFourCX_71 : Nat.Prime 71 := by norm_num

private theorem prime_oneHundredFourCX_73 : Nat.Prime 73 := by norm_num

private theorem prime_oneHundredFourCX_79 : Nat.Prime 79 := by norm_num

private theorem prime_oneHundredFourCX_83 : Nat.Prime 83 := by norm_num

private theorem prime_oneHundredFourCX_89 : Nat.Prime 89 := by norm_num

private theorem prime_oneHundredFourCX_97 : Nat.Prime 97 := by norm_num

private theorem prime_oneHundredFourCX_101 : Nat.Prime 101 := by norm_num

private theorem prime_oneHundredFourCX_103 : Nat.Prime 103 := by norm_num

private theorem prime_oneHundredFourCX_107 : Nat.Prime 107 := by norm_num

private theorem prime_oneHundredFourCX_109 : Nat.Prime 109 := by norm_num

private theorem prime_oneHundredFourCX_113 : Nat.Prime 113 := by norm_num

private theorem prime_oneHundredFourCX_127 : Nat.Prime 127 := by norm_num

private theorem prime_oneHundredFourCX_131 : Nat.Prime 131 := by norm_num

private theorem prime_oneHundredFourCX_137 : Nat.Prime 137 := by norm_num

private theorem prime_oneHundredFourCX_139 : Nat.Prime 139 := by norm_num

private theorem prime_oneHundredFourCX_149 : Nat.Prime 149 := by norm_num

private theorem prime_oneHundredFourCX_151 : Nat.Prime 151 := by norm_num

private theorem prime_oneHundredFourCX_157 : Nat.Prime 157 := by norm_num

private theorem prime_oneHundredFourCX_163 : Nat.Prime 163 := by norm_num

private theorem prime_oneHundredFourCX_167 : Nat.Prime 167 := by norm_num

private theorem prime_oneHundredFourCX_173 : Nat.Prime 173 := by norm_num

private theorem prime_oneHundredFourCX_179 : Nat.Prime 179 := by norm_num

private theorem prime_oneHundredFourCX_191 : Nat.Prime 191 := by norm_num

private theorem prime_oneHundredFourCX_193 : Nat.Prime 193 := by norm_num

private theorem prime_oneHundredFourCX_197 : Nat.Prime 197 := by norm_num

private theorem prime_oneHundredFourCX_211 : Nat.Prime 211 := by norm_num

private theorem prime_oneHundredFourCX_223 : Nat.Prime 223 := by norm_num

private theorem prime_oneHundredFourCX_229 : Nat.Prime 229 := by norm_num

private theorem prime_oneHundredFourCX_233 : Nat.Prime 233 := by norm_num

private theorem prime_oneHundredFourCX_239 : Nat.Prime 239 := by norm_num

private theorem prime_oneHundredFourCX_241 : Nat.Prime 241 := by norm_num

private theorem prime_oneHundredFourCX_251 : Nat.Prime 251 := by norm_num

private theorem prime_oneHundredFourCX_257 : Nat.Prime 257 := by norm_num

private theorem prime_oneHundredFourCX_263 : Nat.Prime 263 := by norm_num

private theorem prime_oneHundredFourCX_269 : Nat.Prime 269 := by norm_num

private theorem prime_oneHundredFourCX_271 : Nat.Prime 271 := by norm_num

private theorem prime_oneHundredFourCX_277 : Nat.Prime 277 := by norm_num

private theorem prime_oneHundredFourCX_281 : Nat.Prime 281 := by norm_num

private theorem prime_oneHundredFourCX_283 : Nat.Prime 283 := by norm_num

private theorem prime_oneHundredFourCX_293 : Nat.Prime 293 := by norm_num

private theorem prime_oneHundredFourCX_307 : Nat.Prime 307 := by norm_num

private theorem prime_oneHundredFourCX_311 : Nat.Prime 311 := by norm_num

private theorem prime_oneHundredFourCX_317 : Nat.Prime 317 := by norm_num

private theorem prime_oneHundredFourCX_337 : Nat.Prime 337 := by norm_num

private theorem prime_oneHundredFourCX_347 : Nat.Prime 347 := by norm_num

private theorem prime_oneHundredFourCX_349 : Nat.Prime 349 := by norm_num

private theorem prime_oneHundredFourCX_359 : Nat.Prime 359 := by norm_num

private theorem prime_oneHundredFourCX_367 : Nat.Prime 367 := by norm_num

private theorem prime_oneHundredFourCX_379 : Nat.Prime 379 := by norm_num

private theorem prime_oneHundredFourCX_383 : Nat.Prime 383 := by norm_num

private theorem prime_oneHundredFourCX_397 : Nat.Prime 397 := by norm_num

private theorem prime_oneHundredFourCX_419 : Nat.Prime 419 := by norm_num

private theorem prime_oneHundredFourCX_431 : Nat.Prime 431 := by norm_num

private theorem prime_oneHundredFourCX_433 : Nat.Prime 433 := by norm_num

private theorem prime_oneHundredFourCX_439 : Nat.Prime 439 := by norm_num

private theorem prime_oneHundredFourCX_457 : Nat.Prime 457 := by norm_num

private theorem prime_oneHundredFourCX_461 : Nat.Prime 461 := by norm_num

private theorem prime_oneHundredFourCX_463 : Nat.Prime 463 := by norm_num

private theorem prime_oneHundredFourCX_479 : Nat.Prime 479 := by norm_num

private theorem prime_oneHundredFourCX_499 : Nat.Prime 499 := by norm_num

private theorem prime_oneHundredFourCX_523 : Nat.Prime 523 := by norm_num

private theorem prime_oneHundredFourCX_571 : Nat.Prime 571 := by norm_num

private theorem prime_oneHundredFourCX_593 : Nat.Prime 593 := by norm_num

private theorem prime_oneHundredFourCX_619 : Nat.Prime 619 := by norm_num

private theorem prime_oneHundredFourCX_631 : Nat.Prime 631 := by norm_num

private theorem prime_oneHundredFourCX_643 : Nat.Prime 643 := by norm_num

private theorem prime_oneHundredFourCX_659 : Nat.Prime 659 := by norm_num

private theorem prime_oneHundredFourCX_673 : Nat.Prime 673 := by norm_num

private theorem prime_oneHundredFourCX_683 : Nat.Prime 683 := by norm_num

private theorem prime_oneHundredFourCX_691 : Nat.Prime 691 := by norm_num

private theorem prime_oneHundredFourCX_719 : Nat.Prime 719 := by norm_num

private theorem prime_oneHundredFourCX_739 : Nat.Prime 739 := by norm_num

private theorem prime_oneHundredFourCX_751 : Nat.Prime 751 := by norm_num

private theorem prime_oneHundredFourCX_757 : Nat.Prime 757 := by norm_num

private theorem prime_oneHundredFourCX_769 : Nat.Prime 769 := by norm_num

private theorem prime_oneHundredFourCX_787 : Nat.Prime 787 := by norm_num

private theorem prime_oneHundredFourCX_809 : Nat.Prime 809 := by norm_num

private theorem prime_oneHundredFourCX_877 : Nat.Prime 877 := by norm_num

private theorem prime_oneHundredFourCX_881 : Nat.Prime 881 := by norm_num

private theorem prime_oneHundredFourCX_883 : Nat.Prime 883 := by norm_num

private theorem prime_oneHundredFourCX_887 : Nat.Prime 887 := by norm_num

private theorem prime_oneHundredFourCX_907 : Nat.Prime 907 := by norm_num

private theorem prime_oneHundredFourCX_919 : Nat.Prime 919 := by norm_num

private theorem prime_oneHundredFourCX_941 : Nat.Prime 941 := by norm_num

private theorem prime_oneHundredFourCX_1009 : Nat.Prime 1009 := by norm_num

private theorem prime_oneHundredFourCX_1013 : Nat.Prime 1013 := by norm_num

private theorem prime_oneHundredFourCX_1031 : Nat.Prime 1031 := by norm_num

private theorem prime_oneHundredFourCX_1033 : Nat.Prime 1033 := by norm_num

private theorem prime_oneHundredFourCX_1091 : Nat.Prime 1091 := by norm_num

private theorem prime_oneHundredFourCX_1093 : Nat.Prime 1093 := by norm_num

private theorem prime_oneHundredFourCX_1097 : Nat.Prime 1097 := by norm_num

private theorem prime_oneHundredFourCX_1103 : Nat.Prime 1103 := by norm_num

private theorem prime_oneHundredFourCX_1109 : Nat.Prime 1109 := by norm_num

private theorem prime_oneHundredFourCX_1163 : Nat.Prime 1163 := by norm_num

private theorem prime_oneHundredFourCX_1217 : Nat.Prime 1217 := by norm_num

private theorem prime_oneHundredFourCX_1259 : Nat.Prime 1259 := by norm_num

private theorem prime_oneHundredFourCX_1277 : Nat.Prime 1277 := by norm_num

private theorem prime_oneHundredFourCX_1289 : Nat.Prime 1289 := by norm_num

private theorem prime_oneHundredFourCX_1319 : Nat.Prime 1319 := by norm_num

private theorem prime_oneHundredFourCX_1427 : Nat.Prime 1427 := by norm_num

private theorem prime_oneHundredFourCX_1471 : Nat.Prime 1471 := by norm_num

private theorem prime_oneHundredFourCX_1493 : Nat.Prime 1493 := by norm_num

private theorem prime_oneHundredFourCX_1543 : Nat.Prime 1543 := by norm_num

private theorem prime_oneHundredFourCX_1549 : Nat.Prime 1549 := by norm_num

private theorem prime_oneHundredFourCX_1553 : Nat.Prime 1553 := by norm_num

private theorem prime_oneHundredFourCX_1583 : Nat.Prime 1583 := by norm_num

private theorem prime_oneHundredFourCX_1667 : Nat.Prime 1667 := by norm_num

private theorem prime_oneHundredFourCX_1759 : Nat.Prime 1759 := by norm_num

private theorem prime_oneHundredFourCX_1811 : Nat.Prime 1811 := by norm_num

private theorem prime_oneHundredFourCX_1831 : Nat.Prime 1831 := by norm_num

private theorem prime_oneHundredFourCX_1867 : Nat.Prime 1867 := by norm_num

private theorem prime_oneHundredFourCX_1889 : Nat.Prime 1889 := by norm_num

private theorem prime_oneHundredFourCX_1901 : Nat.Prime 1901 := by norm_num

private theorem prime_oneHundredFourCX_1987 : Nat.Prime 1987 := by norm_num

private theorem prime_oneHundredFourCX_1993 : Nat.Prime 1993 := by norm_num

private theorem prime_oneHundredFourCX_2011 : Nat.Prime 2011 := by norm_num

private theorem prime_oneHundredFourCX_2027 : Nat.Prime 2027 := by norm_num

private theorem prime_oneHundredFourCX_2131 : Nat.Prime 2131 := by norm_num

private theorem prime_oneHundredFourCX_2179 : Nat.Prime 2179 := by norm_num

private theorem prime_oneHundredFourCX_2293 : Nat.Prime 2293 := by norm_num

private theorem prime_oneHundredFourCX_2357 : Nat.Prime 2357 := by norm_num

private theorem prime_oneHundredFourCX_2377 : Nat.Prime 2377 := by norm_num

private theorem prime_oneHundredFourCX_2411 : Nat.Prime 2411 := by norm_num

private theorem prime_oneHundredFourCX_2423 : Nat.Prime 2423 := by norm_num

private theorem prime_oneHundredFourCX_2521 : Nat.Prime 2521 := by norm_num

private theorem prime_oneHundredFourCX_2549 : Nat.Prime 2549 := by norm_num

private theorem prime_oneHundredFourCX_2579 : Nat.Prime 2579 := by norm_num

private theorem prime_oneHundredFourCX_2593 : Nat.Prime 2593 := by norm_num

private theorem prime_oneHundredFourCX_2711 : Nat.Prime 2711 := by norm_num

private theorem prime_oneHundredFourCX_2731 : Nat.Prime 2731 := by norm_num

private theorem prime_oneHundredFourCX_2741 : Nat.Prime 2741 := by norm_num

private theorem prime_oneHundredFourCX_2777 : Nat.Prime 2777 := by norm_num

private theorem prime_oneHundredFourCX_2879 : Nat.Prime 2879 := by norm_num

private theorem prime_oneHundredFourCX_2887 : Nat.Prime 2887 := by norm_num

private theorem prime_oneHundredFourCX_2903 : Nat.Prime 2903 := by norm_num

private theorem prime_oneHundredFourCX_2909 : Nat.Prime 2909 := by norm_num

private theorem prime_oneHundredFourCX_3221 : Nat.Prime 3221 := by norm_num

private theorem prime_oneHundredFourCX_3373 : Nat.Prime 3373 := by norm_num

private theorem prime_oneHundredFourCX_3803 : Nat.Prime 3803 := by norm_num

private theorem prime_oneHundredFourCX_3823 : Nat.Prime 3823 := by norm_num

private theorem prime_oneHundredFourCX_3947 : Nat.Prime 3947 := by norm_num

private theorem prime_oneHundredFourCX_4027 : Nat.Prime 4027 := by norm_num

private theorem prime_oneHundredFourCX_4057 : Nat.Prime 4057 := by norm_num

private theorem prime_oneHundredFourCX_4093 : Nat.Prime 4093 := by norm_num

private theorem prime_oneHundredFourCX_4447 : Nat.Prime 4447 := by norm_num

private theorem prime_oneHundredFourCX_4463 : Nat.Prime 4463 := by norm_num

private theorem prime_oneHundredFourCX_4519 : Nat.Prime 4519 := by norm_num

private theorem prime_oneHundredFourCX_4679 : Nat.Prime 4679 := by norm_num

private theorem prime_oneHundredFourCX_4729 : Nat.Prime 4729 := by norm_num

private theorem prime_oneHundredFourCX_4733 : Nat.Prime 4733 := by norm_num

private theorem prime_oneHundredFourCX_4969 : Nat.Prime 4969 := by norm_num

private theorem prime_oneHundredFourCX_5209 : Nat.Prime 5209 := by norm_num

private theorem prime_oneHundredFourCX_5443 : Nat.Prime 5443 := by norm_num

private theorem prime_oneHundredFourCX_5573 : Nat.Prime 5573 := by norm_num

private theorem prime_oneHundredFourCX_5651 : Nat.Prime 5651 := by norm_num

private theorem prime_oneHundredFourCX_5717 : Nat.Prime 5717 := by norm_num

private theorem prime_oneHundredFourCX_6029 : Nat.Prime 6029 := by norm_num

private theorem prime_oneHundredFourCX_6101 : Nat.Prime 6101 := by norm_num

private theorem prime_oneHundredFourCX_6113 : Nat.Prime 6113 := by norm_num

private theorem prime_oneHundredFourCX_6151 : Nat.Prime 6151 := by norm_num

private theorem prime_oneHundredFourCX_6173 : Nat.Prime 6173 := by norm_num

private theorem prime_oneHundredFourCX_6277 : Nat.Prime 6277 := by norm_num

private theorem prime_oneHundredFourCX_6317 : Nat.Prime 6317 := by norm_num

private theorem prime_oneHundredFourCX_6553 : Nat.Prime 6553 := by norm_num

private theorem prime_oneHundredFourCX_6709 : Nat.Prime 6709 := by norm_num

private theorem prime_oneHundredFourCX_6883 : Nat.Prime 6883 := by norm_num

private theorem prime_oneHundredFourCX_7001 : Nat.Prime 7001 := by norm_num

private theorem prime_oneHundredFourCX_7213 : Nat.Prime 7213 := by norm_num

private theorem prime_oneHundredFourCX_7247 : Nat.Prime 7247 := by norm_num

private theorem prime_oneHundredFourCX_7561 : Nat.Prime 7561 := by norm_num

private theorem prime_oneHundredFourCX_7607 : Nat.Prime 7607 := by norm_num

private theorem prime_oneHundredFourCX_7789 : Nat.Prime 7789 := by norm_num

private theorem prime_oneHundredFourCX_7919 : Nat.Prime 7919 := by norm_num

private theorem prime_oneHundredFourCX_8273 : Nat.Prime 8273 := by norm_num

private theorem prime_oneHundredFourCX_8377 : Nat.Prime 8377 := by norm_num

private theorem prime_oneHundredFourCX_8521 : Nat.Prime 8521 := by norm_num

private theorem prime_oneHundredFourCX_8807 : Nat.Prime 8807 := by norm_num

private theorem prime_oneHundredFourCX_8929 : Nat.Prime 8929 := by norm_num

private theorem prime_oneHundredFourCX_9439 : Nat.Prime 9439 := by norm_num

private theorem prime_oneHundredFourCX_9719 : Nat.Prime 9719 := by norm_num

private theorem prime_oneHundredFourCX_9923 : Nat.Prime 9923 := by norm_num

private theorem prime_oneHundredFourCX_9967 : Nat.Prime 9967 := by norm_num

private theorem prime_oneHundredFourCX_10333 : Nat.Prime 10333 := by norm_num

private theorem prime_oneHundredFourCX_10781 : Nat.Prime 10781 := by norm_num

private theorem prime_oneHundredFourCX_10789 : Nat.Prime 10789 := by norm_num

private theorem prime_oneHundredFourCX_10831 : Nat.Prime 10831 := by norm_num

private theorem prime_oneHundredFourCX_11117 : Nat.Prime 11117 := by norm_num

private theorem prime_oneHundredFourCX_11519 : Nat.Prime 11519 := by norm_num

private theorem prime_oneHundredFourCX_12073 : Nat.Prime 12073 := by norm_num

private theorem prime_oneHundredFourCX_12373 : Nat.Prime 12373 := by norm_num

private theorem prime_oneHundredFourCX_12659 : Nat.Prime 12659 := by norm_num

private theorem prime_oneHundredFourCX_12821 : Nat.Prime 12821 := by norm_num

private theorem prime_oneHundredFourCX_12911 : Nat.Prime 12911 := by norm_num

private theorem prime_oneHundredFourCX_13187 : Nat.Prime 13187 := by norm_num

private theorem prime_oneHundredFourCX_13411 : Nat.Prime 13411 := by norm_num

private theorem prime_oneHundredFourCX_13417 : Nat.Prime 13417 := by norm_num

private theorem prime_oneHundredFourCX_13441 : Nat.Prime 13441 := by norm_num

private theorem prime_oneHundredFourCX_14051 : Nat.Prime 14051 := by norm_num

private theorem prime_oneHundredFourCX_14107 : Nat.Prime 14107 := by norm_num

private theorem prime_oneHundredFourCX_14387 : Nat.Prime 14387 := by norm_num

private theorem prime_oneHundredFourCX_15073 : Nat.Prime 15073 := by norm_num

private theorem prime_oneHundredFourCX_15091 : Nat.Prime 15091 := by norm_num

private theorem prime_oneHundredFourCX_15373 : Nat.Prime 15373 := by norm_num

private theorem prime_oneHundredFourCX_15901 : Nat.Prime 15901 := by norm_num

private theorem prime_oneHundredFourCX_16067 : Nat.Prime 16067 := by norm_num

private theorem prime_oneHundredFourCX_16651 : Nat.Prime 16651 := by norm_num

private theorem prime_oneHundredFourCX_16831 : Nat.Prime 16831 := by norm_num

private theorem prime_oneHundredFourCX_17203 : Nat.Prime 17203 := by norm_num

private theorem prime_oneHundredFourCX_18913 : Nat.Prime 18913 := by norm_num

private theorem prime_oneHundredFourCX_20333 : Nat.Prime 20333 := by norm_num

private theorem prime_oneHundredFourCX_20357 : Nat.Prime 20357 := by norm_num

private theorem prime_oneHundredFourCX_20753 : Nat.Prime 20753 := by norm_num

private theorem prime_oneHundredFourCX_21011 : Nat.Prime 21011 := by norm_num

private theorem prime_oneHundredFourCX_21391 : Nat.Prime 21391 := by norm_num

private theorem prime_oneHundredFourCX_23369 : Nat.Prime 23369 := by norm_num

private theorem prime_oneHundredFourCX_23447 : Nat.Prime 23447 := by norm_num

private theorem prime_oneHundredFourCX_23671 : Nat.Prime 23671 := by norm_num

private theorem prime_oneHundredFourCX_24841 : Nat.Prime 24841 := by norm_num

private theorem prime_oneHundredFourCX_26021 : Nat.Prime 26021 := by norm_num

private theorem prime_oneHundredFourCX_26183 : Nat.Prime 26183 := by norm_num

private theorem prime_oneHundredFourCX_28211 : Nat.Prime 28211 := by norm_num

private theorem prime_oneHundredFourCX_28607 : Nat.Prime 28607 := by norm_num

private theorem prime_oneHundredFourCX_28643 : Nat.Prime 28643 := by norm_num

private theorem prime_oneHundredFourCX_28729 : Nat.Prime 28729 := by norm_num

private theorem prime_oneHundredFourCX_31219 : Nat.Prime 31219 := by norm_num

private theorem prime_oneHundredFourCX_31547 : Nat.Prime 31547 := by norm_num

private theorem prime_oneHundredFourCX_32063 : Nat.Prime 32063 := by norm_num

private theorem prime_oneHundredFourCX_32779 : Nat.Prime 32779 := by norm_num

private theorem prime_oneHundredFourCX_33739 : Nat.Prime 33739 := by norm_num

private theorem prime_oneHundredFourCX_33767 : Nat.Prime 33767 := by norm_num

private theorem prime_oneHundredFourCX_33797 : Nat.Prime 33797 := by norm_num

private theorem prime_oneHundredFourCX_36493 : Nat.Prime 36493 := by norm_num

private theorem prime_oneHundredFourCX_37573 : Nat.Prime 37573 := by norm_num

private theorem prime_oneHundredFourCX_38333 : Nat.Prime 38333 := by norm_num

private theorem prime_oneHundredFourCX_39023 : Nat.Prime 39023 := by norm_num

private theorem prime_oneHundredFourCX_39047 : Nat.Prime 39047 := by norm_num

private theorem prime_oneHundredFourCX_41513 : Nat.Prime 41513 := by norm_num

private theorem prime_oneHundredFourCX_41627 : Nat.Prime 41627 := by norm_num

private theorem prime_oneHundredFourCX_41941 : Nat.Prime 41941 := by norm_num

private theorem prime_oneHundredFourCX_43291 : Nat.Prime 43291 := by norm_num

private theorem prime_oneHundredFourCX_43609 : Nat.Prime 43609 := by norm_num

private theorem prime_oneHundredFourCX_46457 : Nat.Prime 46457 := by norm_num

private theorem prime_oneHundredFourCX_48017 : Nat.Prime 48017 := by norm_num

private theorem prime_oneHundredFourCX_48313 : Nat.Prime 48313 := by norm_num

private theorem prime_oneHundredFourCX_50789 : Nat.Prime 50789 := by norm_num

private theorem prime_oneHundredFourCX_51581 : Nat.Prime 51581 := by norm_num

private theorem prime_oneHundredFourCX_52757 : Nat.Prime 52757 := by norm_num

private theorem prime_oneHundredFourCX_53279 : Nat.Prime 53279 := by norm_num

private theorem prime_oneHundredFourCX_53597 : Nat.Prime 53597 := by norm_num

private theorem prime_oneHundredFourCX_53897 : Nat.Prime 53897 := by norm_num

private theorem prime_oneHundredFourCX_54091 : Nat.Prime 54091 := by norm_num

private theorem prime_oneHundredFourCX_54323 : Nat.Prime 54323 := by norm_num

private theorem prime_oneHundredFourCX_54419 : Nat.Prime 54419 := by norm_num

private theorem prime_oneHundredFourCX_55171 : Nat.Prime 55171 := by norm_num

private theorem prime_oneHundredFourCX_55351 : Nat.Prime 55351 := by norm_num

private theorem prime_oneHundredFourCX_55787 : Nat.Prime 55787 := by norm_num

private theorem prime_oneHundredFourCX_55799 : Nat.Prime 55799 := by norm_num

private theorem prime_oneHundredFourCX_55927 : Nat.Prime 55927 := by norm_num

private theorem prime_oneHundredFourCX_56821 : Nat.Prime 56821 := by norm_num

private theorem prime_oneHundredFourCX_57397 : Nat.Prime 57397 := by norm_num

private theorem prime_oneHundredFourCX_62039 : Nat.Prime 62039 := by norm_num

private theorem prime_oneHundredFourCX_62939 : Nat.Prime 62939 := by norm_num

private theorem prime_oneHundredFourCX_64217 : Nat.Prime 64217 := by norm_num

private theorem prime_oneHundredFourCX_65789 : Nat.Prime 65789 := by norm_num

private theorem prime_oneHundredFourCX_65837 : Nat.Prime 65837 := by norm_num

private theorem prime_oneHundredFourCX_66089 : Nat.Prime 66089 := by norm_num

private theorem prime_oneHundredFourCX_69997 : Nat.Prime 69997 := by norm_num

private theorem prime_oneHundredFourCX_71171 : Nat.Prime 71171 := by norm_num

private theorem prime_oneHundredFourCX_74293 : Nat.Prime 74293 := by norm_num

private theorem prime_oneHundredFourCX_79349 : Nat.Prime 79349 := by norm_num

private theorem prime_oneHundredFourCX_79379 : Nat.Prime 79379 := by norm_num

private theorem prime_oneHundredFourCX_83357 : Nat.Prime 83357 := by norm_num

private theorem prime_oneHundredFourCX_86719 : Nat.Prime 86719 := by norm_num

private theorem prime_oneHundredFourCX_88423 : Nat.Prime 88423 := by norm_num

private theorem prime_oneHundredFourCX_89119 : Nat.Prime 89119 := by norm_num

private theorem prime_oneHundredFourCX_95279 : Nat.Prime 95279 := by norm_num

private theorem prime_oneHundredFourCX_96289 : Nat.Prime 96289 := by norm_num

private theorem prime_oneHundredFourCX_98939 : Nat.Prime 98939 := by norm_num

private theorem prime_oneHundredFourCX_103723 : Nat.Prime 103723 := by norm_num

private theorem prime_oneHundredFourCX_110119 : Nat.Prime 110119 := by norm_num

private theorem prime_oneHundredFourCX_119929 : Nat.Prime 119929 := by norm_num

private theorem prime_oneHundredFourCX_125539 : Nat.Prime 125539 := by norm_num

private theorem prime_oneHundredFourCX_134171 : Nat.Prime 134171 := by norm_num

private theorem prime_oneHundredFourCX_143977 : Nat.Prime 143977 := by norm_num

private theorem prime_oneHundredFourCX_160183 : Nat.Prime 160183 := by norm_num

private theorem prime_oneHundredFourCX_169003 : Nat.Prime 169003 := by norm_num

private theorem prime_oneHundredFourCX_170603 : Nat.Prime 170603 := by norm_num

private theorem prime_oneHundredFourCX_171401 : Nat.Prime 171401 := by norm_num

private theorem prime_oneHundredFourCX_172313 : Nat.Prime 172313 := by norm_num

private theorem prime_oneHundredFourCX_194527 : Nat.Prime 194527 := by norm_num

private theorem prime_oneHundredFourCX_195893 : Nat.Prime 195893 := by norm_num

private theorem prime_oneHundredFourCX_201211 : Nat.Prime 201211 := by norm_num

private theorem prime_oneHundredFourCX_204859 : Nat.Prime 204859 := by norm_num

private theorem prime_oneHundredFourCX_207341 : Nat.Prime 207341 := by norm_num

private theorem prime_oneHundredFourCX_210403 : Nat.Prime 210403 := by norm_num

private theorem prime_oneHundredFourCX_213613 : Nat.Prime 213613 := by norm_num

private theorem prime_oneHundredFourCX_216133 : Nat.Prime 216133 := by norm_num

private theorem prime_oneHundredFourCX_219683 : Nat.Prime 219683 := by norm_num

private theorem prime_oneHundredFourCX_232439 : Nat.Prime 232439 := by norm_num

private theorem prime_oneHundredFourCX_235013 : Nat.Prime 235013 := by norm_num

private theorem prime_oneHundredFourCX_237467 : Nat.Prime 237467 := by norm_num

private theorem prime_oneHundredFourCX_238531 : Nat.Prime 238531 := by norm_num

private theorem prime_oneHundredFourCX_241817 : Nat.Prime 241817 := by norm_num

private theorem prime_oneHundredFourCX_243209 : Nat.Prime 243209 := by norm_num

private theorem prime_oneHundredFourCX_244781 : Nat.Prime 244781 := by norm_num

private theorem prime_oneHundredFourCX_245299 : Nat.Prime 245299 := by norm_num

private theorem prime_oneHundredFourCX_250361 : Nat.Prime 250361 := by norm_num

private theorem prime_oneHundredFourCX_251897 : Nat.Prime 251897 := by norm_num

private theorem prime_oneHundredFourCX_256211 : Nat.Prime 256211 := by norm_num

private theorem prime_oneHundredFourCX_257611 : Nat.Prime 257611 := by norm_num

private theorem prime_oneHundredFourCX_285841 : Nat.Prime 285841 := by norm_num

private theorem prime_oneHundredFourCX_305101 : Nat.Prime 305101 := by norm_num

private theorem prime_oneHundredFourCX_320401 : Nat.Prime 320401 := by norm_num

private theorem prime_oneHundredFourCX_321187 : Nat.Prime 321187 := by norm_num

private theorem prime_oneHundredFourCX_327289 : Nat.Prime 327289 := by norm_num

private theorem prime_oneHundredFourCX_327797 : Nat.Prime 327797 := by norm_num

private theorem prime_oneHundredFourCX_328633 : Nat.Prime 328633 := by norm_num

private theorem prime_oneHundredFourCX_346417 : Nat.Prime 346417 := by norm_num

private theorem prime_oneHundredFourCX_355027 : Nat.Prime 355027 := by norm_num

private theorem prime_oneHundredFourCX_362027 : Nat.Prime 362027 := by norm_num

private theorem prime_oneHundredFourCX_385771 : Nat.Prime 385771 := by norm_num

private theorem prime_oneHundredFourCX_398407 : Nat.Prime 398407 := by norm_num

private theorem prime_oneHundredFourCX_432659 : Nat.Prime 432659 := by norm_num

private theorem prime_oneHundredFourCX_460987 : Nat.Prime 460987 := by norm_num

private theorem prime_oneHundredFourCX_517721 : Nat.Prime 517721 := by norm_num

private theorem prime_oneHundredFourCX_549481 : Nat.Prime 549481 := by norm_num

private theorem prime_oneHundredFourCX_569507 : Nat.Prime 569507 := by norm_num

private theorem prime_oneHundredFourCX_586367 : Nat.Prime 586367 := by norm_num

private theorem prime_oneHundredFourCX_598777 : Nat.Prime 598777 := by norm_num

private theorem prime_oneHundredFourCX_609913 : Nat.Prime 609913 := by norm_num

private theorem prime_oneHundredFourCX_633317 : Nat.Prime 633317 := by norm_num

private theorem prime_oneHundredFourCX_678593 : Nat.Prime 678593 := by norm_num

private theorem prime_oneHundredFourCX_688217 : Nat.Prime 688217 := by norm_num

private theorem prime_oneHundredFourCX_694717 : Nat.Prime 694717 := by norm_num

private theorem prime_oneHundredFourCX_712301 : Nat.Prime 712301 := by norm_num

private theorem prime_oneHundredFourCX_747139 : Nat.Prime 747139 := by norm_num

private theorem prime_oneHundredFourCX_767537 : Nat.Prime 767537 := by norm_num

private theorem prime_oneHundredFourCX_781631 : Nat.Prime 781631 := by norm_num

private theorem prime_oneHundredFourCX_881987 : Nat.Prime 881987 := by norm_num

private theorem prime_oneHundredFourCX_921517 : Nat.Prime 921517 := by norm_num

private theorem prime_oneHundredFourCX_951407 : Nat.Prime 951407 := by norm_num

private theorem prime_oneHundredFourCX_965749 : Nat.Prime 965749 := by norm_num

private theorem prime_oneHundredFourCX_1059419 : Nat.Prime 1059419 := by norm_num

private theorem prime_oneHundredFourCX_1062311 : Nat.Prime 1062311 := by norm_num

private theorem prime_oneHundredFourCX_1100041 : Nat.Prime 1100041 := by norm_num

private theorem prime_oneHundredFourCX_1152037 : Nat.Prime 1152037 := by norm_num

private theorem prime_oneHundredFourCX_1229519 : Nat.Prime 1229519 := by norm_num

private theorem prime_oneHundredFourCX_1244263 : Nat.Prime 1244263 := by norm_num

private theorem prime_oneHundredFourCX_1404763 : Nat.Prime 1404763 := by norm_num

private theorem prime_oneHundredFourCX_1454821 : Nat.Prime 1454821 := by norm_num

private theorem prime_oneHundredFourCX_1752941 : Nat.Prime 1752941 := by norm_num

private theorem prime_oneHundredFourCX_1775737 : Nat.Prime 1775737 := by norm_num

private theorem prime_oneHundredFourCX_1997243 : Nat.Prime 1997243 := by norm_num

private theorem prime_oneHundredFourCX_2017409 : Nat.Prime 2017409 := by norm_num

private theorem prime_oneHundredFourCX_2289239 : Nat.Prime 2289239 := by norm_num

private theorem prime_oneHundredFourCX_2610161 : Nat.Prime 2610161 := by norm_num

private theorem prime_oneHundredFourCX_2630521 : Nat.Prime 2630521 := by norm_num

private theorem prime_oneHundredFourCX_2677099 : Nat.Prime 2677099 := by norm_num

private theorem prime_oneHundredFourCX_2755243 : Nat.Prime 2755243 := by norm_num

private theorem prime_oneHundredFourCX_2775559 : Nat.Prime 2775559 := by norm_num

private theorem prime_oneHundredFourCX_2846749 : Nat.Prime 2846749 := by norm_num

private theorem prime_oneHundredFourCX_2954863 : Nat.Prime 2954863 := by norm_num

private theorem prime_oneHundredFourCX_3057283 : Nat.Prime 3057283 := by norm_num

private theorem prime_oneHundredFourCX_3059143 : Nat.Prime 3059143 := by norm_num

private theorem prime_oneHundredFourCX_3114971 : Nat.Prime 3114971 := by norm_num

private theorem prime_oneHundredFourCX_3227281 : Nat.Prime 3227281 := by norm_num

private theorem prime_oneHundredFourCX_3463319 : Nat.Prime 3463319 := by norm_num

private theorem prime_oneHundredFourCX_3466751 : Nat.Prime 3466751 := by norm_num

private theorem prime_oneHundredFourCX_3594403 : Nat.Prime 3594403 := by norm_num

private theorem prime_oneHundredFourCX_3625339 : Nat.Prime 3625339 := by norm_num

private theorem prime_oneHundredFourCX_3638827 : Nat.Prime 3638827 := by norm_num

private theorem prime_oneHundredFourCX_3735139 : Nat.Prime 3735139 := by norm_num

private theorem prime_oneHundredFourCX_4066691 : Nat.Prime 4066691 := by norm_num

private theorem prime_oneHundredFourCX_4440187 : Nat.Prime 4440187 := by norm_num

private theorem prime_oneHundredFourCX_4568453 : Nat.Prime 4568453 := by norm_num

private theorem prime_oneHundredFourCX_4857271 : Nat.Prime 4857271 := by norm_num

private theorem prime_oneHundredFourCX_5202511 : Nat.Prime 5202511 := by norm_num

private theorem prime_oneHundredFourCX_5807869 : Nat.Prime 5807869 := by norm_num

private theorem prime_oneHundredFourCX_6931649 : Nat.Prime 6931649 := by norm_num

private theorem prime_oneHundredFourCX_7631857 : Nat.Prime 7631857 := by norm_num

private theorem prime_oneHundredFourCX_7809413 : Nat.Prime 7809413 := by norm_num

private theorem prime_oneHundredFourCX_7928441 : Nat.Prime 7928441 := by norm_num

private theorem prime_oneHundredFourCX_8302403 : Nat.Prime 8302403 := by norm_num

private theorem prime_oneHundredFourCX_8339297 : Nat.Prime 8339297 := by norm_num

private theorem prime_oneHundredFourCX_8422787 : Nat.Prime 8422787 := by norm_num

private theorem prime_oneHundredFourCX_8485681 : Nat.Prime 8485681 := by norm_num

private theorem prime_oneHundredFourCX_8532299 : Nat.Prime 8532299 := by norm_num

private theorem prime_oneHundredFourCX_8802841 : Nat.Prime 8802841 := by norm_num

private theorem prime_oneHundredFourCX_9890501 : Nat.Prime 9890501 := by norm_num

private theorem prime_oneHundredFourCX_10071353 : Nat.Prime 10071353 := by norm_num

private theorem prime_oneHundredFourCX_10320283 : Nat.Prime 10320283 := by norm_num

private theorem prime_oneHundredFourCX_10399843 : Nat.Prime 10399843 := by norm_num

private theorem prime_oneHundredFourCX_10820141 : Nat.Prime 10820141 := by norm_num

private theorem prime_oneHundredFourCX_12040139 : Nat.Prime 12040139 := by norm_num

private theorem prime_oneHundredFourCX_12078173 : Nat.Prime 12078173 := by norm_num

private theorem prime_oneHundredFourCX_12155849 : Nat.Prime 12155849 := by norm_num

private theorem prime_oneHundredFourCX_12188791 : Nat.Prime 12188791 := by norm_num

private theorem prime_oneHundredFourCX_12337727 : Nat.Prime 12337727 := by norm_num

private theorem prime_oneHundredFourCX_13836413 : Nat.Prime 13836413 := by norm_num

private theorem prime_oneHundredFourCX_14025593 : Nat.Prime 14025593 := by norm_num

private theorem prime_oneHundredFourCX_14692609 : Nat.Prime 14692609 := by norm_num

private theorem prime_oneHundredFourCX_15054001 : Nat.Prime 15054001 := by norm_num

private theorem prime_oneHundredFourCX_15425269 : Nat.Prime 15425269 := by norm_num

private theorem prime_oneHundredFourCX_17296753 : Nat.Prime 17296753 := by norm_num

private theorem prime_oneHundredFourCX_20291147 : Nat.Prime 20291147 := by norm_num

private theorem prime_oneHundredFourCX_21378529 : Nat.Prime 21378529 := by norm_num

private theorem prime_oneHundredFourCX_21546677 : Nat.Prime 21546677 := by norm_num

private theorem prime_oneHundredFourCX_21724111 : Nat.Prime 21724111 := by norm_num

private theorem prime_oneHundredFourCX_23385361 : Nat.Prime 23385361 := by norm_num

private theorem prime_oneHundredFourCX_23750833 : Nat.Prime 23750833 := by norm_num

private theorem prime_oneHundredFourCX_24108629 : Nat.Prime 24108629 := by norm_num

private theorem prime_oneHundredFourCX_24336439 : Nat.Prime 24336439 := by norm_num

private theorem prime_oneHundredFourCX_24338467 : Nat.Prime 24338467 := by norm_num

private theorem prime_oneHundredFourCX_25356953 : Nat.Prime 25356953 := by norm_num

private theorem prime_oneHundredFourCX_26462333 : Nat.Prime 26462333 := by norm_num

private theorem prime_oneHundredFourCX_26954803 : Nat.Prime 26954803 := by norm_num

private theorem prime_oneHundredFourCX_29465563 : Nat.Prime 29465563 := by norm_num

private theorem prime_oneHundredFourCX_29567803 : Nat.Prime 29567803 := by norm_num

private theorem prime_oneHundredFourCX_44240389 : Nat.Prime 44240389 := by
  apply lucas_primality 44240389 (2 : ZMod 44240389)
  · rw [← oneHundredFourCXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (1277, 1), (2887, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (1277, 1), (2887, 1)] : List FactorBlock).map factorBlockValue).prod) = 44240389 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourCX_2
      · exact prime_oneHundredFourCX_3
      · exact prime_oneHundredFourCX_1277
      · exact prime_oneHundredFourCX_2887
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 44240389) ^ 22120194 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (2 : ZMod 44240389) ^ 14746796 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (2 : ZMod 44240389) ^ 34644 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (2 : ZMod 44240389) ^ 15324 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourCX_45247621 : Nat.Prime 45247621 := by
  apply lucas_primality 45247621 (2 : ZMod 45247621)
  · rw [← oneHundredFourCXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (11, 1), (179, 1), (383, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (11, 1), (179, 1), (383, 1)] : List FactorBlock).map factorBlockValue).prod) = 45247621 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourCX_2
      · exact prime_oneHundredFourCX_3
      · exact prime_oneHundredFourCX_5
      · exact prime_oneHundredFourCX_11
      · exact prime_oneHundredFourCX_179
      · exact prime_oneHundredFourCX_383
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 45247621) ^ 22623810 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (2 : ZMod 45247621) ^ 15082540 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (2 : ZMod 45247621) ^ 9049524 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (2 : ZMod 45247621) ^ 4113420 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (2 : ZMod 45247621) ^ 252780 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (2 : ZMod 45247621) ^ 118140 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourCX_48288841 : Nat.Prime 48288841 := by
  apply lucas_primality 48288841 (14 : ZMod 48288841)
  · rw [← oneHundredFourCXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 1), (17, 1), (23671, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 1), (17, 1), (23671, 1)] : List FactorBlock).map factorBlockValue).prod) = 48288841 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourCX_2
      · exact prime_oneHundredFourCX_3
      · exact prime_oneHundredFourCX_5
      · exact prime_oneHundredFourCX_17
      · exact prime_oneHundredFourCX_23671
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (14 : ZMod 48288841) ^ 24144420 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (14 : ZMod 48288841) ^ 16096280 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (14 : ZMod 48288841) ^ 9657768 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (14 : ZMod 48288841) ^ 2840520 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (14 : ZMod 48288841) ^ 2040 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourCX_52025111 : Nat.Prime 52025111 := by
  apply lucas_primality 52025111 (13 : ZMod 52025111)
  · rw [← oneHundredFourCXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (5202511, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (5202511, 1)] : List FactorBlock).map factorBlockValue).prod) = 52025111 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFourCX_2
      · exact prime_oneHundredFourCX_5
      · exact prime_oneHundredFourCX_5202511
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (13 : ZMod 52025111) ^ 26012555 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (13 : ZMod 52025111) ^ 10405022 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (13 : ZMod 52025111) ^ 10 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourCX_59223277 : Nat.Prime 59223277 := by
  apply lucas_primality 59223277 (2 : ZMod 59223277)
  · rw [← oneHundredFourCXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (7, 1), (235013, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (7, 1), (235013, 1)] : List FactorBlock).map factorBlockValue).prod) = 59223277 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourCX_2
      · exact prime_oneHundredFourCX_3
      · exact prime_oneHundredFourCX_7
      · exact prime_oneHundredFourCX_235013
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 59223277) ^ 29611638 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (2 : ZMod 59223277) ^ 19741092 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (2 : ZMod 59223277) ^ 8460468 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (2 : ZMod 59223277) ^ 252 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourCX_59899309 : Nat.Prime 59899309 := by
  apply lucas_primality 59899309 (11 : ZMod 59899309)
  · rw [← oneHundredFourCXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 1), (643, 1), (1109, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 1), (643, 1), (1109, 1)] : List FactorBlock).map factorBlockValue).prod) = 59899309 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourCX_2
      · exact prime_oneHundredFourCX_3
      · exact prime_oneHundredFourCX_7
      · exact prime_oneHundredFourCX_643
      · exact prime_oneHundredFourCX_1109
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 59899309) ^ 29949654 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (11 : ZMod 59899309) ^ 19966436 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (11 : ZMod 59899309) ^ 8557044 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (11 : ZMod 59899309) ^ 93156 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (11 : ZMod 59899309) ^ 54012 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourCX_59929613 : Nat.Prime 59929613 := by
  apply lucas_primality 59929613 (2 : ZMod 59929613)
  · rw [← oneHundredFourCXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (1811, 1), (8273, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (1811, 1), (8273, 1)] : List FactorBlock).map factorBlockValue).prod) = 59929613 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFourCX_2
      · exact prime_oneHundredFourCX_1811
      · exact prime_oneHundredFourCX_8273
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 59929613) ^ 29964806 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (2 : ZMod 59929613) ^ 33092 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (2 : ZMod 59929613) ^ 7244 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourCX_62402203 : Nat.Prime 62402203 := by
  apply lucas_primality 62402203 (3 : ZMod 62402203)
  · rw [← oneHundredFourCXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (37, 1), (43, 1), (2179, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (37, 1), (43, 1), (2179, 1)] : List FactorBlock).map factorBlockValue).prod) = 62402203 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourCX_2
      · exact prime_oneHundredFourCX_3
      · exact prime_oneHundredFourCX_37
      · exact prime_oneHundredFourCX_43
      · exact prime_oneHundredFourCX_2179
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 62402203) ^ 31201101 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (3 : ZMod 62402203) ^ 20800734 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (3 : ZMod 62402203) ^ 1686546 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (3 : ZMod 62402203) ^ 1451214 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (3 : ZMod 62402203) ^ 28638 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourCX_63550741 : Nat.Prime 63550741 := by
  apply lucas_primality 63550741 (10 : ZMod 63550741)
  · rw [← oneHundredFourCXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (11, 1), (96289, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (11, 1), (96289, 1)] : List FactorBlock).map factorBlockValue).prod) = 63550741 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourCX_2
      · exact prime_oneHundredFourCX_3
      · exact prime_oneHundredFourCX_5
      · exact prime_oneHundredFourCX_11
      · exact prime_oneHundredFourCX_96289
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 63550741) ^ 31775370 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (10 : ZMod 63550741) ^ 21183580 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (10 : ZMod 63550741) ^ 12710148 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (10 : ZMod 63550741) ^ 5777340 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (10 : ZMod 63550741) ^ 660 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourCX_68744369 : Nat.Prime 68744369 := by
  apply lucas_primality 68744369 (6 : ZMod 68744369)
  · rw [← oneHundredFourCXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (7, 1), (11, 1), (55799, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (7, 1), (11, 1), (55799, 1)] : List FactorBlock).map factorBlockValue).prod) = 68744369 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourCX_2
      · exact prime_oneHundredFourCX_7
      · exact prime_oneHundredFourCX_11
      · exact prime_oneHundredFourCX_55799
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 68744369) ^ 34372184 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (6 : ZMod 68744369) ^ 9820624 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (6 : ZMod 68744369) ^ 6249488 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (6 : ZMod 68744369) ^ 1232 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourCX_71963443 : Nat.Prime 71963443 := by
  apply lucas_primality 71963443 (2 : ZMod 71963443)
  · rw [← oneHundredFourCXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (29, 1), (89, 1), (1549, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (29, 1), (89, 1), (1549, 1)] : List FactorBlock).map factorBlockValue).prod) = 71963443 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourCX_2
      · exact prime_oneHundredFourCX_3
      · exact prime_oneHundredFourCX_29
      · exact prime_oneHundredFourCX_89
      · exact prime_oneHundredFourCX_1549
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 71963443) ^ 35981721 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (2 : ZMod 71963443) ^ 23987814 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (2 : ZMod 71963443) ^ 2481498 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (2 : ZMod 71963443) ^ 808578 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (2 : ZMod 71963443) ^ 46458 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourCX_72249637 : Nat.Prime 72249637 := by
  apply lucas_primality 72249637 (5 : ZMod 72249637)
  · rw [← oneHundredFourCXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (1471, 1), (4093, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (1471, 1), (4093, 1)] : List FactorBlock).map factorBlockValue).prod) = 72249637 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourCX_2
      · exact prime_oneHundredFourCX_3
      · exact prime_oneHundredFourCX_1471
      · exact prime_oneHundredFourCX_4093
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 72249637) ^ 36124818 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (5 : ZMod 72249637) ^ 24083212 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (5 : ZMod 72249637) ^ 49116 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (5 : ZMod 72249637) ^ 17652 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourCX_75825557 : Nat.Prime 75825557 := by
  apply lucas_primality 75825557 (2 : ZMod 75825557)
  · rw [← oneHundredFourCXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (151, 1), (125539, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (151, 1), (125539, 1)] : List FactorBlock).map factorBlockValue).prod) = 75825557 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFourCX_2
      · exact prime_oneHundredFourCX_151
      · exact prime_oneHundredFourCX_125539
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 75825557) ^ 37912778 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (2 : ZMod 75825557) ^ 502156 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (2 : ZMod 75825557) ^ 604 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourCX_88875769 : Nat.Prime 88875769 := by
  apply lucas_primality 88875769 (7 : ZMod 88875769)
  · rw [← oneHundredFourCXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (19, 1), (67, 1), (2909, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (19, 1), (67, 1), (2909, 1)] : List FactorBlock).map factorBlockValue).prod) = 88875769 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourCX_2
      · exact prime_oneHundredFourCX_3
      · exact prime_oneHundredFourCX_19
      · exact prime_oneHundredFourCX_67
      · exact prime_oneHundredFourCX_2909
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 88875769) ^ 44437884 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (7 : ZMod 88875769) ^ 29625256 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (7 : ZMod 88875769) ^ 4677672 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (7 : ZMod 88875769) ^ 1326504 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (7 : ZMod 88875769) ^ 30552 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourCX_91545943 : Nat.Prime 91545943 := by
  apply lucas_primality 91545943 (3 : ZMod 91545943)
  · rw [← oneHundredFourCXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (47, 1), (73, 1), (4447, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (47, 1), (73, 1), (4447, 1)] : List FactorBlock).map factorBlockValue).prod) = 91545943 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourCX_2
      · exact prime_oneHundredFourCX_3
      · exact prime_oneHundredFourCX_47
      · exact prime_oneHundredFourCX_73
      · exact prime_oneHundredFourCX_4447
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 91545943) ^ 45772971 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (3 : ZMod 91545943) ^ 30515314 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (3 : ZMod 91545943) ^ 1947786 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (3 : ZMod 91545943) ^ 1254054 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (3 : ZMod 91545943) ^ 20586 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourCX_92103133 : Nat.Prime 92103133 := by
  apply lucas_primality 92103133 (5 : ZMod 92103133)
  · rw [← oneHundredFourCXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (11, 1), (23, 2), (1319, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (11, 1), (23, 2), (1319, 1)] : List FactorBlock).map factorBlockValue).prod) = 92103133 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourCX_2
      · exact prime_oneHundredFourCX_3
      · exact prime_oneHundredFourCX_11
      · exact prime_oneHundredFourCX_23
      · exact prime_oneHundredFourCX_1319
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 92103133) ^ 46051566 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (5 : ZMod 92103133) ^ 30701044 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (5 : ZMod 92103133) ^ 8373012 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (5 : ZMod 92103133) ^ 4004484 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (5 : ZMod 92103133) ^ 69828 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourCX_102534983 : Nat.Prime 102534983 := by
  apply lucas_primality 102534983 (5 : ZMod 102534983)
  · rw [← oneHundredFourCXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (19, 1), (245299, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (19, 1), (245299, 1)] : List FactorBlock).map factorBlockValue).prod) = 102534983 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourCX_2
      · exact prime_oneHundredFourCX_11
      · exact prime_oneHundredFourCX_19
      · exact prime_oneHundredFourCX_245299
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 102534983) ^ 51267491 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (5 : ZMod 102534983) ^ 9321362 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (5 : ZMod 102534983) ^ 5396578 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (5 : ZMod 102534983) ^ 418 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourCX_102578743 : Nat.Prime 102578743 := by
  apply lucas_primality 102578743 (6 : ZMod 102578743)
  · rw [← oneHundredFourCXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (7, 1), (29, 1), (67, 1), (419, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (7, 1), (29, 1), (67, 1), (419, 1)] : List FactorBlock).map factorBlockValue).prod) = 102578743 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourCX_2
      · exact prime_oneHundredFourCX_3
      · exact prime_oneHundredFourCX_7
      · exact prime_oneHundredFourCX_29
      · exact prime_oneHundredFourCX_67
      · exact prime_oneHundredFourCX_419
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 102578743) ^ 51289371 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (6 : ZMod 102578743) ^ 34192914 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (6 : ZMod 102578743) ^ 14654106 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (6 : ZMod 102578743) ^ 3537198 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (6 : ZMod 102578743) ^ 1531026 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (6 : ZMod 102578743) ^ 244818 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourCX_103533119 : Nat.Prime 103533119 := by
  apply lucas_primality 103533119 (7 : ZMod 103533119)
  · rw [← oneHundredFourCXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 2), (31, 1), (41, 1), (241, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 2), (31, 1), (41, 1), (241, 1)] : List FactorBlock).map factorBlockValue).prod) = 103533119 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourCX_2
      · exact prime_oneHundredFourCX_13
      · exact prime_oneHundredFourCX_31
      · exact prime_oneHundredFourCX_41
      · exact prime_oneHundredFourCX_241
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 103533119) ^ 51766559 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (7 : ZMod 103533119) ^ 7964086 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (7 : ZMod 103533119) ^ 3339778 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (7 : ZMod 103533119) ^ 2525198 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (7 : ZMod 103533119) ^ 429598 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourCX_104050223 : Nat.Prime 104050223 := by
  apply lucas_primality 104050223 (5 : ZMod 104050223)
  · rw [← oneHundredFourCXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (52025111, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (52025111, 1)] : List FactorBlock).map factorBlockValue).prod) = 104050223 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredFourCX_2
      · exact prime_oneHundredFourCX_52025111
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 104050223) ^ 52025111 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (5 : ZMod 104050223) ^ 2 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourCX_104921471 : Nat.Prime 104921471 := by
  apply lucas_primality 104921471 (7 : ZMod 104921471)
  · rw [← oneHundredFourCXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (59, 1), (163, 1), (1091, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (59, 1), (163, 1), (1091, 1)] : List FactorBlock).map factorBlockValue).prod) = 104921471 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourCX_2
      · exact prime_oneHundredFourCX_5
      · exact prime_oneHundredFourCX_59
      · exact prime_oneHundredFourCX_163
      · exact prime_oneHundredFourCX_1091
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 104921471) ^ 52460735 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (7 : ZMod 104921471) ^ 20984294 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (7 : ZMod 104921471) ^ 1778330 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (7 : ZMod 104921471) ^ 643690 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (7 : ZMod 104921471) ^ 96170 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourCX_105381401 : Nat.Prime 105381401 := by
  apply lucas_primality 105381401 (6 : ZMod 105381401)
  · rw [← oneHundredFourCXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 2), (23, 1), (31, 1), (739, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 2), (23, 1), (31, 1), (739, 1)] : List FactorBlock).map factorBlockValue).prod) = 105381401 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourCX_2
      · exact prime_oneHundredFourCX_5
      · exact prime_oneHundredFourCX_23
      · exact prime_oneHundredFourCX_31
      · exact prime_oneHundredFourCX_739
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 105381401) ^ 52690700 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (6 : ZMod 105381401) ^ 21076280 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (6 : ZMod 105381401) ^ 4581800 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (6 : ZMod 105381401) ^ 3399400 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (6 : ZMod 105381401) ^ 142600 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourCX_110458261 : Nat.Prime 110458261 := by
  apply lucas_primality 110458261 (19 : ZMod 110458261)
  · rw [← oneHundredFourCXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (5, 1), (11, 1), (55787, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (5, 1), (11, 1), (55787, 1)] : List FactorBlock).map factorBlockValue).prod) = 110458261 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourCX_2
      · exact prime_oneHundredFourCX_3
      · exact prime_oneHundredFourCX_5
      · exact prime_oneHundredFourCX_11
      · exact prime_oneHundredFourCX_55787
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (19 : ZMod 110458261) ^ 55229130 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (19 : ZMod 110458261) ^ 36819420 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (19 : ZMod 110458261) ^ 22091652 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (19 : ZMod 110458261) ^ 10041660 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (19 : ZMod 110458261) ^ 1980 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourCX_142641539 : Nat.Prime 142641539 := by
  apply lucas_primality 142641539 (2 : ZMod 142641539)
  · rw [← oneHundredFourCXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (23, 1), (238531, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (23, 1), (238531, 1)] : List FactorBlock).map factorBlockValue).prod) = 142641539 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourCX_2
      · exact prime_oneHundredFourCX_13
      · exact prime_oneHundredFourCX_23
      · exact prime_oneHundredFourCX_238531
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 142641539) ^ 71320769 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (2 : ZMod 142641539) ^ 10972426 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (2 : ZMod 142641539) ^ 6201806 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (2 : ZMod 142641539) ^ 598 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourCX_146030803 : Nat.Prime 146030803 := by
  apply lucas_primality 146030803 (3 : ZMod 146030803)
  · rw [← oneHundredFourCXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (24338467, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (24338467, 1)] : List FactorBlock).map factorBlockValue).prod) = 146030803 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFourCX_2
      · exact prime_oneHundredFourCX_3
      · exact prime_oneHundredFourCX_24338467
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 146030803) ^ 73015401 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (3 : ZMod 146030803) ^ 48676934 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (3 : ZMod 146030803) ^ 6 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourCX_166257313 : Nat.Prime 166257313 := by
  apply lucas_primality 166257313 (5 : ZMod 166257313)
  · rw [← oneHundredFourCXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (13, 1), (101, 1), (1319, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (13, 1), (101, 1), (1319, 1)] : List FactorBlock).map factorBlockValue).prod) = 166257313 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourCX_2
      · exact prime_oneHundredFourCX_3
      · exact prime_oneHundredFourCX_13
      · exact prime_oneHundredFourCX_101
      · exact prime_oneHundredFourCX_1319
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 166257313) ^ 83128656 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (5 : ZMod 166257313) ^ 55419104 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (5 : ZMod 166257313) ^ 12789024 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (5 : ZMod 166257313) ^ 1646112 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (5 : ZMod 166257313) ^ 126048 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourCX_170478391 : Nat.Prime 170478391 := by
  apply lucas_primality 170478391 (12 : ZMod 170478391)
  · rw [← oneHundredFourCXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (103, 1), (55171, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (103, 1), (55171, 1)] : List FactorBlock).map factorBlockValue).prod) = 170478391 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourCX_2
      · exact prime_oneHundredFourCX_3
      · exact prime_oneHundredFourCX_5
      · exact prime_oneHundredFourCX_103
      · exact prime_oneHundredFourCX_55171
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (12 : ZMod 170478391) ^ 85239195 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (12 : ZMod 170478391) ^ 56826130 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (12 : ZMod 170478391) ^ 34095678 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (12 : ZMod 170478391) ^ 1655130 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (12 : ZMod 170478391) ^ 3090 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourCX_175690703 : Nat.Prime 175690703 := by
  apply lucas_primality 175690703 (5 : ZMod 175690703)
  · rw [← oneHundredFourCXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (31, 1), (257611, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (31, 1), (257611, 1)] : List FactorBlock).map factorBlockValue).prod) = 175690703 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourCX_2
      · exact prime_oneHundredFourCX_11
      · exact prime_oneHundredFourCX_31
      · exact prime_oneHundredFourCX_257611
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 175690703) ^ 87845351 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (5 : ZMod 175690703) ^ 15971882 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (5 : ZMod 175690703) ^ 5667442 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (5 : ZMod 175690703) ^ 682 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourCX_176475751 : Nat.Prime 176475751 := by
  apply lucas_primality 176475751 (7 : ZMod 176475751)
  · rw [← oneHundredFourCXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 3), (11, 1), (21391, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 3), (11, 1), (21391, 1)] : List FactorBlock).map factorBlockValue).prod) = 176475751 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourCX_2
      · exact prime_oneHundredFourCX_3
      · exact prime_oneHundredFourCX_5
      · exact prime_oneHundredFourCX_11
      · exact prime_oneHundredFourCX_21391
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 176475751) ^ 88237875 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (7 : ZMod 176475751) ^ 58825250 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (7 : ZMod 176475751) ^ 35295150 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (7 : ZMod 176475751) ^ 16043250 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (7 : ZMod 176475751) ^ 8250 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourCX_185423809 : Nat.Prime 185423809 := by
  apply lucas_primality 185423809 (11 : ZMod 185423809)
  · rw [← oneHundredFourCXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 1), (965749, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 1), (965749, 1)] : List FactorBlock).map factorBlockValue).prod) = 185423809 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFourCX_2
      · exact prime_oneHundredFourCX_3
      · exact prime_oneHundredFourCX_965749
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (11 : ZMod 185423809) ^ 92711904 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (11 : ZMod 185423809) ^ 61807936 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (11 : ZMod 185423809) ^ 192 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourCX_203426459 : Nat.Prime 203426459 := by
  apply lucas_primality 203426459 (2 : ZMod 203426459)
  · rw [← oneHundredFourCXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (463, 1), (219683, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (463, 1), (219683, 1)] : List FactorBlock).map factorBlockValue).prod) = 203426459 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFourCX_2
      · exact prime_oneHundredFourCX_463
      · exact prime_oneHundredFourCX_219683
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 203426459) ^ 101713229 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (2 : ZMod 203426459) ^ 439366 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (2 : ZMod 203426459) ^ 926 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourCX_224762081 : Nat.Prime 224762081 := by
  apply lucas_primality 224762081 (6 : ZMod 224762081)
  · rw [← oneHundredFourCXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (5, 1), (1404763, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (5, 1), (1404763, 1)] : List FactorBlock).map factorBlockValue).prod) = 224762081 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFourCX_2
      · exact prime_oneHundredFourCX_5
      · exact prime_oneHundredFourCX_1404763
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (6 : ZMod 224762081) ^ 112381040 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (6 : ZMod 224762081) ^ 44952416 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (6 : ZMod 224762081) ^ 160 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourCX_237863789 : Nat.Prime 237863789 := by
  apply lucas_primality 237863789 (2 : ZMod 237863789)
  · rw [← oneHundredFourCXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (43, 1), (53, 1), (97, 1), (269, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (43, 1), (53, 1), (97, 1), (269, 1)] : List FactorBlock).map factorBlockValue).prod) = 237863789 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourCX_2
      · exact prime_oneHundredFourCX_43
      · exact prime_oneHundredFourCX_53
      · exact prime_oneHundredFourCX_97
      · exact prime_oneHundredFourCX_269
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 237863789) ^ 118931894 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (2 : ZMod 237863789) ^ 5531716 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (2 : ZMod 237863789) ^ 4487996 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (2 : ZMod 237863789) ^ 2452204 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (2 : ZMod 237863789) ^ 884252 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourCX_256811773 : Nat.Prime 256811773 := by
  apply lucas_primality 256811773 (5 : ZMod 256811773)
  · rw [← oneHundredFourCXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 1), (3057283, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 1), (3057283, 1)] : List FactorBlock).map factorBlockValue).prod) = 256811773 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourCX_2
      · exact prime_oneHundredFourCX_3
      · exact prime_oneHundredFourCX_7
      · exact prime_oneHundredFourCX_3057283
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 256811773) ^ 128405886 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (5 : ZMod 256811773) ^ 85603924 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (5 : ZMod 256811773) ^ 36687396 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (5 : ZMod 256811773) ^ 84 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourCX_261250841 : Nat.Prime 261250841 := by
  apply lucas_primality 261250841 (3 : ZMod 261250841)
  · rw [← oneHundredFourCXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (251, 1), (26021, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (251, 1), (26021, 1)] : List FactorBlock).map factorBlockValue).prod) = 261250841 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourCX_2
      · exact prime_oneHundredFourCX_5
      · exact prime_oneHundredFourCX_251
      · exact prime_oneHundredFourCX_26021
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 261250841) ^ 130625420 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (3 : ZMod 261250841) ^ 52250168 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (3 : ZMod 261250841) ^ 1040840 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (3 : ZMod 261250841) ^ 10040 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourCX_269791169 : Nat.Prime 269791169 := by
  apply lucas_primality 269791169 (3 : ZMod 269791169)
  · rw [← oneHundredFourCXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (83, 1), (50789, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (83, 1), (50789, 1)] : List FactorBlock).map factorBlockValue).prod) = 269791169 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFourCX_2
      · exact prime_oneHundredFourCX_83
      · exact prime_oneHundredFourCX_50789
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 269791169) ^ 134895584 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (3 : ZMod 269791169) ^ 3250496 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (3 : ZMod 269791169) ^ 5312 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourCX_273656311 : Nat.Prime 273656311 := by
  apply lucas_primality 273656311 (11 : ZMod 273656311)
  · rw [← oneHundredFourCXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (17, 1), (89, 1), (6029, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (17, 1), (89, 1), (6029, 1)] : List FactorBlock).map factorBlockValue).prod) = 273656311 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourCX_2
      · exact prime_oneHundredFourCX_3
      · exact prime_oneHundredFourCX_5
      · exact prime_oneHundredFourCX_17
      · exact prime_oneHundredFourCX_89
      · exact prime_oneHundredFourCX_6029
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 273656311) ^ 136828155 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (11 : ZMod 273656311) ^ 91218770 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (11 : ZMod 273656311) ^ 54731262 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (11 : ZMod 273656311) ^ 16097430 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (11 : ZMod 273656311) ^ 3074790 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (11 : ZMod 273656311) ^ 45390 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourCX_283800709 : Nat.Prime 283800709 := by
  apply lucas_primality 283800709 (2 : ZMod 283800709)
  · rw [← oneHundredFourCXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (89, 1), (101, 1), (877, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (89, 1), (101, 1), (877, 1)] : List FactorBlock).map factorBlockValue).prod) = 283800709 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourCX_2
      · exact prime_oneHundredFourCX_3
      · exact prime_oneHundredFourCX_89
      · exact prime_oneHundredFourCX_101
      · exact prime_oneHundredFourCX_877
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 283800709) ^ 141900354 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (2 : ZMod 283800709) ^ 94600236 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (2 : ZMod 283800709) ^ 3188772 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (2 : ZMod 283800709) ^ 2809908 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (2 : ZMod 283800709) ^ 323604 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourCX_284376793 : Nat.Prime 284376793 := by
  apply lucas_primality 284376793 (5 : ZMod 284376793)
  · rw [← oneHundredFourCXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (7, 2), (241817, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (7, 2), (241817, 1)] : List FactorBlock).map factorBlockValue).prod) = 284376793 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourCX_2
      · exact prime_oneHundredFourCX_3
      · exact prime_oneHundredFourCX_7
      · exact prime_oneHundredFourCX_241817
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 284376793) ^ 142188396 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (5 : ZMod 284376793) ^ 94792264 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (5 : ZMod 284376793) ^ 40625256 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (5 : ZMod 284376793) ^ 1176 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourCX_295456519 : Nat.Prime 295456519 := by
  apply lucas_primality 295456519 (6 : ZMod 295456519)
  · rw [← oneHundredFourCXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (7, 1), (781631, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (7, 1), (781631, 1)] : List FactorBlock).map factorBlockValue).prod) = 295456519 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourCX_2
      · exact prime_oneHundredFourCX_3
      · exact prime_oneHundredFourCX_7
      · exact prime_oneHundredFourCX_781631
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 295456519) ^ 147728259 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (6 : ZMod 295456519) ^ 98485506 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (6 : ZMod 295456519) ^ 42208074 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (6 : ZMod 295456519) ^ 378 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourCX_349996873 : Nat.Prime 349996873 := by
  apply lucas_primality 349996873 (11 : ZMod 349996873)
  · rw [← oneHundredFourCXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (19, 1), (767537, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (19, 1), (767537, 1)] : List FactorBlock).map factorBlockValue).prod) = 349996873 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourCX_2
      · exact prime_oneHundredFourCX_3
      · exact prime_oneHundredFourCX_19
      · exact prime_oneHundredFourCX_767537
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 349996873) ^ 174998436 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (11 : ZMod 349996873) ^ 116665624 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (11 : ZMod 349996873) ^ 18420888 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (11 : ZMod 349996873) ^ 456 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourCX_429543953 : Nat.Prime 429543953 := by
  apply lucas_primality 429543953 (3 : ZMod 429543953)
  · rw [← oneHundredFourCXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (23, 1), (37, 1), (31547, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (23, 1), (37, 1), (31547, 1)] : List FactorBlock).map factorBlockValue).prod) = 429543953 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourCX_2
      · exact prime_oneHundredFourCX_23
      · exact prime_oneHundredFourCX_37
      · exact prime_oneHundredFourCX_31547
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 429543953) ^ 214771976 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (3 : ZMod 429543953) ^ 18675824 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (3 : ZMod 429543953) ^ 11609296 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (3 : ZMod 429543953) ^ 13616 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourCX_433955323 : Nat.Prime 433955323 := by
  apply lucas_primality 433955323 (3 : ZMod 433955323)
  · rw [← oneHundredFourCXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (24108629, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (24108629, 1)] : List FactorBlock).map factorBlockValue).prod) = 433955323 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFourCX_2
      · exact prime_oneHundredFourCX_3
      · exact prime_oneHundredFourCX_24108629
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 433955323) ^ 216977661 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (3 : ZMod 433955323) ^ 144651774 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (3 : ZMod 433955323) ^ 18 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourCX_440880637 : Nat.Prime 440880637 := by
  apply lucas_primality 440880637 (2 : ZMod 440880637)
  · rw [← oneHundredFourCXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 2), (19, 2), (31, 1), (67, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 2), (19, 2), (31, 1), (67, 1)] : List FactorBlock).map factorBlockValue).prod) = 440880637 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourCX_2
      · exact prime_oneHundredFourCX_3
      · exact prime_oneHundredFourCX_7
      · exact prime_oneHundredFourCX_19
      · exact prime_oneHundredFourCX_31
      · exact prime_oneHundredFourCX_67
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 440880637) ^ 220440318 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (2 : ZMod 440880637) ^ 146960212 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (2 : ZMod 440880637) ^ 62982948 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (2 : ZMod 440880637) ^ 23204244 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (2 : ZMod 440880637) ^ 14221956 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (2 : ZMod 440880637) ^ 6580308 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourCX_455584477 : Nat.Prime 455584477 := by
  apply lucas_primality 455584477 (2 : ZMod 455584477)
  · rw [← oneHundredFourCXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (2879, 1), (13187, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (2879, 1), (13187, 1)] : List FactorBlock).map factorBlockValue).prod) = 455584477 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourCX_2
      · exact prime_oneHundredFourCX_3
      · exact prime_oneHundredFourCX_2879
      · exact prime_oneHundredFourCX_13187
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 455584477) ^ 227792238 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (2 : ZMod 455584477) ^ 151861492 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (2 : ZMod 455584477) ^ 158244 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (2 : ZMod 455584477) ^ 34548 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourCX_465058499 : Nat.Prime 465058499 := by
  apply lucas_primality 465058499 (2 : ZMod 465058499)
  · rw [← oneHundredFourCXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (269, 1), (463, 1), (1867, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (269, 1), (463, 1), (1867, 1)] : List FactorBlock).map factorBlockValue).prod) = 465058499 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourCX_2
      · exact prime_oneHundredFourCX_269
      · exact prime_oneHundredFourCX_463
      · exact prime_oneHundredFourCX_1867
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 465058499) ^ 232529249 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (2 : ZMod 465058499) ^ 1728842 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (2 : ZMod 465058499) ^ 1004446 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (2 : ZMod 465058499) ^ 249094 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourCX_492912293 : Nat.Prime 492912293 := by
  apply lucas_primality 492912293 (2 : ZMod 492912293)
  · rw [← oneHundredFourCXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (173, 1), (712301, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (173, 1), (712301, 1)] : List FactorBlock).map factorBlockValue).prod) = 492912293 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFourCX_2
      · exact prime_oneHundredFourCX_173
      · exact prime_oneHundredFourCX_712301
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 492912293) ^ 246456146 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (2 : ZMod 492912293) ^ 2849204 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (2 : ZMod 492912293) ^ 692 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourCX_514798139 : Nat.Prime 514798139 := by
  apply lucas_primality 514798139 (2 : ZMod 514798139)
  · rw [← oneHundredFourCXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (71, 1), (3625339, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (71, 1), (3625339, 1)] : List FactorBlock).map factorBlockValue).prod) = 514798139 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFourCX_2
      · exact prime_oneHundredFourCX_71
      · exact prime_oneHundredFourCX_3625339
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 514798139) ^ 257399069 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (2 : ZMod 514798139) ^ 7250678 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (2 : ZMod 514798139) ^ 142 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourCX_550210777 : Nat.Prime 550210777 := by
  apply lucas_primality 550210777 (10 : ZMod 550210777)
  · rw [← oneHundredFourCXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (1811, 1), (12659, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (1811, 1), (12659, 1)] : List FactorBlock).map factorBlockValue).prod) = 550210777 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourCX_2
      · exact prime_oneHundredFourCX_3
      · exact prime_oneHundredFourCX_1811
      · exact prime_oneHundredFourCX_12659
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (10 : ZMod 550210777) ^ 275105388 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (10 : ZMod 550210777) ^ 183403592 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (10 : ZMod 550210777) ^ 303816 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (10 : ZMod 550210777) ^ 43464 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourCX_582823067 : Nat.Prime 582823067 := by
  apply lucas_primality 582823067 (2 : ZMod 582823067)
  · rw [← oneHundredFourCXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (127, 1), (327797, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (127, 1), (327797, 1)] : List FactorBlock).map factorBlockValue).prod) = 582823067 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourCX_2
      · exact prime_oneHundredFourCX_7
      · exact prime_oneHundredFourCX_127
      · exact prime_oneHundredFourCX_327797
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 582823067) ^ 291411533 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (2 : ZMod 582823067) ^ 83260438 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (2 : ZMod 582823067) ^ 4589158 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (2 : ZMod 582823067) ^ 1778 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourCX_606209761 : Nat.Prime 606209761 := by
  apply lucas_primality 606209761 (14 : ZMod 606209761)
  · rw [← oneHundredFourCXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 2), (5, 1), (13, 2), (47, 1), (53, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 2), (5, 1), (13, 2), (47, 1), (53, 1)] : List FactorBlock).map factorBlockValue).prod) = 606209761 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourCX_2
      · exact prime_oneHundredFourCX_3
      · exact prime_oneHundredFourCX_5
      · exact prime_oneHundredFourCX_13
      · exact prime_oneHundredFourCX_47
      · exact prime_oneHundredFourCX_53
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (14 : ZMod 606209761) ^ 303104880 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (14 : ZMod 606209761) ^ 202069920 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (14 : ZMod 606209761) ^ 121241952 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (14 : ZMod 606209761) ^ 46631520 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (14 : ZMod 606209761) ^ 12898080 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (14 : ZMod 606209761) ^ 11437920 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourCX_714027719 : Nat.Prime 714027719 := by
  apply lucas_primality 714027719 (11 : ZMod 714027719)
  · rw [← oneHundredFourCXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17203, 1), (20753, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17203, 1), (20753, 1)] : List FactorBlock).map factorBlockValue).prod) = 714027719 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFourCX_2
      · exact prime_oneHundredFourCX_17203
      · exact prime_oneHundredFourCX_20753
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (11 : ZMod 714027719) ^ 357013859 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (11 : ZMod 714027719) ^ 41506 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (11 : ZMod 714027719) ^ 34406 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourCX_718620989 : Nat.Prime 718620989 := by
  apply lucas_primality 718620989 (2 : ZMod 718620989)
  · rw [← oneHundredFourCXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (43, 1), (107, 1), (39047, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (43, 1), (107, 1), (39047, 1)] : List FactorBlock).map factorBlockValue).prod) = 718620989 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourCX_2
      · exact prime_oneHundredFourCX_43
      · exact prime_oneHundredFourCX_107
      · exact prime_oneHundredFourCX_39047
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 718620989) ^ 359310494 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (2 : ZMod 718620989) ^ 16712116 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (2 : ZMod 718620989) ^ 6716084 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (2 : ZMod 718620989) ^ 18404 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourCX_719634431 : Nat.Prime 719634431 := by
  apply lucas_primality 719634431 (19 : ZMod 719634431)
  · rw [← oneHundredFourCXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (71963443, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (71963443, 1)] : List FactorBlock).map factorBlockValue).prod) = 719634431 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFourCX_2
      · exact prime_oneHundredFourCX_5
      · exact prime_oneHundredFourCX_71963443
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (19 : ZMod 719634431) ^ 359817215 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (19 : ZMod 719634431) ^ 143926886 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (19 : ZMod 719634431) ^ 10 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourCX_729682649 : Nat.Prime 729682649 := by
  apply lucas_primality 729682649 (3 : ZMod 729682649)
  · rw [← oneHundredFourCXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (107, 1), (191, 1), (4463, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (107, 1), (191, 1), (4463, 1)] : List FactorBlock).map factorBlockValue).prod) = 729682649 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourCX_2
      · exact prime_oneHundredFourCX_107
      · exact prime_oneHundredFourCX_191
      · exact prime_oneHundredFourCX_4463
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 729682649) ^ 364841324 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (3 : ZMod 729682649) ^ 6819464 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (3 : ZMod 729682649) ^ 3820328 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (3 : ZMod 729682649) ^ 163496 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourCX_794832221 : Nat.Prime 794832221 := by
  apply lucas_primality 794832221 (3 : ZMod 794832221)
  · rw [← oneHundredFourCXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (7, 1), (13, 1), (71, 1), (6151, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (7, 1), (13, 1), (71, 1), (6151, 1)] : List FactorBlock).map factorBlockValue).prod) = 794832221 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourCX_2
      · exact prime_oneHundredFourCX_5
      · exact prime_oneHundredFourCX_7
      · exact prime_oneHundredFourCX_13
      · exact prime_oneHundredFourCX_71
      · exact prime_oneHundredFourCX_6151
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 794832221) ^ 397416110 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (3 : ZMod 794832221) ^ 158966444 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (3 : ZMod 794832221) ^ 113547460 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (3 : ZMod 794832221) ^ 61140940 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (3 : ZMod 794832221) ^ 11194820 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (3 : ZMod 794832221) ^ 129220 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourCX_800821243 : Nat.Prime 800821243 := by
  apply lucas_primality 800821243 (2 : ZMod 800821243)
  · rw [← oneHundredFourCXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 4), (13, 1), (73, 1), (5209, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 4), (13, 1), (73, 1), (5209, 1)] : List FactorBlock).map factorBlockValue).prod) = 800821243 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourCX_2
      · exact prime_oneHundredFourCX_3
      · exact prime_oneHundredFourCX_13
      · exact prime_oneHundredFourCX_73
      · exact prime_oneHundredFourCX_5209
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 800821243) ^ 400410621 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (2 : ZMod 800821243) ^ 266940414 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (2 : ZMod 800821243) ^ 61601634 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (2 : ZMod 800821243) ^ 10970154 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (2 : ZMod 800821243) ^ 153738 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourCX_824071373 : Nat.Prime 824071373 := by
  apply lucas_primality 824071373 (2 : ZMod 824071373)
  · rw [← oneHundredFourCXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (643, 1), (320401, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (643, 1), (320401, 1)] : List FactorBlock).map factorBlockValue).prod) = 824071373 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFourCX_2
      · exact prime_oneHundredFourCX_643
      · exact prime_oneHundredFourCX_320401
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 824071373) ^ 412035686 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (2 : ZMod 824071373) ^ 1281604 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (2 : ZMod 824071373) ^ 2572 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourCX_833975603 : Nat.Prime 833975603 := by
  apply lucas_primality 833975603 (2 : ZMod 833975603)
  · rw [← oneHundredFourCXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (4679, 1), (89119, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (4679, 1), (89119, 1)] : List FactorBlock).map factorBlockValue).prod) = 833975603 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFourCX_2
      · exact prime_oneHundredFourCX_4679
      · exact prime_oneHundredFourCX_89119
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 833975603) ^ 416987801 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (2 : ZMod 833975603) ^ 178238 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (2 : ZMod 833975603) ^ 9358 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourCX_835787389 : Nat.Prime 835787389 := by
  apply lucas_primality 835787389 (10 : ZMod 835787389)
  · rw [← oneHundredFourCXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (17, 1), (43, 1), (95279, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (17, 1), (43, 1), (95279, 1)] : List FactorBlock).map factorBlockValue).prod) = 835787389 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourCX_2
      · exact prime_oneHundredFourCX_3
      · exact prime_oneHundredFourCX_17
      · exact prime_oneHundredFourCX_43
      · exact prime_oneHundredFourCX_95279
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 835787389) ^ 417893694 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (10 : ZMod 835787389) ^ 278595796 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (10 : ZMod 835787389) ^ 49163964 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (10 : ZMod 835787389) ^ 19436916 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (10 : ZMod 835787389) ^ 8772 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourCX_1036932751 : Nat.Prime 1036932751 := by
  apply lucas_primality 1036932751 (6 : ZMod 1036932751)
  · rw [← oneHundredFourCXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 3), (7, 1), (65837, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 3), (7, 1), (65837, 1)] : List FactorBlock).map factorBlockValue).prod) = 1036932751 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourCX_2
      · exact prime_oneHundredFourCX_3
      · exact prime_oneHundredFourCX_5
      · exact prime_oneHundredFourCX_7
      · exact prime_oneHundredFourCX_65837
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 1036932751) ^ 518466375 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (6 : ZMod 1036932751) ^ 345644250 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (6 : ZMod 1036932751) ^ 207386550 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (6 : ZMod 1036932751) ^ 148133250 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (6 : ZMod 1036932751) ^ 15750 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourCX_1179891679 : Nat.Prime 1179891679 := by
  apply lucas_primality 1179891679 (13 : ZMod 1179891679)
  · rw [← oneHundredFourCXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 2), (19, 2), (11117, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 2), (19, 2), (11117, 1)] : List FactorBlock).map factorBlockValue).prod) = 1179891679 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourCX_2
      · exact prime_oneHundredFourCX_3
      · exact prime_oneHundredFourCX_7
      · exact prime_oneHundredFourCX_19
      · exact prime_oneHundredFourCX_11117
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 1179891679) ^ 589945839 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (13 : ZMod 1179891679) ^ 393297226 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (13 : ZMod 1179891679) ^ 168555954 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (13 : ZMod 1179891679) ^ 62099562 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (13 : ZMod 1179891679) ^ 106134 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourCX_1299989947 : Nat.Prime 1299989947 := by
  apply lucas_primality 1299989947 (2 : ZMod 1299989947)
  · rw [← oneHundredFourCXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (23, 1), (1667, 1), (5651, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (23, 1), (1667, 1), (5651, 1)] : List FactorBlock).map factorBlockValue).prod) = 1299989947 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourCX_2
      · exact prime_oneHundredFourCX_3
      · exact prime_oneHundredFourCX_23
      · exact prime_oneHundredFourCX_1667
      · exact prime_oneHundredFourCX_5651
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1299989947) ^ 649994973 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (2 : ZMod 1299989947) ^ 433329982 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (2 : ZMod 1299989947) ^ 56521302 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (2 : ZMod 1299989947) ^ 779838 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (2 : ZMod 1299989947) ^ 230046 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourCX_1377202471 : Nat.Prime 1377202471 := by
  apply lucas_primality 1377202471 (12 : ZMod 1377202471)
  · rw [← oneHundredFourCXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (7, 1), (17, 1), (385771, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (7, 1), (17, 1), (385771, 1)] : List FactorBlock).map factorBlockValue).prod) = 1377202471 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourCX_2
      · exact prime_oneHundredFourCX_3
      · exact prime_oneHundredFourCX_5
      · exact prime_oneHundredFourCX_7
      · exact prime_oneHundredFourCX_17
      · exact prime_oneHundredFourCX_385771
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (12 : ZMod 1377202471) ^ 688601235 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (12 : ZMod 1377202471) ^ 459067490 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (12 : ZMod 1377202471) ^ 275440494 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (12 : ZMod 1377202471) ^ 196743210 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (12 : ZMod 1377202471) ^ 81011910 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (12 : ZMod 1377202471) ^ 3570 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourCX_1382503337 : Nat.Prime 1382503337 := by
  apply lucas_primality 1382503337 (3 : ZMod 1382503337)
  · rw [← oneHundredFourCXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (809, 1), (213613, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (809, 1), (213613, 1)] : List FactorBlock).map factorBlockValue).prod) = 1382503337 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFourCX_2
      · exact prime_oneHundredFourCX_809
      · exact prime_oneHundredFourCX_213613
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 1382503337) ^ 691251668 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (3 : ZMod 1382503337) ^ 1708904 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (3 : ZMod 1382503337) ^ 6472 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourCX_1399940627 : Nat.Prime 1399940627 := by
  apply lucas_primality 1399940627 (2 : ZMod 1399940627)
  · rw [← oneHundredFourCXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (167, 1), (598777, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (167, 1), (598777, 1)] : List FactorBlock).map factorBlockValue).prod) = 1399940627 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourCX_2
      · exact prime_oneHundredFourCX_7
      · exact prime_oneHundredFourCX_167
      · exact prime_oneHundredFourCX_598777
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1399940627) ^ 699970313 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (2 : ZMod 1399940627) ^ 199991518 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (2 : ZMod 1399940627) ^ 8382878 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (2 : ZMod 1399940627) ^ 2338 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourCX_1437241979 : Nat.Prime 1437241979 := by
  apply lucas_primality 1437241979 (2 : ZMod 1437241979)
  · rw [← oneHundredFourCXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (718620989, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (718620989, 1)] : List FactorBlock).map factorBlockValue).prod) = 1437241979 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredFourCX_2
      · exact prime_oneHundredFourCX_718620989
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 1437241979) ^ 718620989 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (2 : ZMod 1437241979) ^ 2 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourCX_1593184889 : Nat.Prime 1593184889 := by
  apply lucas_primality 1593184889 (3 : ZMod 1593184889)
  · rw [← oneHundredFourCXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (41, 1), (4857271, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (41, 1), (4857271, 1)] : List FactorBlock).map factorBlockValue).prod) = 1593184889 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFourCX_2
      · exact prime_oneHundredFourCX_41
      · exact prime_oneHundredFourCX_4857271
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 1593184889) ^ 796592444 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (3 : ZMod 1593184889) ^ 38858168 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (3 : ZMod 1593184889) ^ 328 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourCX_1648142747 : Nat.Prime 1648142747 := by
  apply lucas_primality 1648142747 (2 : ZMod 1648142747)
  · rw [← oneHundredFourCXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (824071373, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (824071373, 1)] : List FactorBlock).map factorBlockValue).prod) = 1648142747 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredFourCX_2
      · exact prime_oneHundredFourCX_824071373
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 1648142747) ^ 824071373 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (2 : ZMod 1648142747) ^ 2 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourCX_1855108091 : Nat.Prime 1855108091 := by
  apply lucas_primality 1855108091 (10 : ZMod 1855108091)
  · rw [← oneHundredFourCXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (11, 1), (59, 1), (285841, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (11, 1), (59, 1), (285841, 1)] : List FactorBlock).map factorBlockValue).prod) = 1855108091 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourCX_2
      · exact prime_oneHundredFourCX_5
      · exact prime_oneHundredFourCX_11
      · exact prime_oneHundredFourCX_59
      · exact prime_oneHundredFourCX_285841
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 1855108091) ^ 927554045 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (10 : ZMod 1855108091) ^ 371021618 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (10 : ZMod 1855108091) ^ 168646190 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (10 : ZMod 1855108091) ^ 31442510 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (10 : ZMod 1855108091) ^ 6490 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourCX_1995587999 : Nat.Prime 1995587999 := by
  apply lucas_primality 1995587999 (11 : ZMod 1995587999)
  · rw [← oneHundredFourCXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (41, 1), (24336439, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (41, 1), (24336439, 1)] : List FactorBlock).map factorBlockValue).prod) = 1995587999 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFourCX_2
      · exact prime_oneHundredFourCX_41
      · exact prime_oneHundredFourCX_24336439
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (11 : ZMod 1995587999) ^ 997793999 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (11 : ZMod 1995587999) ^ 48672878 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (11 : ZMod 1995587999) ^ 82 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourCX_2318099881 : Nat.Prime 2318099881 := by
  apply lucas_primality 2318099881 (7 : ZMod 2318099881)
  · rw [← oneHundredFourCXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 1), (349, 1), (55351, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 1), (349, 1), (55351, 1)] : List FactorBlock).map factorBlockValue).prod) = 2318099881 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourCX_2
      · exact prime_oneHundredFourCX_3
      · exact prime_oneHundredFourCX_5
      · exact prime_oneHundredFourCX_349
      · exact prime_oneHundredFourCX_55351
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 2318099881) ^ 1159049940 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (7 : ZMod 2318099881) ^ 772699960 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (7 : ZMod 2318099881) ^ 463619976 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (7 : ZMod 2318099881) ^ 6642120 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (7 : ZMod 2318099881) ^ 41880 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourCX_2416168199 : Nat.Prime 2416168199 := by
  apply lucas_primality 2416168199 (7 : ZMod 2416168199)
  · rw [← oneHundredFourCXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (47, 1), (71, 1), (362027, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (47, 1), (71, 1), (362027, 1)] : List FactorBlock).map factorBlockValue).prod) = 2416168199 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourCX_2
      · exact prime_oneHundredFourCX_47
      · exact prime_oneHundredFourCX_71
      · exact prime_oneHundredFourCX_362027
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 2416168199) ^ 1208084099 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (7 : ZMod 2416168199) ^ 51407834 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (7 : ZMod 2416168199) ^ 34030538 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (7 : ZMod 2416168199) ^ 6674 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourCX_3119242051 : Nat.Prime 3119242051 := by
  apply lucas_primality 3119242051 (3 : ZMod 3119242051)
  · rw [← oneHundredFourCXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 2), (6931649, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 2), (6931649, 1)] : List FactorBlock).map factorBlockValue).prod) = 3119242051 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourCX_2
      · exact prime_oneHundredFourCX_3
      · exact prime_oneHundredFourCX_5
      · exact prime_oneHundredFourCX_6931649
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 3119242051) ^ 1559621025 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (3 : ZMod 3119242051) ^ 1039747350 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (3 : ZMod 3119242051) ^ 623848410 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (3 : ZMod 3119242051) ^ 450 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourCX_3496915489 : Nat.Prime 3496915489 := by
  apply lucas_primality 3496915489 (23 : ZMod 3496915489)
  · rw [← oneHundredFourCXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (11, 2), (43, 1), (7001, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (11, 2), (43, 1), (7001, 1)] : List FactorBlock).map factorBlockValue).prod) = 3496915489 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourCX_2
      · exact prime_oneHundredFourCX_3
      · exact prime_oneHundredFourCX_11
      · exact prime_oneHundredFourCX_43
      · exact prime_oneHundredFourCX_7001
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (23 : ZMod 3496915489) ^ 1748457744 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (23 : ZMod 3496915489) ^ 1165638496 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (23 : ZMod 3496915489) ^ 317901408 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (23 : ZMod 3496915489) ^ 81323616 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (23 : ZMod 3496915489) ^ 499488 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourCX_5509144847 : Nat.Prime 5509144847 := by
  apply lucas_primality 5509144847 (5 : ZMod 5509144847)
  · rw [← oneHundredFourCXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (2593, 1), (1062311, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (2593, 1), (1062311, 1)] : List FactorBlock).map factorBlockValue).prod) = 5509144847 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFourCX_2
      · exact prime_oneHundredFourCX_2593
      · exact prime_oneHundredFourCX_1062311
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 5509144847) ^ 2754572423 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (5 : ZMod 5509144847) ^ 2124622 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (5 : ZMod 5509144847) ^ 5186 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourCX_5765387687 : Nat.Prime 5765387687 := by
  apply lucas_primality 5765387687 (5 : ZMod 5765387687)
  · rw [← oneHundredFourCXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (631, 1), (4568453, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (631, 1), (4568453, 1)] : List FactorBlock).map factorBlockValue).prod) = 5765387687 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFourCX_2
      · exact prime_oneHundredFourCX_631
      · exact prime_oneHundredFourCX_4568453
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 5765387687) ^ 2882693843 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (5 : ZMod 5765387687) ^ 9136906 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (5 : ZMod 5765387687) ^ 1262 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourCX_6037638679 : Nat.Prime 6037638679 := by
  apply lucas_primality 6037638679 (3 : ZMod 6037638679)
  · rw [← oneHundredFourCXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (31, 1), (10820141, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (31, 1), (10820141, 1)] : List FactorBlock).map factorBlockValue).prod) = 6037638679 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourCX_2
      · exact prime_oneHundredFourCX_3
      · exact prime_oneHundredFourCX_31
      · exact prime_oneHundredFourCX_10820141
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 6037638679) ^ 3018819339 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (3 : ZMod 6037638679) ^ 2012546226 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (3 : ZMod 6037638679) ^ 194762538 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (3 : ZMod 6037638679) ^ 558 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourCX_6258102553 : Nat.Prime 6258102553 := by
  apply lucas_primality 6258102553 (7 : ZMod 6258102553)
  · rw [← oneHundredFourCXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 3), (13, 1), (79, 1), (28211, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 3), (13, 1), (79, 1), (28211, 1)] : List FactorBlock).map factorBlockValue).prod) = 6258102553 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourCX_2
      · exact prime_oneHundredFourCX_3
      · exact prime_oneHundredFourCX_13
      · exact prime_oneHundredFourCX_79
      · exact prime_oneHundredFourCX_28211
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 6258102553) ^ 3129051276 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (7 : ZMod 6258102553) ^ 2086034184 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (7 : ZMod 6258102553) ^ 481392504 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (7 : ZMod 6258102553) ^ 79216488 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (7 : ZMod 6258102553) ^ 221832 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourCX_6502467331 : Nat.Prime 6502467331 := by
  apply lucas_primality 6502467331 (2 : ZMod 6502467331)
  · rw [← oneHundredFourCXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (72249637, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (72249637, 1)] : List FactorBlock).map factorBlockValue).prod) = 6502467331 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourCX_2
      · exact prime_oneHundredFourCX_3
      · exact prime_oneHundredFourCX_5
      · exact prime_oneHundredFourCX_72249637
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 6502467331) ^ 3251233665 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (2 : ZMod 6502467331) ^ 2167489110 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (2 : ZMod 6502467331) ^ 1300493466 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (2 : ZMod 6502467331) ^ 90 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourCX_6591727349 : Nat.Prime 6591727349 := by
  apply lucas_primality 6591727349 (2 : ZMod 6591727349)
  · rw [← oneHundredFourCXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (26183, 1), (62939, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (26183, 1), (62939, 1)] : List FactorBlock).map factorBlockValue).prod) = 6591727349 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFourCX_2
      · exact prime_oneHundredFourCX_26183
      · exact prime_oneHundredFourCX_62939
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 6591727349) ^ 3295863674 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (2 : ZMod 6591727349) ^ 251756 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (2 : ZMod 6591727349) ^ 104732 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourCX_6998309863 : Nat.Prime 6998309863 := by
  apply lucas_primality 6998309863 (3 : ZMod 6998309863)
  · rw [← oneHundredFourCXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (17, 1), (19, 1), (67, 1), (53897, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (17, 1), (19, 1), (67, 1), (53897, 1)] : List FactorBlock).map factorBlockValue).prod) = 6998309863 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourCX_2
      · exact prime_oneHundredFourCX_3
      · exact prime_oneHundredFourCX_17
      · exact prime_oneHundredFourCX_19
      · exact prime_oneHundredFourCX_67
      · exact prime_oneHundredFourCX_53897
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 6998309863) ^ 3499154931 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (3 : ZMod 6998309863) ^ 2332769954 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (3 : ZMod 6998309863) ^ 411665286 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (3 : ZMod 6998309863) ^ 368332098 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (3 : ZMod 6998309863) ^ 104452386 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (3 : ZMod 6998309863) ^ 129846 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourCX_7453849253 : Nat.Prime 7453849253 := by
  apply lucas_primality 7453849253 (2 : ZMod 7453849253)
  · rw [← oneHundredFourCXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (59, 1), (73, 1), (432659, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (59, 1), (73, 1), (432659, 1)] : List FactorBlock).map factorBlockValue).prod) = 7453849253 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourCX_2
      · exact prime_oneHundredFourCX_59
      · exact prime_oneHundredFourCX_73
      · exact prime_oneHundredFourCX_432659
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 7453849253) ^ 3726924626 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (2 : ZMod 7453849253) ^ 126336428 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (2 : ZMod 7453849253) ^ 102107524 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (2 : ZMod 7453849253) ^ 17228 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourCX_7460903881 : Nat.Prime 7460903881 := by
  apply lucas_primality 7460903881 (11 : ZMod 7460903881)
  · rw [← oneHundredFourCXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (5, 1), (103, 1), (201211, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (5, 1), (103, 1), (201211, 1)] : List FactorBlock).map factorBlockValue).prod) = 7460903881 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourCX_2
      · exact prime_oneHundredFourCX_3
      · exact prime_oneHundredFourCX_5
      · exact prime_oneHundredFourCX_103
      · exact prime_oneHundredFourCX_201211
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 7460903881) ^ 3730451940 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (11 : ZMod 7460903881) ^ 2486967960 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (11 : ZMod 7460903881) ^ 1492180776 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (11 : ZMod 7460903881) ^ 72435960 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (11 : ZMod 7460903881) ^ 37080 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourCX_9257508937 : Nat.Prime 9257508937 := by
  apply lucas_primality 9257508937 (5 : ZMod 9257508937)
  · rw [← oneHundredFourCXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (13, 1), (9890501, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (13, 1), (9890501, 1)] : List FactorBlock).map factorBlockValue).prod) = 9257508937 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourCX_2
      · exact prime_oneHundredFourCX_3
      · exact prime_oneHundredFourCX_13
      · exact prime_oneHundredFourCX_9890501
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 9257508937) ^ 4628754468 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (5 : ZMod 9257508937) ^ 3085836312 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (5 : ZMod 9257508937) ^ 712116072 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (5 : ZMod 9257508937) ^ 936 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourCX_9301169981 : Nat.Prime 9301169981 := by
  apply lucas_primality 9301169981 (2 : ZMod 9301169981)
  · rw [← oneHundredFourCXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (465058499, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (465058499, 1)] : List FactorBlock).map factorBlockValue).prod) = 9301169981 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFourCX_2
      · exact prime_oneHundredFourCX_5
      · exact prime_oneHundredFourCX_465058499
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 9301169981) ^ 4650584990 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (2 : ZMod 9301169981) ^ 1860233996 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (2 : ZMod 9301169981) ^ 20 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourCX_10018853863 : Nat.Prime 10018853863 := by
  apply lucas_primality 10018853863 (3 : ZMod 10018853863)
  · rw [← oneHundredFourCXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (19, 1), (2741, 1), (32063, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (19, 1), (2741, 1), (32063, 1)] : List FactorBlock).map factorBlockValue).prod) = 10018853863 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourCX_2
      · exact prime_oneHundredFourCX_3
      · exact prime_oneHundredFourCX_19
      · exact prime_oneHundredFourCX_2741
      · exact prime_oneHundredFourCX_32063
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 10018853863) ^ 5009426931 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (3 : ZMod 10018853863) ^ 3339617954 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (3 : ZMod 10018853863) ^ 527308098 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (3 : ZMod 10018853863) ^ 3655182 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (3 : ZMod 10018853863) ^ 312474 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourCX_10030579093 : Nat.Prime 10030579093 := by
  apply lucas_primality 10030579093 (7 : ZMod 10030579093)
  · rw [← oneHundredFourCXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (263, 1), (1059419, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (263, 1), (1059419, 1)] : List FactorBlock).map factorBlockValue).prod) = 10030579093 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourCX_2
      · exact prime_oneHundredFourCX_3
      · exact prime_oneHundredFourCX_263
      · exact prime_oneHundredFourCX_1059419
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 10030579093) ^ 5015289546 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (7 : ZMod 10030579093) ^ 3343526364 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (7 : ZMod 10030579093) ^ 38139084 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (7 : ZMod 10030579093) ^ 9468 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourCX_11161612591 : Nat.Prime 11161612591 := by
  apply lucas_primality 11161612591 (15 : ZMod 11161612591)
  · rw [← oneHundredFourCXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (7213, 1), (51581, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (7213, 1), (51581, 1)] : List FactorBlock).map factorBlockValue).prod) = 11161612591 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourCX_2
      · exact prime_oneHundredFourCX_3
      · exact prime_oneHundredFourCX_5
      · exact prime_oneHundredFourCX_7213
      · exact prime_oneHundredFourCX_51581
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (15 : ZMod 11161612591) ^ 5580806295 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (15 : ZMod 11161612591) ^ 3720537530 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (15 : ZMod 11161612591) ^ 2232322518 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (15 : ZMod 11161612591) ^ 1547430 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (15 : ZMod 11161612591) ^ 216390 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourCX_12886318591 : Nat.Prime 12886318591 := by
  apply lucas_primality 12886318591 (6 : ZMod 12886318591)
  · rw [← oneHundredFourCXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (429543953, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (429543953, 1)] : List FactorBlock).map factorBlockValue).prod) = 12886318591 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourCX_2
      · exact prime_oneHundredFourCX_3
      · exact prime_oneHundredFourCX_5
      · exact prime_oneHundredFourCX_429543953
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 12886318591) ^ 6443159295 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (6 : ZMod 12886318591) ^ 4295439530 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (6 : ZMod 12886318591) ^ 2577263718 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (6 : ZMod 12886318591) ^ 30 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourCX_14026441951 : Nat.Prime 14026441951 := by
  apply lucas_primality 14026441951 (3 : ZMod 14026441951)
  · rw [← oneHundredFourCXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 4), (5, 2), (3463319, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 4), (5, 2), (3463319, 1)] : List FactorBlock).map factorBlockValue).prod) = 14026441951 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourCX_2
      · exact prime_oneHundredFourCX_3
      · exact prime_oneHundredFourCX_5
      · exact prime_oneHundredFourCX_3463319
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 14026441951) ^ 7013220975 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (3 : ZMod 14026441951) ^ 4675480650 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (3 : ZMod 14026441951) ^ 2805288390 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (3 : ZMod 14026441951) ^ 4050 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourCX_14663412833 : Nat.Prime 14663412833 := by
  apply lucas_primality 14663412833 (3 : ZMod 14663412833)
  · rw [← oneHundredFourCXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (17, 1), (26954803, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (17, 1), (26954803, 1)] : List FactorBlock).map factorBlockValue).prod) = 14663412833 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFourCX_2
      · exact prime_oneHundredFourCX_17
      · exact prime_oneHundredFourCX_26954803
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 14663412833) ^ 7331706416 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (3 : ZMod 14663412833) ^ 862553696 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (3 : ZMod 14663412833) ^ 544 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourCX_14750067271 : Nat.Prime 14750067271 := by
  apply lucas_primality 14750067271 (15 : ZMod 14750067271)
  · rw [← oneHundredFourCXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (19, 1), (101, 1), (256211, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (19, 1), (101, 1), (256211, 1)] : List FactorBlock).map factorBlockValue).prod) = 14750067271 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourCX_2
      · exact prime_oneHundredFourCX_3
      · exact prime_oneHundredFourCX_5
      · exact prime_oneHundredFourCX_19
      · exact prime_oneHundredFourCX_101
      · exact prime_oneHundredFourCX_256211
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (15 : ZMod 14750067271) ^ 7375033635 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (15 : ZMod 14750067271) ^ 4916689090 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (15 : ZMod 14750067271) ^ 2950013454 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (15 : ZMod 14750067271) ^ 776319330 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (15 : ZMod 14750067271) ^ 146040270 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (15 : ZMod 14750067271) ^ 57570 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourCX_16377364331 : Nat.Prime 16377364331 := by
  apply lucas_primality 16377364331 (6 : ZMod 16377364331)
  · rw [← oneHundredFourCXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (193, 1), (8485681, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (193, 1), (8485681, 1)] : List FactorBlock).map factorBlockValue).prod) = 16377364331 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourCX_2
      · exact prime_oneHundredFourCX_5
      · exact prime_oneHundredFourCX_193
      · exact prime_oneHundredFourCX_8485681
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 16377364331) ^ 8188682165 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (6 : ZMod 16377364331) ^ 3275472866 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (6 : ZMod 16377364331) ^ 84856810 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (6 : ZMod 16377364331) ^ 1930 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourCX_16514973161 : Nat.Prime 16514973161 := by
  apply lucas_primality 16514973161 (3 : ZMod 16514973161)
  · rw [← oneHundredFourCXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (7, 1), (349, 1), (169003, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (7, 1), (349, 1), (169003, 1)] : List FactorBlock).map factorBlockValue).prod) = 16514973161 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourCX_2
      · exact prime_oneHundredFourCX_5
      · exact prime_oneHundredFourCX_7
      · exact prime_oneHundredFourCX_349
      · exact prime_oneHundredFourCX_169003
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 16514973161) ^ 8257486580 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (3 : ZMod 16514973161) ^ 3302994632 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (3 : ZMod 16514973161) ^ 2359281880 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (3 : ZMod 16514973161) ^ 47320840 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (3 : ZMod 16514973161) ^ 97720 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourCX_17746879697 : Nat.Prime 17746879697 := by
  apply lucas_primality 17746879697 (3 : ZMod 17746879697)
  · rw [← oneHundredFourCXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (7, 1), (13, 1), (12188791, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (7, 1), (13, 1), (12188791, 1)] : List FactorBlock).map factorBlockValue).prod) = 17746879697 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourCX_2
      · exact prime_oneHundredFourCX_7
      · exact prime_oneHundredFourCX_13
      · exact prime_oneHundredFourCX_12188791
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 17746879697) ^ 8873439848 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (3 : ZMod 17746879697) ^ 2535268528 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (3 : ZMod 17746879697) ^ 1365144592 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (3 : ZMod 17746879697) ^ 1456 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourCX_21200988013 : Nat.Prime 21200988013 := by
  apply lucas_primality 21200988013 (2 : ZMod 21200988013)
  · rw [← oneHundredFourCXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (37, 1), (1103, 1), (43291, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (37, 1), (1103, 1), (43291, 1)] : List FactorBlock).map factorBlockValue).prod) = 21200988013 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourCX_2
      · exact prime_oneHundredFourCX_3
      · exact prime_oneHundredFourCX_37
      · exact prime_oneHundredFourCX_1103
      · exact prime_oneHundredFourCX_43291
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 21200988013) ^ 10600494006 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (2 : ZMod 21200988013) ^ 7066996004 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (2 : ZMod 21200988013) ^ 572999676 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (2 : ZMod 21200988013) ^ 19221204 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (2 : ZMod 21200988013) ^ 489732 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourCX_22292713759 : Nat.Prime 22292713759 := by
  apply lucas_primality 22292713759 (7 : ZMod 22292713759)
  · rw [← oneHundredFourCXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 2), (75825557, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 2), (75825557, 1)] : List FactorBlock).map factorBlockValue).prod) = 22292713759 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourCX_2
      · exact prime_oneHundredFourCX_3
      · exact prime_oneHundredFourCX_7
      · exact prime_oneHundredFourCX_75825557
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 22292713759) ^ 11146356879 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (7 : ZMod 22292713759) ^ 7430904586 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (7 : ZMod 22292713759) ^ 3184673394 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (7 : ZMod 22292713759) ^ 294 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourCX_25198931287 : Nat.Prime 25198931287 := by
  apply lucas_primality 25198931287 (3 : ZMod 25198931287)
  · rw [← oneHundredFourCXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (1399940627, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (1399940627, 1)] : List FactorBlock).map factorBlockValue).prod) = 25198931287 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFourCX_2
      · exact prime_oneHundredFourCX_3
      · exact prime_oneHundredFourCX_1399940627
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 25198931287) ^ 12599465643 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (3 : ZMod 25198931287) ^ 8399643762 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (3 : ZMod 25198931287) ^ 18 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourCX_29335293089 : Nat.Prime 29335293089 := by
  apply lucas_primality 29335293089 (3 : ZMod 29335293089)
  · rw [← oneHundredFourCXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (53, 1), (17296753, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (53, 1), (17296753, 1)] : List FactorBlock).map factorBlockValue).prod) = 29335293089 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFourCX_2
      · exact prime_oneHundredFourCX_53
      · exact prime_oneHundredFourCX_17296753
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 29335293089) ^ 14667646544 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (3 : ZMod 29335293089) ^ 553496096 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (3 : ZMod 29335293089) ^ 1696 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourCX_32754728663 : Nat.Prime 32754728663 := by
  apply lucas_primality 32754728663 (5 : ZMod 32754728663)
  · rw [← oneHundredFourCXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (16377364331, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (16377364331, 1)] : List FactorBlock).map factorBlockValue).prod) = 32754728663 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredFourCX_2
      · exact prime_oneHundredFourCX_16377364331
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 32754728663) ^ 16377364331 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (5 : ZMod 32754728663) ^ 2 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourCX_33020716279 : Nat.Prime 33020716279 := by
  apply lucas_primality 33020716279 (3 : ZMod 33020716279)
  · rw [← oneHundredFourCXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (12821, 1), (39023, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (12821, 1), (39023, 1)] : List FactorBlock).map factorBlockValue).prod) = 33020716279 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourCX_2
      · exact prime_oneHundredFourCX_3
      · exact prime_oneHundredFourCX_11
      · exact prime_oneHundredFourCX_12821
      · exact prime_oneHundredFourCX_39023
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 33020716279) ^ 16510358139 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (3 : ZMod 33020716279) ^ 11006905426 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (3 : ZMod 33020716279) ^ 3001883298 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (3 : ZMod 33020716279) ^ 2575518 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (3 : ZMod 33020716279) ^ 846186 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourCX_34387031947 : Nat.Prime 34387031947 := by
  apply lucas_primality 34387031947 (3 : ZMod 34387031947)
  · rw [← oneHundredFourCXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (66089, 1), (86719, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (66089, 1), (86719, 1)] : List FactorBlock).map factorBlockValue).prod) = 34387031947 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourCX_2
      · exact prime_oneHundredFourCX_3
      · exact prime_oneHundredFourCX_66089
      · exact prime_oneHundredFourCX_86719
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 34387031947) ^ 17193515973 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (3 : ZMod 34387031947) ^ 11462343982 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (3 : ZMod 34387031947) ^ 520314 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (3 : ZMod 34387031947) ^ 396534 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourCX_34592326123 : Nat.Prime 34592326123 := by
  apply lucas_primality 34592326123 (2 : ZMod 34592326123)
  · rw [← oneHundredFourCXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5765387687, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5765387687, 1)] : List FactorBlock).map factorBlockValue).prod) = 34592326123 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFourCX_2
      · exact prime_oneHundredFourCX_3
      · exact prime_oneHundredFourCX_5765387687
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 34592326123) ^ 17296163061 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (2 : ZMod 34592326123) ^ 11530775374 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (2 : ZMod 34592326123) ^ 6 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourCX_34671681157 : Nat.Prime 34671681157 := by
  apply lucas_primality 34671681157 (2 : ZMod 34671681157)
  · rw [← oneHundredFourCXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 1), (19, 1), (21724111, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 1), (19, 1), (21724111, 1)] : List FactorBlock).map factorBlockValue).prod) = 34671681157 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourCX_2
      · exact prime_oneHundredFourCX_3
      · exact prime_oneHundredFourCX_7
      · exact prime_oneHundredFourCX_19
      · exact prime_oneHundredFourCX_21724111
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 34671681157) ^ 17335840578 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (2 : ZMod 34671681157) ^ 11557227052 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (2 : ZMod 34671681157) ^ 4953097308 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (2 : ZMod 34671681157) ^ 1824825324 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (2 : ZMod 34671681157) ^ 1596 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourCX_35006273453 : Nat.Prime 35006273453 := by
  apply lucas_primality 35006273453 (2 : ZMod 35006273453)
  · rw [← oneHundredFourCXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (17, 1), (514798139, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (17, 1), (514798139, 1)] : List FactorBlock).map factorBlockValue).prod) = 35006273453 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFourCX_2
      · exact prime_oneHundredFourCX_17
      · exact prime_oneHundredFourCX_514798139
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 35006273453) ^ 17503136726 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (2 : ZMod 35006273453) ^ 2059192556 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (2 : ZMod 35006273453) ^ 68 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourCX_39764973961 : Nat.Prime 39764973961 := by
  apply lucas_primality 39764973961 (7 : ZMod 39764973961)
  · rw [← oneHundredFourCXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (5, 1), (110458261, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (5, 1), (110458261, 1)] : List FactorBlock).map factorBlockValue).prod) = 39764973961 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourCX_2
      · exact prime_oneHundredFourCX_3
      · exact prime_oneHundredFourCX_5
      · exact prime_oneHundredFourCX_110458261
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 39764973961) ^ 19882486980 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (7 : ZMod 39764973961) ^ 13254991320 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (7 : ZMod 39764973961) ^ 7952994792 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (7 : ZMod 39764973961) ^ 360 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourCX_47612670971 : Nat.Prime 47612670971 := by
  apply lucas_primality 47612670971 (2 : ZMod 47612670971)
  · rw [← oneHundredFourCXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (13411, 1), (355027, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (13411, 1), (355027, 1)] : List FactorBlock).map factorBlockValue).prod) = 47612670971 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourCX_2
      · exact prime_oneHundredFourCX_5
      · exact prime_oneHundredFourCX_13411
      · exact prime_oneHundredFourCX_355027
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 47612670971) ^ 23806335485 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (2 : ZMod 47612670971) ^ 9522534194 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (2 : ZMod 47612670971) ^ 3550270 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (2 : ZMod 47612670971) ^ 134110 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourCX_58670586179 : Nat.Prime 58670586179 := by
  apply lucas_primality 58670586179 (2 : ZMod 58670586179)
  · rw [← oneHundredFourCXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (29335293089, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (29335293089, 1)] : List FactorBlock).map factorBlockValue).prod) = 58670586179 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredFourCX_2
      · exact prime_oneHundredFourCX_29335293089
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 58670586179) ^ 29335293089 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (2 : ZMod 58670586179) ^ 2 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourCX_65207015611 : Nat.Prime 65207015611 := by
  apply lucas_primality 65207015611 (10 : ZMod 65207015611)
  · rw [← oneHundredFourCXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (11, 1), (19, 1), (10399843, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (11, 1), (19, 1), (10399843, 1)] : List FactorBlock).map factorBlockValue).prod) = 65207015611 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourCX_2
      · exact prime_oneHundredFourCX_3
      · exact prime_oneHundredFourCX_5
      · exact prime_oneHundredFourCX_11
      · exact prime_oneHundredFourCX_19
      · exact prime_oneHundredFourCX_10399843
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 65207015611) ^ 32603507805 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (10 : ZMod 65207015611) ^ 21735671870 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (10 : ZMod 65207015611) ^ 13041403122 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (10 : ZMod 65207015611) ^ 5927910510 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (10 : ZMod 65207015611) ^ 3431948190 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (10 : ZMod 65207015611) ^ 6270 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourCX_72621713963 : Nat.Prime 72621713963 := by
  apply lucas_primality 72621713963 (5 : ZMod 72621713963)
  · rw [← oneHundredFourCXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (37, 1), (2131, 1), (65789, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (37, 1), (2131, 1), (65789, 1)] : List FactorBlock).map factorBlockValue).prod) = 72621713963 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourCX_2
      · exact prime_oneHundredFourCX_7
      · exact prime_oneHundredFourCX_37
      · exact prime_oneHundredFourCX_2131
      · exact prime_oneHundredFourCX_65789
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 72621713963) ^ 36310856981 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (5 : ZMod 72621713963) ^ 10374530566 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (5 : ZMod 72621713963) ^ 1962749026 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (5 : ZMod 72621713963) ^ 34078702 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (5 : ZMod 72621713963) ^ 1103858 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourCX_73845961043 : Nat.Prime 73845961043 := by
  apply lucas_primality 73845961043 (2 : ZMod 73845961043)
  · rw [← oneHundredFourCXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (83, 1), (63550741, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (83, 1), (63550741, 1)] : List FactorBlock).map factorBlockValue).prod) = 73845961043 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourCX_2
      · exact prime_oneHundredFourCX_7
      · exact prime_oneHundredFourCX_83
      · exact prime_oneHundredFourCX_63550741
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 73845961043) ^ 36922980521 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (2 : ZMod 73845961043) ^ 10549423006 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (2 : ZMod 73845961043) ^ 889710374 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (2 : ZMod 73845961043) ^ 1162 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourCX_73950312193 : Nat.Prime 73950312193 := by
  apply lucas_primality 73950312193 (5 : ZMod 73950312193)
  · rw [← oneHundredFourCXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 8), (3, 1), (293, 1), (328633, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 8), (3, 1), (293, 1), (328633, 1)] : List FactorBlock).map factorBlockValue).prod) = 73950312193 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourCX_2
      · exact prime_oneHundredFourCX_3
      · exact prime_oneHundredFourCX_293
      · exact prime_oneHundredFourCX_328633
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 73950312193) ^ 36975156096 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (5 : ZMod 73950312193) ^ 24650104064 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (5 : ZMod 73950312193) ^ 252390144 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (5 : ZMod 73950312193) ^ 225024 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourCX_83456486219 : Nat.Prime 83456486219 := by
  apply lucas_primality 83456486219 (2 : ZMod 83456486219)
  · rw [← oneHundredFourCXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (659, 1), (673, 1), (13441, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (659, 1), (673, 1), (13441, 1)] : List FactorBlock).map factorBlockValue).prod) = 83456486219 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourCX_2
      · exact prime_oneHundredFourCX_7
      · exact prime_oneHundredFourCX_659
      · exact prime_oneHundredFourCX_673
      · exact prime_oneHundredFourCX_13441
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 83456486219) ^ 41728243109 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (2 : ZMod 83456486219) ^ 11922355174 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (2 : ZMod 83456486219) ^ 126641102 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (2 : ZMod 83456486219) ^ 124006666 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (2 : ZMod 83456486219) ^ 6209098 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourCX_86923581623 : Nat.Prime 86923581623 := by
  apply lucas_primality 86923581623 (5 : ZMod 86923581623)
  · rw [← oneHundredFourCXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (16651, 1), (2610161, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (16651, 1), (2610161, 1)] : List FactorBlock).map factorBlockValue).prod) = 86923581623 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFourCX_2
      · exact prime_oneHundredFourCX_16651
      · exact prime_oneHundredFourCX_2610161
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 86923581623) ^ 43461790811 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (5 : ZMod 86923581623) ^ 5220322 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (5 : ZMod 86923581623) ^ 33302 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourCX_87239226703 : Nat.Prime 87239226703 := by
  apply lucas_primality 87239226703 (3 : ZMod 87239226703)
  · rw [← oneHundredFourCXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (109, 1), (10781, 1), (12373, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (109, 1), (10781, 1), (12373, 1)] : List FactorBlock).map factorBlockValue).prod) = 87239226703 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourCX_2
      · exact prime_oneHundredFourCX_3
      · exact prime_oneHundredFourCX_109
      · exact prime_oneHundredFourCX_10781
      · exact prime_oneHundredFourCX_12373
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 87239226703) ^ 43619613351 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (3 : ZMod 87239226703) ^ 29079742234 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (3 : ZMod 87239226703) ^ 800359878 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (3 : ZMod 87239226703) ^ 8091942 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (3 : ZMod 87239226703) ^ 7050774 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourCX_90915292669 : Nat.Prime 90915292669 := by
  apply lucas_primality 90915292669 (2 : ZMod 90915292669)
  · rw [← oneHundredFourCXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (29, 1), (261250841, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (29, 1), (261250841, 1)] : List FactorBlock).map factorBlockValue).prod) = 90915292669 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourCX_2
      · exact prime_oneHundredFourCX_3
      · exact prime_oneHundredFourCX_29
      · exact prime_oneHundredFourCX_261250841
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 90915292669) ^ 45457646334 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (2 : ZMod 90915292669) ^ 30305097556 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (2 : ZMod 90915292669) ^ 3135010092 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (2 : ZMod 90915292669) ^ 348 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourCX_98329738021 : Nat.Prime 98329738021 := by
  apply lucas_primality 98329738021 (2 : ZMod 98329738021)
  · rw [← oneHundredFourCXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (7789, 1), (210403, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (7789, 1), (210403, 1)] : List FactorBlock).map factorBlockValue).prod) = 98329738021 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourCX_2
      · exact prime_oneHundredFourCX_3
      · exact prime_oneHundredFourCX_5
      · exact prime_oneHundredFourCX_7789
      · exact prime_oneHundredFourCX_210403
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 98329738021) ^ 49164869010 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (2 : ZMod 98329738021) ^ 32776579340 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (2 : ZMod 98329738021) ^ 19665947604 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (2 : ZMod 98329738021) ^ 12624180 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (2 : ZMod 98329738021) ^ 467340 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourCX_118662433481 : Nat.Prime 118662433481 := by
  apply lucas_primality 118662433481 (6 : ZMod 118662433481)
  · rw [← oneHundredFourCXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (71, 1), (79, 1), (263, 1), (2011, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (71, 1), (79, 1), (263, 1), (2011, 1)] : List FactorBlock).map factorBlockValue).prod) = 118662433481 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourCX_2
      · exact prime_oneHundredFourCX_5
      · exact prime_oneHundredFourCX_71
      · exact prime_oneHundredFourCX_79
      · exact prime_oneHundredFourCX_263
      · exact prime_oneHundredFourCX_2011
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 118662433481) ^ 59331216740 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (6 : ZMod 118662433481) ^ 23732486696 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (6 : ZMod 118662433481) ^ 1671301880 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (6 : ZMod 118662433481) ^ 1502056120 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (6 : ZMod 118662433481) ^ 451187960 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (6 : ZMod 118662433481) ^ 59006680 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourCX_126757647031 : Nat.Prime 126757647031 := by
  apply lucas_primality 126757647031 (12 : ZMod 126757647031)
  · rw [← oneHundredFourCXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (7, 1), (7607, 1), (79349, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (7, 1), (7607, 1), (79349, 1)] : List FactorBlock).map factorBlockValue).prod) = 126757647031 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourCX_2
      · exact prime_oneHundredFourCX_3
      · exact prime_oneHundredFourCX_5
      · exact prime_oneHundredFourCX_7
      · exact prime_oneHundredFourCX_7607
      · exact prime_oneHundredFourCX_79349
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (12 : ZMod 126757647031) ^ 63378823515 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (12 : ZMod 126757647031) ^ 42252549010 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (12 : ZMod 126757647031) ^ 25351529406 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (12 : ZMod 126757647031) ^ 18108235290 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (12 : ZMod 126757647031) ^ 16663290 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (12 : ZMod 126757647031) ^ 1597470 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourCX_140565441811 : Nat.Prime 140565441811 := by
  apply lucas_primality 140565441811 (2 : ZMod 140565441811)
  · rw [← oneHundredFourCXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (41, 1), (79, 1), (229, 1), (6317, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (41, 1), (79, 1), (229, 1), (6317, 1)] : List FactorBlock).map factorBlockValue).prod) = 140565441811 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourCX_2
      · exact prime_oneHundredFourCX_3
      · exact prime_oneHundredFourCX_5
      · exact prime_oneHundredFourCX_41
      · exact prime_oneHundredFourCX_79
      · exact prime_oneHundredFourCX_229
      · exact prime_oneHundredFourCX_6317
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 140565441811) ^ 70282720905 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (2 : ZMod 140565441811) ^ 46855147270 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (2 : ZMod 140565441811) ^ 28113088362 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (2 : ZMod 140565441811) ^ 3428425410 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (2 : ZMod 140565441811) ^ 1779309390 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (2 : ZMod 140565441811) ^ 613822890 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (2 : ZMod 140565441811) ^ 22251930 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourCX_143544239351 : Nat.Prime 143544239351 := by
  apply lucas_primality 143544239351 (13 : ZMod 143544239351)
  · rw [← oneHundredFourCXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (71, 2), (569507, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (71, 2), (569507, 1)] : List FactorBlock).map factorBlockValue).prod) = 143544239351 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourCX_2
      · exact prime_oneHundredFourCX_5
      · exact prime_oneHundredFourCX_71
      · exact prime_oneHundredFourCX_569507
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (13 : ZMod 143544239351) ^ 71772119675 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (13 : ZMod 143544239351) ^ 28708847870 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (13 : ZMod 143544239351) ^ 2021749850 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (13 : ZMod 143544239351) ^ 252050 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourCX_185061724517 : Nat.Prime 185061724517 := by
  apply lucas_primality 185061724517 (2 : ZMod 185061724517)
  · rw [← oneHundredFourCXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (19, 2), (103, 1), (1244263, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (19, 2), (103, 1), (1244263, 1)] : List FactorBlock).map factorBlockValue).prod) = 185061724517 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourCX_2
      · exact prime_oneHundredFourCX_19
      · exact prime_oneHundredFourCX_103
      · exact prime_oneHundredFourCX_1244263
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 185061724517) ^ 92530862258 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (2 : ZMod 185061724517) ^ 9740090764 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (2 : ZMod 185061724517) ^ 1796715772 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (2 : ZMod 185061724517) ^ 148732 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourCX_192116537581 : Nat.Prime 192116537581 := by
  apply lucas_primality 192116537581 (7 : ZMod 192116537581)
  · rw [← oneHundredFourCXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (11, 2), (26462333, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (11, 2), (26462333, 1)] : List FactorBlock).map factorBlockValue).prod) = 192116537581 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourCX_2
      · exact prime_oneHundredFourCX_3
      · exact prime_oneHundredFourCX_5
      · exact prime_oneHundredFourCX_11
      · exact prime_oneHundredFourCX_26462333
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 192116537581) ^ 96058268790 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (7 : ZMod 192116537581) ^ 64038845860 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (7 : ZMod 192116537581) ^ 38423307516 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (7 : ZMod 192116537581) ^ 17465139780 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (7 : ZMod 192116537581) ^ 7260 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourCX_198221802073 : Nat.Prime 198221802073 := by
  apply lucas_primality 198221802073 (5 : ZMod 198221802073)
  · rw [← oneHundredFourCXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (7, 1), (1179891679, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (7, 1), (1179891679, 1)] : List FactorBlock).map factorBlockValue).prod) = 198221802073 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourCX_2
      · exact prime_oneHundredFourCX_3
      · exact prime_oneHundredFourCX_7
      · exact prime_oneHundredFourCX_1179891679
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 198221802073) ^ 99110901036 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (5 : ZMod 198221802073) ^ 66073934024 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (5 : ZMod 198221802073) ^ 28317400296 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (5 : ZMod 198221802073) ^ 168 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourCX_347372067817 : Nat.Prime 347372067817 := by
  apply lucas_primality 347372067817 (7 : ZMod 347372067817)
  · rw [← oneHundredFourCXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (17, 1), (283800709, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (17, 1), (283800709, 1)] : List FactorBlock).map factorBlockValue).prod) = 347372067817 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourCX_2
      · exact prime_oneHundredFourCX_3
      · exact prime_oneHundredFourCX_17
      · exact prime_oneHundredFourCX_283800709
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 347372067817) ^ 173686033908 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (7 : ZMod 347372067817) ^ 115790689272 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (7 : ZMod 347372067817) ^ 20433651048 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (7 : ZMod 347372067817) ^ 1224 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourCX_401634562237 : Nat.Prime 401634562237 := by
  apply lucas_primality 401634562237 (2 : ZMod 401634562237)
  · rw [← oneHundredFourCXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (127, 1), (277, 1), (951407, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (127, 1), (277, 1), (951407, 1)] : List FactorBlock).map factorBlockValue).prod) = 401634562237 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourCX_2
      · exact prime_oneHundredFourCX_3
      · exact prime_oneHundredFourCX_127
      · exact prime_oneHundredFourCX_277
      · exact prime_oneHundredFourCX_951407
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 401634562237) ^ 200817281118 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (2 : ZMod 401634562237) ^ 133878187412 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (2 : ZMod 401634562237) ^ 3162476868 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (2 : ZMod 401634562237) ^ 1449944268 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (2 : ZMod 401634562237) ^ 422148 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourCX_471834248563 : Nat.Prime 471834248563 := by
  apply lucas_primality 471834248563 (2 : ZMod 471834248563)
  · rw [← oneHundredFourCXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (907, 1), (1009, 1), (28643, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (907, 1), (1009, 1), (28643, 1)] : List FactorBlock).map factorBlockValue).prod) = 471834248563 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourCX_2
      · exact prime_oneHundredFourCX_3
      · exact prime_oneHundredFourCX_907
      · exact prime_oneHundredFourCX_1009
      · exact prime_oneHundredFourCX_28643
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 471834248563) ^ 235917124281 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (2 : ZMod 471834248563) ^ 157278082854 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (2 : ZMod 471834248563) ^ 520214166 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (2 : ZMod 471834248563) ^ 467625618 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (2 : ZMod 471834248563) ^ 16472934 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourCX_641759962141 : Nat.Prime 641759962141 := by
  apply lucas_primality 641759962141 (10 : ZMod 641759962141)
  · rw [← oneHundredFourCXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (5, 1), (11, 2), (29465563, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (5, 1), (11, 2), (29465563, 1)] : List FactorBlock).map factorBlockValue).prod) = 641759962141 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourCX_2
      · exact prime_oneHundredFourCX_3
      · exact prime_oneHundredFourCX_5
      · exact prime_oneHundredFourCX_11
      · exact prime_oneHundredFourCX_29465563
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 641759962141) ^ 320879981070 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (10 : ZMod 641759962141) ^ 213919987380 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (10 : ZMod 641759962141) ^ 128351992428 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (10 : ZMod 641759962141) ^ 58341814740 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (10 : ZMod 641759962141) ^ 21780 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourCX_685754131277 : Nat.Prime 685754131277 := by
  apply lucas_primality 685754131277 (2 : ZMod 685754131277)
  · rw [← oneHundredFourCXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (23, 1), (7453849253, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (23, 1), (7453849253, 1)] : List FactorBlock).map factorBlockValue).prod) = 685754131277 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFourCX_2
      · exact prime_oneHundredFourCX_23
      · exact prime_oneHundredFourCX_7453849253
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 685754131277) ^ 342877065638 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (2 : ZMod 685754131277) ^ 29815397012 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (2 : ZMod 685754131277) ^ 92 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourCX_896590250737 : Nat.Prime 896590250737 := by
  apply lucas_primality 896590250737 (5 : ZMod 896590250737)
  · rw [← oneHundredFourCXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (41, 1), (455584477, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (41, 1), (455584477, 1)] : List FactorBlock).map factorBlockValue).prod) = 896590250737 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourCX_2
      · exact prime_oneHundredFourCX_3
      · exact prime_oneHundredFourCX_41
      · exact prime_oneHundredFourCX_455584477
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 896590250737) ^ 448295125368 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (5 : ZMod 896590250737) ^ 298863416912 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (5 : ZMod 896590250737) ^ 21868054896 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (5 : ZMod 896590250737) ^ 1968 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourCX_1152699225487 : Nat.Prime 1152699225487 := by
  apply lucas_primality 1152699225487 (5 : ZMod 1152699225487)
  · rw [← oneHundredFourCXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (192116537581, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (192116537581, 1)] : List FactorBlock).map factorBlockValue).prod) = 1152699225487 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFourCX_2
      · exact prime_oneHundredFourCX_3
      · exact prime_oneHundredFourCX_192116537581
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 1152699225487) ^ 576349612743 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (5 : ZMod 1152699225487) ^ 384233075162 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (5 : ZMod 1152699225487) ^ 6 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourCX_1564506913061 : Nat.Prime 1564506913061 := by
  apply lucas_primality 1564506913061 (2 : ZMod 1564506913061)
  · rw [← oneHundredFourCXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (7, 1), (13, 1), (281, 1), (3059143, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (7, 1), (13, 1), (281, 1), (3059143, 1)] : List FactorBlock).map factorBlockValue).prod) = 1564506913061 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourCX_2
      · exact prime_oneHundredFourCX_5
      · exact prime_oneHundredFourCX_7
      · exact prime_oneHundredFourCX_13
      · exact prime_oneHundredFourCX_281
      · exact prime_oneHundredFourCX_3059143
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1564506913061) ^ 782253456530 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (2 : ZMod 1564506913061) ^ 312901382612 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (2 : ZMod 1564506913061) ^ 223500987580 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (2 : ZMod 1564506913061) ^ 120346685620 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (2 : ZMod 1564506913061) ^ 5567640260 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (2 : ZMod 1564506913061) ^ 511420 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourCX_1840866070013 : Nat.Prime 1840866070013 := by
  apply lucas_primality 1840866070013 (2 : ZMod 1840866070013)
  · rw [← oneHundredFourCXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (31, 1), (1901, 1), (7809413, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (31, 1), (1901, 1), (7809413, 1)] : List FactorBlock).map factorBlockValue).prod) = 1840866070013 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourCX_2
      · exact prime_oneHundredFourCX_31
      · exact prime_oneHundredFourCX_1901
      · exact prime_oneHundredFourCX_7809413
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1840866070013) ^ 920433035006 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (2 : ZMod 1840866070013) ^ 59382776452 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (2 : ZMod 1840866070013) ^ 968367212 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (2 : ZMod 1840866070013) ^ 235724 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourCX_2676546708113 : Nat.Prime 2676546708113 := by
  apply lucas_primality 2676546708113 (3 : ZMod 2676546708113)
  · rw [← oneHundredFourCXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (107, 1), (28729, 1), (54419, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (107, 1), (28729, 1), (54419, 1)] : List FactorBlock).map factorBlockValue).prod) = 2676546708113 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourCX_2
      · exact prime_oneHundredFourCX_107
      · exact prime_oneHundredFourCX_28729
      · exact prime_oneHundredFourCX_54419
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 2676546708113) ^ 1338273354056 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (3 : ZMod 2676546708113) ^ 25014455216 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (3 : ZMod 2676546708113) ^ 93165328 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (3 : ZMod 2676546708113) ^ 49184048 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourCX_2852304439213 : Nat.Prime 2852304439213 := by
  apply lucas_primality 2852304439213 (2 : ZMod 2852304439213)
  · rw [← oneHundredFourCXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 4), (101, 1), (2579, 1), (33797, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 4), (101, 1), (2579, 1), (33797, 1)] : List FactorBlock).map factorBlockValue).prod) = 2852304439213 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourCX_2
      · exact prime_oneHundredFourCX_3
      · exact prime_oneHundredFourCX_101
      · exact prime_oneHundredFourCX_2579
      · exact prime_oneHundredFourCX_33797
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 2852304439213) ^ 1426152219606 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (2 : ZMod 2852304439213) ^ 950768146404 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (2 : ZMod 2852304439213) ^ 28240638012 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (2 : ZMod 2852304439213) ^ 1105973028 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (2 : ZMod 2852304439213) ^ 84395196 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourCX_4395081243799 : Nat.Prime 4395081243799 := by
  apply lucas_primality 4395081243799 (7 : ZMod 4395081243799)
  · rw [← oneHundredFourCXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (7, 1), (2521, 1), (13836413, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (7, 1), (2521, 1), (13836413, 1)] : List FactorBlock).map factorBlockValue).prod) = 4395081243799 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourCX_2
      · exact prime_oneHundredFourCX_3
      · exact prime_oneHundredFourCX_7
      · exact prime_oneHundredFourCX_2521
      · exact prime_oneHundredFourCX_13836413
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 4395081243799) ^ 2197540621899 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (7 : ZMod 4395081243799) ^ 1465027081266 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (7 : ZMod 4395081243799) ^ 627868749114 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (7 : ZMod 4395081243799) ^ 1743388038 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (7 : ZMod 4395081243799) ^ 317646 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourCX_4406161086179 : Nat.Prime 4406161086179 := by
  apply lucas_primality 4406161086179 (2 : ZMod 4406161086179)
  · rw [← oneHundredFourCXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (19, 1), (263, 1), (440880637, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (19, 1), (263, 1), (440880637, 1)] : List FactorBlock).map factorBlockValue).prod) = 4406161086179 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourCX_2
      · exact prime_oneHundredFourCX_19
      · exact prime_oneHundredFourCX_263
      · exact prime_oneHundredFourCX_440880637
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 4406161086179) ^ 2203080543089 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (2 : ZMod 4406161086179) ^ 231903215062 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (2 : ZMod 4406161086179) ^ 16753464206 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (2 : ZMod 4406161086179) ^ 9994 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourCX_4420856813203 : Nat.Prime 4420856813203 := by
  apply lucas_primality 4420856813203 (2 : ZMod 4420856813203)
  · rw [← oneHundredFourCXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (103, 1), (794832221, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (103, 1), (794832221, 1)] : List FactorBlock).map factorBlockValue).prod) = 4420856813203 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourCX_2
      · exact prime_oneHundredFourCX_3
      · exact prime_oneHundredFourCX_103
      · exact prime_oneHundredFourCX_794832221
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 4420856813203) ^ 2210428406601 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (2 : ZMod 4420856813203) ^ 1473618937734 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (2 : ZMod 4420856813203) ^ 42920939934 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (2 : ZMod 4420856813203) ^ 5562 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourCX_5248904427061 : Nat.Prime 5248904427061 := by
  apply lucas_primality 5248904427061 (6 : ZMod 5248904427061)
  · rw [← oneHundredFourCXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (7, 1), (19, 2), (619, 1), (55927, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (7, 1), (19, 2), (619, 1), (55927, 1)] : List FactorBlock).map factorBlockValue).prod) = 5248904427061 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourCX_2
      · exact prime_oneHundredFourCX_3
      · exact prime_oneHundredFourCX_5
      · exact prime_oneHundredFourCX_7
      · exact prime_oneHundredFourCX_19
      · exact prime_oneHundredFourCX_619
      · exact prime_oneHundredFourCX_55927
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 5248904427061) ^ 2624452213530 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (6 : ZMod 5248904427061) ^ 1749634809020 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (6 : ZMod 5248904427061) ^ 1049780885412 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (6 : ZMod 5248904427061) ^ 749843489580 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (6 : ZMod 5248904427061) ^ 276258127740 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (6 : ZMod 5248904427061) ^ 8479651740 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (6 : ZMod 5248904427061) ^ 93852780 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourCX_5267554879547 : Nat.Prime 5267554879547 := by
  apply lucas_primality 5267554879547 (2 : ZMod 5267554879547)
  · rw [← oneHundredFourCXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (4519, 1), (582823067, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (4519, 1), (582823067, 1)] : List FactorBlock).map factorBlockValue).prod) = 5267554879547 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFourCX_2
      · exact prime_oneHundredFourCX_4519
      · exact prime_oneHundredFourCX_582823067
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 5267554879547) ^ 2633777439773 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (2 : ZMod 5267554879547) ^ 1165646134 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (2 : ZMod 5267554879547) ^ 9038 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourCX_5478203566151 : Nat.Prime 5478203566151 := by
  apply lucas_primality 5478203566151 (14 : ZMod 5478203566151)
  · rw [← oneHundredFourCXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (7, 1), (8929, 1), (1752941, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (7, 1), (8929, 1), (1752941, 1)] : List FactorBlock).map factorBlockValue).prod) = 5478203566151 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourCX_2
      · exact prime_oneHundredFourCX_5
      · exact prime_oneHundredFourCX_7
      · exact prime_oneHundredFourCX_8929
      · exact prime_oneHundredFourCX_1752941
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (14 : ZMod 5478203566151) ^ 2739101783075 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (14 : ZMod 5478203566151) ^ 1095640713230 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (14 : ZMod 5478203566151) ^ 782600509450 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (14 : ZMod 5478203566151) ^ 613529350 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (14 : ZMod 5478203566151) ^ 3125150 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourCX_5506709036351 : Nat.Prime 5506709036351 := by
  apply lucas_primality 5506709036351 (17 : ZMod 5506709036351)
  · rw [← oneHundredFourCXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (47, 1), (3373, 1), (694717, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (47, 1), (3373, 1), (694717, 1)] : List FactorBlock).map factorBlockValue).prod) = 5506709036351 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourCX_2
      · exact prime_oneHundredFourCX_5
      · exact prime_oneHundredFourCX_47
      · exact prime_oneHundredFourCX_3373
      · exact prime_oneHundredFourCX_694717
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (17 : ZMod 5506709036351) ^ 2753354518175 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (17 : ZMod 5506709036351) ^ 1101341807270 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (17 : ZMod 5506709036351) ^ 117164022050 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (17 : ZMod 5506709036351) ^ 1632584950 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (17 : ZMod 5506709036351) ^ 7926550 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourCX_5782770656261 : Nat.Prime 5782770656261 := by
  apply lucas_primality 5782770656261 (2 : ZMod 5782770656261)
  · rw [← oneHundredFourCXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (13, 1), (17, 1), (23447, 1), (55799, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (13, 1), (17, 1), (23447, 1), (55799, 1)] : List FactorBlock).map factorBlockValue).prod) = 5782770656261 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourCX_2
      · exact prime_oneHundredFourCX_5
      · exact prime_oneHundredFourCX_13
      · exact prime_oneHundredFourCX_17
      · exact prime_oneHundredFourCX_23447
      · exact prime_oneHundredFourCX_55799
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 5782770656261) ^ 2891385328130 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (2 : ZMod 5782770656261) ^ 1156554131252 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (2 : ZMod 5782770656261) ^ 444828512020 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (2 : ZMod 5782770656261) ^ 340162979780 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (2 : ZMod 5782770656261) ^ 246631580 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (2 : ZMod 5782770656261) ^ 103635740 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourCX_7177211967551 : Nat.Prime 7177211967551 := by
  apply lucas_primality 7177211967551 (13 : ZMod 7177211967551)
  · rw [← oneHundredFourCXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (143544239351, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (143544239351, 1)] : List FactorBlock).map factorBlockValue).prod) = 7177211967551 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFourCX_2
      · exact prime_oneHundredFourCX_5
      · exact prime_oneHundredFourCX_143544239351
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (13 : ZMod 7177211967551) ^ 3588605983775 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (13 : ZMod 7177211967551) ^ 1435442393510 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (13 : ZMod 7177211967551) ^ 50 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourCX_9236959368229 : Nat.Prime 9236959368229 := by
  apply lucas_primality 9236959368229 (6 : ZMod 9236959368229)
  · rw [← oneHundredFourCXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (41, 1), (6258102553, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (41, 1), (6258102553, 1)] : List FactorBlock).map factorBlockValue).prod) = 9236959368229 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourCX_2
      · exact prime_oneHundredFourCX_3
      · exact prime_oneHundredFourCX_41
      · exact prime_oneHundredFourCX_6258102553
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 9236959368229) ^ 4618479684114 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (6 : ZMod 9236959368229) ^ 3078986456076 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (6 : ZMod 9236959368229) ^ 225291691908 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (6 : ZMod 9236959368229) ^ 1476 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourCX_9785892628279 : Nat.Prime 9785892628279 := by
  apply lucas_primality 9785892628279 (6 : ZMod 9785892628279)
  · rw [← oneHundredFourCXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 4), (13, 1), (229, 1), (20291147, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 4), (13, 1), (229, 1), (20291147, 1)] : List FactorBlock).map factorBlockValue).prod) = 9785892628279 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourCX_2
      · exact prime_oneHundredFourCX_3
      · exact prime_oneHundredFourCX_13
      · exact prime_oneHundredFourCX_229
      · exact prime_oneHundredFourCX_20291147
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 9785892628279) ^ 4892946314139 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (6 : ZMod 9785892628279) ^ 3261964209426 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (6 : ZMod 9785892628279) ^ 752760971406 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (6 : ZMod 9785892628279) ^ 42733155582 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (6 : ZMod 9785892628279) ^ 482274 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourCX_10247335520207 : Nat.Prime 10247335520207 := by
  apply lucas_primality 10247335520207 (5 : ZMod 10247335520207)
  · rw [← oneHundredFourCXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (149, 1), (34387031947, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (149, 1), (34387031947, 1)] : List FactorBlock).map factorBlockValue).prod) = 10247335520207 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFourCX_2
      · exact prime_oneHundredFourCX_149
      · exact prime_oneHundredFourCX_34387031947
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 10247335520207) ^ 5123667760103 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (5 : ZMod 10247335520207) ^ 68774063894 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (5 : ZMod 10247335520207) ^ 298 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourCX_10501882035901 : Nat.Prime 10501882035901 := by
  apply lucas_primality 10501882035901 (2 : ZMod 10501882035901)
  · rw [← oneHundredFourCXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 2), (35006273453, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 2), (35006273453, 1)] : List FactorBlock).map factorBlockValue).prod) = 10501882035901 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourCX_2
      · exact prime_oneHundredFourCX_3
      · exact prime_oneHundredFourCX_5
      · exact prime_oneHundredFourCX_35006273453
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 10501882035901) ^ 5250941017950 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (2 : ZMod 10501882035901) ^ 3500627345300 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (2 : ZMod 10501882035901) ^ 2100376407180 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (2 : ZMod 10501882035901) ^ 300 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourCX_14804937961361 : Nat.Prime 14804937961361 := by
  apply lucas_primality 14804937961361 (6 : ZMod 14804937961361)
  · rw [← oneHundredFourCXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (5, 1), (185061724517, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (5, 1), (185061724517, 1)] : List FactorBlock).map factorBlockValue).prod) = 14804937961361 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFourCX_2
      · exact prime_oneHundredFourCX_5
      · exact prime_oneHundredFourCX_185061724517
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (6 : ZMod 14804937961361) ^ 7402468980680 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (6 : ZMod 14804937961361) ^ 2960987592272 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (6 : ZMod 14804937961361) ^ 80 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourCX_23712864539461 : Nat.Prime 23712864539461 := by
  apply lucas_primality 23712864539461 (7 : ZMod 23712864539461)
  · rw [← oneHundredFourCXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (103, 1), (311, 1), (12337727, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (103, 1), (311, 1), (12337727, 1)] : List FactorBlock).map factorBlockValue).prod) = 23712864539461 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourCX_2
      · exact prime_oneHundredFourCX_3
      · exact prime_oneHundredFourCX_5
      · exact prime_oneHundredFourCX_103
      · exact prime_oneHundredFourCX_311
      · exact prime_oneHundredFourCX_12337727
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 23712864539461) ^ 11856432269730 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (7 : ZMod 23712864539461) ^ 7904288179820 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (7 : ZMod 23712864539461) ^ 4742572907892 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (7 : ZMod 23712864539461) ^ 230221985820 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (7 : ZMod 23712864539461) ^ 76247152860 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (7 : ZMod 23712864539461) ^ 1921980 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourCX_28095098988029 : Nat.Prime 28095098988029 := by
  apply lucas_primality 28095098988029 (2 : ZMod 28095098988029)
  · rw [← oneHundredFourCXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (479, 1), (14663412833, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (479, 1), (14663412833, 1)] : List FactorBlock).map factorBlockValue).prod) = 28095098988029 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFourCX_2
      · exact prime_oneHundredFourCX_479
      · exact prime_oneHundredFourCX_14663412833
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 28095098988029) ^ 14047549494014 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (2 : ZMod 28095098988029) ^ 58653651332 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (2 : ZMod 28095098988029) ^ 1916 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourCX_33312673606897 : Nat.Prime 33312673606897 := by
  apply lucas_primality 33312673606897 (7 : ZMod 33312673606897)
  · rw [← oneHundredFourCXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 2), (31, 1), (151, 2), (327289, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 2), (31, 1), (151, 2), (327289, 1)] : List FactorBlock).map factorBlockValue).prod) = 33312673606897 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourCX_2
      · exact prime_oneHundredFourCX_3
      · exact prime_oneHundredFourCX_31
      · exact prime_oneHundredFourCX_151
      · exact prime_oneHundredFourCX_327289
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 33312673606897) ^ 16656336803448 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (7 : ZMod 33312673606897) ^ 11104224535632 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (7 : ZMod 33312673606897) ^ 1074602374416 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (7 : ZMod 33312673606897) ^ 220613732496 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (7 : ZMod 33312673606897) ^ 101783664 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourCX_51953828355277 : Nat.Prime 51953828355277 := by
  apply lucas_primality 51953828355277 (6 : ZMod 51953828355277)
  · rw [← oneHundredFourCXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (1493, 1), (13417, 1), (216133, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (1493, 1), (13417, 1), (216133, 1)] : List FactorBlock).map factorBlockValue).prod) = 51953828355277 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourCX_2
      · exact prime_oneHundredFourCX_3
      · exact prime_oneHundredFourCX_1493
      · exact prime_oneHundredFourCX_13417
      · exact prime_oneHundredFourCX_216133
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 51953828355277) ^ 25976914177638 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (6 : ZMod 51953828355277) ^ 17317942785092 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (6 : ZMod 51953828355277) ^ 34798277532 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (6 : ZMod 51953828355277) ^ 3872238828 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (6 : ZMod 51953828355277) ^ 240378972 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourCX_52688903207623 : Nat.Prime 52688903207623 := by
  apply lucas_primality 52688903207623 (3 : ZMod 52688903207623)
  · rw [← oneHundredFourCXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (107, 1), (7460903881, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (107, 1), (7460903881, 1)] : List FactorBlock).map factorBlockValue).prod) = 52688903207623 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourCX_2
      · exact prime_oneHundredFourCX_3
      · exact prime_oneHundredFourCX_11
      · exact prime_oneHundredFourCX_107
      · exact prime_oneHundredFourCX_7460903881
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 52688903207623) ^ 26344451603811 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (3 : ZMod 52688903207623) ^ 17562967735874 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (3 : ZMod 52688903207623) ^ 4789900291602 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (3 : ZMod 52688903207623) ^ 492419656146 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (3 : ZMod 52688903207623) ^ 7062 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourCX_91897139755117 : Nat.Prime 91897139755117 := by
  apply lucas_primality 91897139755117 (2 : ZMod 91897139755117)
  · rw [← oneHundredFourCXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (37, 1), (98939, 1), (232439, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (37, 1), (98939, 1), (232439, 1)] : List FactorBlock).map factorBlockValue).prod) = 91897139755117 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourCX_2
      · exact prime_oneHundredFourCX_3
      · exact prime_oneHundredFourCX_37
      · exact prime_oneHundredFourCX_98939
      · exact prime_oneHundredFourCX_232439
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 91897139755117) ^ 45948569877558 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (2 : ZMod 91897139755117) ^ 30632379918372 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (2 : ZMod 91897139755117) ^ 2483706479868 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (2 : ZMod 91897139755117) ^ 928826244 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (2 : ZMod 91897139755117) ^ 395360244 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourCX_115342509540833 : Nat.Prime 115342509540833 := by
  apply lucas_primality 115342509540833 (3 : ZMod 115342509540833)
  · rw [← oneHundredFourCXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (7, 1), (2777, 1), (185423809, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (7, 1), (2777, 1), (185423809, 1)] : List FactorBlock).map factorBlockValue).prod) = 115342509540833 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourCX_2
      · exact prime_oneHundredFourCX_7
      · exact prime_oneHundredFourCX_2777
      · exact prime_oneHundredFourCX_185423809
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 115342509540833) ^ 57671254770416 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (3 : ZMod 115342509540833) ^ 16477501362976 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (3 : ZMod 115342509540833) ^ 41534933216 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (3 : ZMod 115342509540833) ^ 622048 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourCX_115465670140633 : Nat.Prime 115465670140633 := by
  apply lucas_primality 115465670140633 (11 : ZMod 115465670140633)
  · rw [← oneHundredFourCXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (7, 3), (14026441951, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (7, 3), (14026441951, 1)] : List FactorBlock).map factorBlockValue).prod) = 115465670140633 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourCX_2
      · exact prime_oneHundredFourCX_3
      · exact prime_oneHundredFourCX_7
      · exact prime_oneHundredFourCX_14026441951
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 115465670140633) ^ 57732835070316 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (11 : ZMod 115465670140633) ^ 38488556713544 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (11 : ZMod 115465670140633) ^ 16495095734376 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (11 : ZMod 115465670140633) ^ 8232 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourCX_193144198366307 : Nat.Prime 193144198366307 := by
  apply lucas_primality 193144198366307 (2 : ZMod 193144198366307)
  · rw [← oneHundredFourCXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (101, 1), (86923581623, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (101, 1), (86923581623, 1)] : List FactorBlock).map factorBlockValue).prod) = 193144198366307 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourCX_2
      · exact prime_oneHundredFourCX_11
      · exact prime_oneHundredFourCX_101
      · exact prime_oneHundredFourCX_86923581623
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 193144198366307) ^ 96572099183153 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (2 : ZMod 193144198366307) ^ 17558563487846 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (2 : ZMod 193144198366307) ^ 1912318795706 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (2 : ZMod 193144198366307) ^ 2222 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourCX_258862483991359 : Nat.Prime 258862483991359 := by
  apply lucas_primality 258862483991359 (6 : ZMod 258862483991359)
  · rw [← oneHundredFourCXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (13, 1), (10789, 1), (102534983, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (13, 1), (10789, 1), (102534983, 1)] : List FactorBlock).map factorBlockValue).prod) = 258862483991359 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourCX_2
      · exact prime_oneHundredFourCX_3
      · exact prime_oneHundredFourCX_13
      · exact prime_oneHundredFourCX_10789
      · exact prime_oneHundredFourCX_102534983
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 258862483991359) ^ 129431241995679 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (6 : ZMod 258862483991359) ^ 86287494663786 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (6 : ZMod 258862483991359) ^ 19912498768566 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (6 : ZMod 258862483991359) ^ 23993186022 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (6 : ZMod 258862483991359) ^ 2524626 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourCX_267494201311979 : Nat.Prime 267494201311979 := by
  apply lucas_primality 267494201311979 (6 : ZMod 267494201311979)
  · rw [← oneHundredFourCXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (97, 1), (107, 1), (12886318591, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (97, 1), (107, 1), (12886318591, 1)] : List FactorBlock).map factorBlockValue).prod) = 267494201311979 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourCX_2
      · exact prime_oneHundredFourCX_97
      · exact prime_oneHundredFourCX_107
      · exact prime_oneHundredFourCX_12886318591
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 267494201311979) ^ 133747100655989 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (6 : ZMod 267494201311979) ^ 2757672178474 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (6 : ZMod 267494201311979) ^ 2499945806654 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (6 : ZMod 267494201311979) ^ 20758 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourCX_281090863417759 : Nat.Prime 281090863417759 := by
  apply lucas_primality 281090863417759 (3 : ZMod 281090863417759)
  · rw [← oneHundredFourCXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (73, 1), (641759962141, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (73, 1), (641759962141, 1)] : List FactorBlock).map factorBlockValue).prod) = 281090863417759 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourCX_2
      · exact prime_oneHundredFourCX_3
      · exact prime_oneHundredFourCX_73
      · exact prime_oneHundredFourCX_641759962141
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 281090863417759) ^ 140545431708879 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (3 : ZMod 281090863417759) ^ 93696954472586 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (3 : ZMod 281090863417759) ^ 3850559772846 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (3 : ZMod 281090863417759) ^ 438 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourCX_391277769120149 : Nat.Prime 391277769120149 := by
  apply lucas_primality 391277769120149 (2 : ZMod 391277769120149)
  · rw [← oneHundredFourCXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (29, 1), (293, 2), (2731, 1), (14387, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (29, 1), (293, 2), (2731, 1), (14387, 1)] : List FactorBlock).map factorBlockValue).prod) = 391277769120149 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourCX_2
      · exact prime_oneHundredFourCX_29
      · exact prime_oneHundredFourCX_293
      · exact prime_oneHundredFourCX_2731
      · exact prime_oneHundredFourCX_14387
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 391277769120149) ^ 195638884560074 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (2 : ZMod 391277769120149) ^ 13492336866212 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (2 : ZMod 391277769120149) ^ 1335419007236 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (2 : ZMod 391277769120149) ^ 143272709308 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (2 : ZMod 391277769120149) ^ 27196619804 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourCX_413137636917107 : Nat.Prime 413137636917107 := by
  apply lucas_primality 413137636917107 (2 : ZMod 413137636917107)
  · rw [← oneHundredFourCXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (47, 1), (4395081243799, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (47, 1), (4395081243799, 1)] : List FactorBlock).map factorBlockValue).prod) = 413137636917107 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFourCX_2
      · exact prime_oneHundredFourCX_47
      · exact prime_oneHundredFourCX_4395081243799
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 413137636917107) ^ 206568818458553 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (2 : ZMod 413137636917107) ^ 8790162487598 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (2 : ZMod 413137636917107) ^ 94 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourCX_419604237344917 : Nat.Prime 419604237344917 := by
  apply lucas_primality 419604237344917 (5 : ZMod 419604237344917)
  · rw [← oneHundredFourCXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (13, 1), (896590250737, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (13, 1), (896590250737, 1)] : List FactorBlock).map factorBlockValue).prod) = 419604237344917 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourCX_2
      · exact prime_oneHundredFourCX_3
      · exact prime_oneHundredFourCX_13
      · exact prime_oneHundredFourCX_896590250737
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 419604237344917) ^ 209802118672458 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (5 : ZMod 419604237344917) ^ 139868079114972 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (5 : ZMod 419604237344917) ^ 32277249026532 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (5 : ZMod 419604237344917) ^ 468 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourCX_566265620336761 : Nat.Prime 566265620336761 := by
  apply lucas_primality 566265620336761 (13 : ZMod 566265620336761)
  · rw [← oneHundredFourCXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (5, 1), (157, 1), (10018853863, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (5, 1), (157, 1), (10018853863, 1)] : List FactorBlock).map factorBlockValue).prod) = 566265620336761 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourCX_2
      · exact prime_oneHundredFourCX_3
      · exact prime_oneHundredFourCX_5
      · exact prime_oneHundredFourCX_157
      · exact prime_oneHundredFourCX_10018853863
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 566265620336761) ^ 283132810168380 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (13 : ZMod 566265620336761) ^ 188755206778920 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (13 : ZMod 566265620336761) ^ 113253124067352 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (13 : ZMod 566265620336761) ^ 3606787390680 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (13 : ZMod 566265620336761) ^ 56520 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourCX_576590716499729 : Nat.Prime 576590716499729 := by
  apply lucas_primality 576590716499729 (3 : ZMod 576590716499729)
  · rw [← oneHundredFourCXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (7, 1), (6173, 1), (833975603, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (7, 1), (6173, 1), (833975603, 1)] : List FactorBlock).map factorBlockValue).prod) = 576590716499729 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourCX_2
      · exact prime_oneHundredFourCX_7
      · exact prime_oneHundredFourCX_6173
      · exact prime_oneHundredFourCX_833975603
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 576590716499729) ^ 288295358249864 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (3 : ZMod 576590716499729) ^ 82370102357104 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (3 : ZMod 576590716499729) ^ 93405267536 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (3 : ZMod 576590716499729) ^ 691376 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourCX_810117218002061 : Nat.Prime 810117218002061 := by
  apply lucas_primality 810117218002061 (2 : ZMod 810117218002061)
  · rw [← oneHundredFourCXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (23, 1), (79, 1), (22292713759, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (23, 1), (79, 1), (22292713759, 1)] : List FactorBlock).map factorBlockValue).prod) = 810117218002061 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourCX_2
      · exact prime_oneHundredFourCX_5
      · exact prime_oneHundredFourCX_23
      · exact prime_oneHundredFourCX_79
      · exact prime_oneHundredFourCX_22292713759
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 810117218002061) ^ 405058609001030 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (2 : ZMod 810117218002061) ^ 162023443600412 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (2 : ZMod 810117218002061) ^ 35222487739220 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (2 : ZMod 810117218002061) ^ 10254648329140 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (2 : ZMod 810117218002061) ^ 36340 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourCX_821991499516457 : Nat.Prime 821991499516457 := by
  apply lucas_primality 821991499516457 (3 : ZMod 821991499516457)
  · rw [← oneHundredFourCXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (479, 1), (243209, 1), (881987, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (479, 1), (243209, 1), (881987, 1)] : List FactorBlock).map factorBlockValue).prod) = 821991499516457 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourCX_2
      · exact prime_oneHundredFourCX_479
      · exact prime_oneHundredFourCX_243209
      · exact prime_oneHundredFourCX_881987
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 821991499516457) ^ 410995749758228 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (3 : ZMod 821991499516457) ^ 1716057410264 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (3 : ZMod 821991499516457) ^ 3379774184 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (3 : ZMod 821991499516457) ^ 931976888 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourCX_1103534258950789 : Nat.Prime 1103534258950789 := by
  apply lucas_primality 1103534258950789 (2 : ZMod 1103534258950789)
  · rw [← oneHundredFourCXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 1), (1993, 1), (6591727349, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 1), (1993, 1), (6591727349, 1)] : List FactorBlock).map factorBlockValue).prod) = 1103534258950789 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourCX_2
      · exact prime_oneHundredFourCX_3
      · exact prime_oneHundredFourCX_7
      · exact prime_oneHundredFourCX_1993
      · exact prime_oneHundredFourCX_6591727349
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1103534258950789) ^ 551767129475394 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (2 : ZMod 1103534258950789) ^ 367844752983596 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (2 : ZMod 1103534258950789) ^ 157647751278684 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (2 : ZMod 1103534258950789) ^ 553705097316 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (2 : ZMod 1103534258950789) ^ 167412 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourCX_1291737826932829 : Nat.Prime 1291737826932829 := by
  apply lucas_primality 1291737826932829 (2 : ZMod 1291737826932829)
  · rw [← oneHundredFourCXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (11, 1), (9785892628279, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (11, 1), (9785892628279, 1)] : List FactorBlock).map factorBlockValue).prod) = 1291737826932829 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourCX_2
      · exact prime_oneHundredFourCX_3
      · exact prime_oneHundredFourCX_11
      · exact prime_oneHundredFourCX_9785892628279
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1291737826932829) ^ 645868913466414 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (2 : ZMod 1291737826932829) ^ 430579275644276 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (2 : ZMod 1291737826932829) ^ 117430711539348 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (2 : ZMod 1291737826932829) ^ 132 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourCX_1835110977115861 : Nat.Prime 1835110977115861 := by
  apply lucas_primality 1835110977115861 (6 : ZMod 1835110977115861)
  · rw [← oneHundredFourCXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (5, 1), (31, 1), (457, 1), (719634431, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (5, 1), (31, 1), (457, 1), (719634431, 1)] : List FactorBlock).map factorBlockValue).prod) = 1835110977115861 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourCX_2
      · exact prime_oneHundredFourCX_3
      · exact prime_oneHundredFourCX_5
      · exact prime_oneHundredFourCX_31
      · exact prime_oneHundredFourCX_457
      · exact prime_oneHundredFourCX_719634431
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 1835110977115861) ^ 917555488557930 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (6 : ZMod 1835110977115861) ^ 611703659038620 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (6 : ZMod 1835110977115861) ^ 367022195423172 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (6 : ZMod 1835110977115861) ^ 59197128294060 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (6 : ZMod 1835110977115861) ^ 4015560124980 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (6 : ZMod 1835110977115861) ^ 2550060 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourCX_4737580147635521 : Nat.Prime 4737580147635521 := by
  apply lucas_primality 4737580147635521 (3 : ZMod 4737580147635521)
  · rw [← oneHundredFourCXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (5, 1), (14804937961361, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (5, 1), (14804937961361, 1)] : List FactorBlock).map factorBlockValue).prod) = 4737580147635521 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFourCX_2
      · exact prime_oneHundredFourCX_5
      · exact prime_oneHundredFourCX_14804937961361
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 4737580147635521) ^ 2368790073817760 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (3 : ZMod 4737580147635521) ^ 947516029527104 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (3 : ZMod 4737580147635521) ^ 320 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourCX_8050069606855691 : Nat.Prime 8050069606855691 := by
  apply lucas_primality 8050069606855691 (2 : ZMod 8050069606855691)
  · rw [← oneHundredFourCXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (23, 1), (53, 1), (71, 1), (9301169981, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (23, 1), (53, 1), (71, 1), (9301169981, 1)] : List FactorBlock).map factorBlockValue).prod) = 8050069606855691 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourCX_2
      · exact prime_oneHundredFourCX_5
      · exact prime_oneHundredFourCX_23
      · exact prime_oneHundredFourCX_53
      · exact prime_oneHundredFourCX_71
      · exact prime_oneHundredFourCX_9301169981
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 8050069606855691) ^ 4025034803427845 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (2 : ZMod 8050069606855691) ^ 1610013921371138 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (2 : ZMod 8050069606855691) ^ 350003026385030 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (2 : ZMod 8050069606855691) ^ 151888105789730 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (2 : ZMod 8050069606855691) ^ 113381262068390 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (2 : ZMod 8050069606855691) ^ 865490 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourCX_8560070626452379 : Nat.Prime 8560070626452379 := by
  apply lucas_primality 8560070626452379 (2 : ZMod 8560070626452379)
  · rw [← oneHundredFourCXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (1093, 1), (118662433481, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (1093, 1), (118662433481, 1)] : List FactorBlock).map factorBlockValue).prod) = 8560070626452379 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourCX_2
      · exact prime_oneHundredFourCX_3
      · exact prime_oneHundredFourCX_11
      · exact prime_oneHundredFourCX_1093
      · exact prime_oneHundredFourCX_118662433481
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 8560070626452379) ^ 4280035313226189 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (2 : ZMod 8560070626452379) ^ 2853356875484126 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (2 : ZMod 8560070626452379) ^ 778188238768398 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (2 : ZMod 8560070626452379) ^ 7831720609746 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (2 : ZMod 8560070626452379) ^ 72138 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourCX_10803717004655213 : Nat.Prime 10803717004655213 := by
  apply lucas_primality 10803717004655213 (2 : ZMod 10803717004655213)
  · rw [← oneHundredFourCXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (11, 1), (107, 1), (719, 1), (5443, 1), (586367, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (11, 1), (107, 1), (719, 1), (5443, 1), (586367, 1)] : List FactorBlock).map factorBlockValue).prod) = 10803717004655213 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourCX_2
      · exact prime_oneHundredFourCX_11
      · exact prime_oneHundredFourCX_107
      · exact prime_oneHundredFourCX_719
      · exact prime_oneHundredFourCX_5443
      · exact prime_oneHundredFourCX_586367
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 10803717004655213) ^ 5401858502327606 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (2 : ZMod 10803717004655213) ^ 982156091332292 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (2 : ZMod 10803717004655213) ^ 100969317800516 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (2 : ZMod 10803717004655213) ^ 15026031995348 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (2 : ZMod 10803717004655213) ^ 1984882786084 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (2 : ZMod 10803717004655213) ^ 18424838036 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourCX_11164177654478881 : Nat.Prime 11164177654478881 := by
  apply lucas_primality 11164177654478881 (11 : ZMod 11164177654478881)
  · rw [← oneHundredFourCXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (5, 1), (53597, 1), (433955323, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (5, 1), (53597, 1), (433955323, 1)] : List FactorBlock).map factorBlockValue).prod) = 11164177654478881 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourCX_2
      · exact prime_oneHundredFourCX_3
      · exact prime_oneHundredFourCX_5
      · exact prime_oneHundredFourCX_53597
      · exact prime_oneHundredFourCX_433955323
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 11164177654478881) ^ 5582088827239440 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (11 : ZMod 11164177654478881) ^ 3721392551492960 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (11 : ZMod 11164177654478881) ^ 2232835530895776 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (11 : ZMod 11164177654478881) ^ 208298555040 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (11 : ZMod 11164177654478881) ^ 25726560 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourCX_13310364533096083 : Nat.Prime 13310364533096083 := by
  apply lucas_primality 13310364533096083 (3 : ZMod 13310364533096083)
  · rw [← oneHundredFourCXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (397, 1), (398407, 1), (14025593, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (397, 1), (398407, 1), (14025593, 1)] : List FactorBlock).map factorBlockValue).prod) = 13310364533096083 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourCX_2
      · exact prime_oneHundredFourCX_3
      · exact prime_oneHundredFourCX_397
      · exact prime_oneHundredFourCX_398407
      · exact prime_oneHundredFourCX_14025593
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 13310364533096083) ^ 6655182266548041 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (3 : ZMod 13310364533096083) ^ 4436788177698694 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (3 : ZMod 13310364533096083) ^ 33527366582106 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (3 : ZMod 13310364533096083) ^ 33408962526 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (3 : ZMod 13310364533096083) ^ 949005474 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourCX_16356802009660531 : Nat.Prime 16356802009660531 := by
  apply lucas_primality 16356802009660531 (2 : ZMod 16356802009660531)
  · rw [← oneHundredFourCXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (11, 1), (43, 1), (1152699225487, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (11, 1), (43, 1), (1152699225487, 1)] : List FactorBlock).map factorBlockValue).prod) = 16356802009660531 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourCX_2
      · exact prime_oneHundredFourCX_3
      · exact prime_oneHundredFourCX_5
      · exact prime_oneHundredFourCX_11
      · exact prime_oneHundredFourCX_43
      · exact prime_oneHundredFourCX_1152699225487
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 16356802009660531) ^ 8178401004830265 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (2 : ZMod 16356802009660531) ^ 5452267336553510 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (2 : ZMod 16356802009660531) ^ 3271360401932106 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (2 : ZMod 16356802009660531) ^ 1486982000878230 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (2 : ZMod 16356802009660531) ^ 380390744410710 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (2 : ZMod 16356802009660531) ^ 14190 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourCX_26010350623398439 : Nat.Prime 26010350623398439 := by
  apply lucas_primality 26010350623398439 (3 : ZMod 26010350623398439)
  · rw [← oneHundredFourCXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (11, 1), (251, 1), (5717, 1), (91545943, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (11, 1), (251, 1), (5717, 1), (91545943, 1)] : List FactorBlock).map factorBlockValue).prod) = 26010350623398439 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourCX_2
      · exact prime_oneHundredFourCX_3
      · exact prime_oneHundredFourCX_11
      · exact prime_oneHundredFourCX_251
      · exact prime_oneHundredFourCX_5717
      · exact prime_oneHundredFourCX_91545943
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 26010350623398439) ^ 13005175311699219 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (3 : ZMod 26010350623398439) ^ 8670116874466146 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (3 : ZMod 26010350623398439) ^ 2364577329399858 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (3 : ZMod 26010350623398439) ^ 103626894913938 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (3 : ZMod 26010350623398439) ^ 4549650275214 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (3 : ZMod 26010350623398439) ^ 284123466 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourCX_31763930413152169 : Nat.Prime 31763930413152169 := by
  apply lucas_primality 31763930413152169 (23 : ZMod 31763930413152169)
  · rw [← oneHundredFourCXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 3), (7, 2), (11, 1), (17, 1), (6101, 1), (2630521, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 3), (7, 2), (11, 1), (17, 1), (6101, 1), (2630521, 1)] : List FactorBlock).map factorBlockValue).prod) = 31763930413152169 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourCX_2
      · exact prime_oneHundredFourCX_3
      · exact prime_oneHundredFourCX_7
      · exact prime_oneHundredFourCX_11
      · exact prime_oneHundredFourCX_17
      · exact prime_oneHundredFourCX_6101
      · exact prime_oneHundredFourCX_2630521
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (23 : ZMod 31763930413152169) ^ 15881965206576084 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (23 : ZMod 31763930413152169) ^ 10587976804384056 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (23 : ZMod 31763930413152169) ^ 4537704344736024 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (23 : ZMod 31763930413152169) ^ 2887630037559288 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (23 : ZMod 31763930413152169) ^ 1868466494891304 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (23 : ZMod 31763930413152169) ^ 5206348207368 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (23 : ZMod 31763930413152169) ^ 12075148008 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourCX_37051420944511243 : Nat.Prime 37051420944511243 := by
  apply lucas_primality 37051420944511243 (3 : ZMod 37051420944511243)
  · rw [← oneHundredFourCXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (131, 1), (170603, 1), (92103133, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (131, 1), (170603, 1), (92103133, 1)] : List FactorBlock).map factorBlockValue).prod) = 37051420944511243 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourCX_2
      · exact prime_oneHundredFourCX_3
      · exact prime_oneHundredFourCX_131
      · exact prime_oneHundredFourCX_170603
      · exact prime_oneHundredFourCX_92103133
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 37051420944511243) ^ 18525710472255621 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (3 : ZMod 37051420944511243) ^ 12350473648170414 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (3 : ZMod 37051420944511243) ^ 282835274385582 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (3 : ZMod 37051420944511243) ^ 217179187614 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (3 : ZMod 37051420944511243) ^ 402281874 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourCX_53635814563226921 : Nat.Prime 53635814563226921 := by
  apply lucas_primality 53635814563226921 (3 : ZMod 53635814563226921)
  · rw [← oneHundredFourCXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (16067, 1), (83456486219, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (16067, 1), (83456486219, 1)] : List FactorBlock).map factorBlockValue).prod) = 53635814563226921 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourCX_2
      · exact prime_oneHundredFourCX_5
      · exact prime_oneHundredFourCX_16067
      · exact prime_oneHundredFourCX_83456486219
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 53635814563226921) ^ 26817907281613460 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (3 : ZMod 53635814563226921) ^ 10727162912645384 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (3 : ZMod 53635814563226921) ^ 3338259448760 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (3 : ZMod 53635814563226921) ^ 642680 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourCX_55070634248535781 : Nat.Prime 55070634248535781 := by
  apply lucas_primality 55070634248535781 (11 : ZMod 55070634248535781)
  · rw [← oneHundredFourCXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (5, 1), (7, 1), (167, 1), (87239226703, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (5, 1), (7, 1), (167, 1), (87239226703, 1)] : List FactorBlock).map factorBlockValue).prod) = 55070634248535781 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourCX_2
      · exact prime_oneHundredFourCX_3
      · exact prime_oneHundredFourCX_5
      · exact prime_oneHundredFourCX_7
      · exact prime_oneHundredFourCX_167
      · exact prime_oneHundredFourCX_87239226703
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 55070634248535781) ^ 27535317124267890 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (11 : ZMod 55070634248535781) ^ 18356878082845260 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (11 : ZMod 55070634248535781) ^ 11014126849707156 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (11 : ZMod 55070634248535781) ^ 7867233464076540 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (11 : ZMod 55070634248535781) ^ 329764276937340 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (11 : ZMod 55070634248535781) ^ 631260 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourCX_66601208358624913 : Nat.Prime 66601208358624913 := by
  apply lucas_primality 66601208358624913 (11 : ZMod 66601208358624913)
  · rw [← oneHundredFourCXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (7, 2), (1031, 1), (4729, 1), (5807869, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (7, 2), (1031, 1), (4729, 1), (5807869, 1)] : List FactorBlock).map factorBlockValue).prod) = 66601208358624913 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourCX_2
      · exact prime_oneHundredFourCX_3
      · exact prime_oneHundredFourCX_7
      · exact prime_oneHundredFourCX_1031
      · exact prime_oneHundredFourCX_4729
      · exact prime_oneHundredFourCX_5807869
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 66601208358624913) ^ 33300604179312456 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (11 : ZMod 66601208358624913) ^ 22200402786208304 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (11 : ZMod 66601208358624913) ^ 9514458336946416 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (11 : ZMod 66601208358624913) ^ 64598650202352 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (11 : ZMod 66601208358624913) ^ 14083571232528 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (11 : ZMod 66601208358624913) ^ 11467408848 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourCX_70075919093336591 : Nat.Prime 70075919093336591 := by
  apply lucas_primality 70075919093336591 (14 : ZMod 70075919093336591)
  · rw [← oneHundredFourCXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 1), (31, 1), (24841, 1), (1299989947, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 1), (31, 1), (24841, 1), (1299989947, 1)] : List FactorBlock).map factorBlockValue).prod) = 70075919093336591 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourCX_2
      · exact prime_oneHundredFourCX_5
      · exact prime_oneHundredFourCX_7
      · exact prime_oneHundredFourCX_31
      · exact prime_oneHundredFourCX_24841
      · exact prime_oneHundredFourCX_1299989947
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (14 : ZMod 70075919093336591) ^ 35037959546668295 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (14 : ZMod 70075919093336591) ^ 14015183818667318 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (14 : ZMod 70075919093336591) ^ 10010845584762370 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (14 : ZMod 70075919093336591) ^ 2260513519139890 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (14 : ZMod 70075919093336591) ^ 2820978184990 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (14 : ZMod 70075919093336591) ^ 53904970 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourCX_83886273557254331 : Nat.Prime 83886273557254331 := by
  apply lucas_primality 83886273557254331 (6 : ZMod 83886273557254331)
  · rw [← oneHundredFourCXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (17, 1), (173, 1), (2852304439213, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (17, 1), (173, 1), (2852304439213, 1)] : List FactorBlock).map factorBlockValue).prod) = 83886273557254331 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourCX_2
      · exact prime_oneHundredFourCX_5
      · exact prime_oneHundredFourCX_17
      · exact prime_oneHundredFourCX_173
      · exact prime_oneHundredFourCX_2852304439213
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 83886273557254331) ^ 41943136778627165 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (6 : ZMod 83886273557254331) ^ 16777254711450866 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (6 : ZMod 83886273557254331) ^ 4934486679838490 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (6 : ZMod 83886273557254331) ^ 484891754666210 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (6 : ZMod 83886273557254331) ^ 29410 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourCX_85276442657439379 : Nat.Prime 85276442657439379 := by
  apply lucas_primality 85276442657439379 (3 : ZMod 85276442657439379)
  · rw [← oneHundredFourCXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (4737580147635521, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (4737580147635521, 1)] : List FactorBlock).map factorBlockValue).prod) = 85276442657439379 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFourCX_2
      · exact prime_oneHundredFourCX_3
      · exact prime_oneHundredFourCX_4737580147635521
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 85276442657439379) ^ 42638221328719689 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (3 : ZMod 85276442657439379) ^ 28425480885813126 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (3 : ZMod 85276442657439379) ^ 18 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourCX_86863664744673079 : Nat.Prime 86863664744673079 := by
  apply lucas_primality 86863664744673079 (3 : ZMod 86863664744673079)
  · rw [← oneHundredFourCXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (37, 1), (391277769120149, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (37, 1), (391277769120149, 1)] : List FactorBlock).map factorBlockValue).prod) = 86863664744673079 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourCX_2
      · exact prime_oneHundredFourCX_3
      · exact prime_oneHundredFourCX_37
      · exact prime_oneHundredFourCX_391277769120149
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 86863664744673079) ^ 43431832372336539 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (3 : ZMod 86863664744673079) ^ 28954554914891026 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (3 : ZMod 86863664744673079) ^ 2347666614720894 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (3 : ZMod 86863664744673079) ^ 222 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourCX_87202404512886353 : Nat.Prime 87202404512886353 := by
  apply lucas_primality 87202404512886353 (3 : ZMod 87202404512886353)
  · rw [← oneHundredFourCXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (23, 1), (47, 1), (113, 1), (251, 1), (10333, 1), (17203, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (23, 1), (47, 1), (113, 1), (251, 1), (10333, 1), (17203, 1)] : List FactorBlock).map factorBlockValue).prod) = 87202404512886353 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourCX_2
      · exact prime_oneHundredFourCX_23
      · exact prime_oneHundredFourCX_47
      · exact prime_oneHundredFourCX_113
      · exact prime_oneHundredFourCX_251
      · exact prime_oneHundredFourCX_10333
      · exact prime_oneHundredFourCX_17203
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 87202404512886353) ^ 43601202256443176 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (3 : ZMod 87202404512886353) ^ 3791408891864624 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (3 : ZMod 87202404512886353) ^ 1855370308784816 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (3 : ZMod 87202404512886353) ^ 771702694804304 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (3 : ZMod 87202404512886353) ^ 347419938298352 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (3 : ZMod 87202404512886353) ^ 8439214604944 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (3 : ZMod 87202404512886353) ^ 5069023107184 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourCX_88424436268679879 : Nat.Prime 88424436268679879 := by
  apply lucas_primality 88424436268679879 (7 : ZMod 88424436268679879)
  · rw [← oneHundredFourCXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (2677099, 1), (16514973161, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (2677099, 1), (16514973161, 1)] : List FactorBlock).map factorBlockValue).prod) = 88424436268679879 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFourCX_2
      · exact prime_oneHundredFourCX_2677099
      · exact prime_oneHundredFourCX_16514973161
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 88424436268679879) ^ 44212218134339939 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (7 : ZMod 88424436268679879) ^ 33029946322 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (7 : ZMod 88424436268679879) ^ 5354198 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourCX_174404809025772707 : Nat.Prime 174404809025772707 := by
  apply lucas_primality 174404809025772707 (2 : ZMod 174404809025772707)
  · rw [← oneHundredFourCXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (87202404512886353, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (87202404512886353, 1)] : List FactorBlock).map factorBlockValue).prod) = 174404809025772707 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredFourCX_2
      · exact prime_oneHundredFourCX_87202404512886353
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 174404809025772707) ^ 87202404512886353 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (2 : ZMod 174404809025772707) ^ 2 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourCX_177112743868002511 : Nat.Prime 177112743868002511 := by
  apply lucas_primality 177112743868002511 (6 : ZMod 177112743868002511)
  · rw [← oneHundredFourCXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (281, 1), (678593, 1), (10320283, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (281, 1), (678593, 1), (10320283, 1)] : List FactorBlock).map factorBlockValue).prod) = 177112743868002511 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourCX_2
      · exact prime_oneHundredFourCX_3
      · exact prime_oneHundredFourCX_5
      · exact prime_oneHundredFourCX_281
      · exact prime_oneHundredFourCX_678593
      · exact prime_oneHundredFourCX_10320283
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 177112743868002511) ^ 88556371934001255 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (6 : ZMod 177112743868002511) ^ 59037581289334170 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (6 : ZMod 177112743868002511) ^ 35422548773600502 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (6 : ZMod 177112743868002511) ^ 630294462163710 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (6 : ZMod 177112743868002511) ^ 260999957070 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (6 : ZMod 177112743868002511) ^ 17161616970 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourCX_198950482390006177 : Nat.Prime 198950482390006177 := by
  apply lucas_primality 198950482390006177 (5 : ZMod 198950482390006177)
  · rw [← oneHundredFourCXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (47, 1), (52757, 1), (835787389, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (47, 1), (52757, 1), (835787389, 1)] : List FactorBlock).map factorBlockValue).prod) = 198950482390006177 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourCX_2
      · exact prime_oneHundredFourCX_3
      · exact prime_oneHundredFourCX_47
      · exact prime_oneHundredFourCX_52757
      · exact prime_oneHundredFourCX_835787389
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 198950482390006177) ^ 99475241195003088 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (5 : ZMod 198950482390006177) ^ 66316827463335392 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (5 : ZMod 198950482390006177) ^ 4232988987021408 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (5 : ZMod 198950482390006177) ^ 3771072699168 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (5 : ZMod 198950482390006177) ^ 238039584 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourCX_265946010870138941 : Nat.Prime 265946010870138941 := by
  apply lucas_primality 265946010870138941 (2 : ZMod 265946010870138941)
  · rw [← oneHundredFourCXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (11, 2), (131, 1), (631, 1), (12073, 1), (110119, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (11, 2), (131, 1), (631, 1), (12073, 1), (110119, 1)] : List FactorBlock).map factorBlockValue).prod) = 265946010870138941 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourCX_2
      · exact prime_oneHundredFourCX_5
      · exact prime_oneHundredFourCX_11
      · exact prime_oneHundredFourCX_131
      · exact prime_oneHundredFourCX_631
      · exact prime_oneHundredFourCX_12073
      · exact prime_oneHundredFourCX_110119
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 265946010870138941) ^ 132973005435069470 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (2 : ZMod 265946010870138941) ^ 53189202174027788 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (2 : ZMod 265946010870138941) ^ 24176910079103540 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (2 : ZMod 265946010870138941) ^ 2030122220382740 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (2 : ZMod 265946010870138941) ^ 421467529112740 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (2 : ZMod 265946010870138941) ^ 22028162914780 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (2 : ZMod 265946010870138941) ^ 2415078332260 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourCX_402278543675223311 : Nat.Prime 402278543675223311 := by
  apply lucas_primality 402278543675223311 (13 : ZMod 402278543675223311)
  · rw [← oneHundredFourCXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (359, 1), (1543, 1), (72621713963, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (359, 1), (1543, 1), (72621713963, 1)] : List FactorBlock).map factorBlockValue).prod) = 402278543675223311 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourCX_2
      · exact prime_oneHundredFourCX_5
      · exact prime_oneHundredFourCX_359
      · exact prime_oneHundredFourCX_1543
      · exact prime_oneHundredFourCX_72621713963
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 402278543675223311) ^ 201139271837611655 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (13 : ZMod 402278543675223311) ^ 80455708735044662 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (13 : ZMod 402278543675223311) ^ 1120553046449090 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (13 : ZMod 402278543675223311) ^ 260711953127170 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (13 : ZMod 402278543675223311) ^ 5539370 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourCX_404604471794112671 : Nat.Prime 404604471794112671 := by
  apply lucas_primality 404604471794112671 (11 : ZMod 404604471794112671)
  · rw [← oneHundredFourCXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (17, 2), (688217, 1), (203426459, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (17, 2), (688217, 1), (203426459, 1)] : List FactorBlock).map factorBlockValue).prod) = 404604471794112671 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourCX_2
      · exact prime_oneHundredFourCX_5
      · exact prime_oneHundredFourCX_17
      · exact prime_oneHundredFourCX_688217
      · exact prime_oneHundredFourCX_203426459
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 404604471794112671) ^ 202302235897056335 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (11 : ZMod 404604471794112671) ^ 80920894358822534 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (11 : ZMod 404604471794112671) ^ 23800263046712510 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (11 : ZMod 404604471794112671) ^ 587902466510 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (11 : ZMod 404604471794112671) ^ 1988947130 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourCX_467644591344983909 : Nat.Prime 467644591344983909 := by
  apply lucas_primality 467644591344983909 (2 : ZMod 467644591344983909)
  · rw [← oneHundredFourCXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (4733, 1), (7919, 1), (3119242051, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (4733, 1), (7919, 1), (3119242051, 1)] : List FactorBlock).map factorBlockValue).prod) = 467644591344983909 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourCX_2
      · exact prime_oneHundredFourCX_4733
      · exact prime_oneHundredFourCX_7919
      · exact prime_oneHundredFourCX_3119242051
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 467644591344983909) ^ 233822295672491954 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (2 : ZMod 467644591344983909) ^ 98805111207476 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (2 : ZMod 467644591344983909) ^ 59053490509532 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (2 : ZMod 467644591344983909) ^ 149922508 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourCX_512949524250042317 : Nat.Prime 512949524250042317 := by
  apply lucas_primality 512949524250042317 (2 : ZMod 512949524250042317)
  · rw [← oneHundredFourCXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (29, 1), (2775559, 1), (1593184889, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (29, 1), (2775559, 1), (1593184889, 1)] : List FactorBlock).map factorBlockValue).prod) = 512949524250042317 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourCX_2
      · exact prime_oneHundredFourCX_29
      · exact prime_oneHundredFourCX_2775559
      · exact prime_oneHundredFourCX_1593184889
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 512949524250042317) ^ 256474762125021158 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (2 : ZMod 512949524250042317) ^ 17687914629311804 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (2 : ZMod 512949524250042317) ^ 184809447124 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (2 : ZMod 512949524250042317) ^ 321964844 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourCX_632225841986292193 : Nat.Prime 632225841986292193 := by
  apply lucas_primality 632225841986292193 (5 : ZMod 632225841986292193)
  · rw [← oneHundredFourCXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 2), (1100041, 1), (1995587999, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 2), (1100041, 1), (1995587999, 1)] : List FactorBlock).map factorBlockValue).prod) = 632225841986292193 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourCX_2
      · exact prime_oneHundredFourCX_3
      · exact prime_oneHundredFourCX_1100041
      · exact prime_oneHundredFourCX_1995587999
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 632225841986292193) ^ 316112920993146096 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (5 : ZMod 632225841986292193) ^ 210741947328764064 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (5 : ZMod 632225841986292193) ^ 574729343712 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (5 : ZMod 632225841986292193) ^ 316811808 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourCX_1473596414167950607 : Nat.Prime 1473596414167950607 := by
  apply lucas_primality 1473596414167950607 (3 : ZMod 1473596414167950607)
  · rw [← oneHundredFourCXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (109, 1), (173, 1), (883, 1), (14750067271, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (109, 1), (173, 1), (883, 1), (14750067271, 1)] : List FactorBlock).map factorBlockValue).prod) = 1473596414167950607 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourCX_2
      · exact prime_oneHundredFourCX_3
      · exact prime_oneHundredFourCX_109
      · exact prime_oneHundredFourCX_173
      · exact prime_oneHundredFourCX_883
      · exact prime_oneHundredFourCX_14750067271
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1473596414167950607) ^ 736798207083975303 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (3 : ZMod 1473596414167950607) ^ 491198804722650202 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (3 : ZMod 1473596414167950607) ^ 13519233157504134 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (3 : ZMod 1473596414167950607) ^ 8517898347791622 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (3 : ZMod 1473596414167950607) ^ 1668852111175482 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (3 : ZMod 1473596414167950607) ^ 99904386 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourCX_1541977758959001869 : Nat.Prime 1541977758959001869 := by
  apply lucas_primality 1541977758959001869 (2 : ZMod 1541977758959001869)
  · rw [← oneHundredFourCXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (55070634248535781, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (55070634248535781, 1)] : List FactorBlock).map factorBlockValue).prod) = 1541977758959001869 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFourCX_2
      · exact prime_oneHundredFourCX_7
      · exact prime_oneHundredFourCX_55070634248535781
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 1541977758959001869) ^ 770988879479500934 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (2 : ZMod 1541977758959001869) ^ 220282536994143124 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (2 : ZMod 1541977758959001869) ^ 28 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourCX_2220502305087140441 : Nat.Prime 2220502305087140441 := by
  apply lucas_primality 2220502305087140441 (3 : ZMod 2220502305087140441)
  · rw [← oneHundredFourCXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (101, 1), (191, 1), (48017, 1), (59929613, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (101, 1), (191, 1), (48017, 1), (59929613, 1)] : List FactorBlock).map factorBlockValue).prod) = 2220502305087140441 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourCX_2
      · exact prime_oneHundredFourCX_5
      · exact prime_oneHundredFourCX_101
      · exact prime_oneHundredFourCX_191
      · exact prime_oneHundredFourCX_48017
      · exact prime_oneHundredFourCX_59929613
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 2220502305087140441) ^ 1110251152543570220 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (3 : ZMod 2220502305087140441) ^ 444100461017428088 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (3 : ZMod 2220502305087140441) ^ 21985171337496440 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (3 : ZMod 2220502305087140441) ^ 11625666518780840 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (3 : ZMod 2220502305087140441) ^ 46244086575320 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (3 : ZMod 2220502305087140441) ^ 37051837880 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourCX_2427626830764676027 : Nat.Prime 2427626830764676027 := by
  apply lucas_primality 2427626830764676027 (2 : ZMod 2427626830764676027)
  · rw [← oneHundredFourCXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (404604471794112671, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (404604471794112671, 1)] : List FactorBlock).map factorBlockValue).prod) = 2427626830764676027 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFourCX_2
      · exact prime_oneHundredFourCX_3
      · exact prime_oneHundredFourCX_404604471794112671
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 2427626830764676027) ^ 1213813415382338013 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (2 : ZMod 2427626830764676027) ^ 809208943588225342 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (2 : ZMod 2427626830764676027) ^ 6 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourCX_2927544154246713619 : Nat.Prime 2927544154246713619 := by
  apply lucas_primality 2927544154246713619 (3 : ZMod 2927544154246713619)
  · rw [← oneHundredFourCXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (19, 1), (8560070626452379, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (19, 1), (8560070626452379, 1)] : List FactorBlock).map factorBlockValue).prod) = 2927544154246713619 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourCX_2
      · exact prime_oneHundredFourCX_3
      · exact prime_oneHundredFourCX_19
      · exact prime_oneHundredFourCX_8560070626452379
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 2927544154246713619) ^ 1463772077123356809 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (3 : ZMod 2927544154246713619) ^ 975848051415571206 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (3 : ZMod 2927544154246713619) ^ 154081271276142822 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (3 : ZMod 2927544154246713619) ^ 342 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourCX_3014995691311940443 : Nat.Prime 3014995691311940443 := by
  apply lucas_primality 3014995691311940443 (2 : ZMod 3014995691311940443)
  · rw [← oneHundredFourCXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (321187, 1), (1564506913061, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (321187, 1), (1564506913061, 1)] : List FactorBlock).map factorBlockValue).prod) = 3014995691311940443 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourCX_2
      · exact prime_oneHundredFourCX_3
      · exact prime_oneHundredFourCX_321187
      · exact prime_oneHundredFourCX_1564506913061
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 3014995691311940443) ^ 1507497845655970221 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (2 : ZMod 3014995691311940443) ^ 1004998563770646814 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (2 : ZMod 3014995691311940443) ^ 9387041478366 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (2 : ZMod 3014995691311940443) ^ 1927122 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourCX_3503795954666829551 : Nat.Prime 3503795954666829551 := by
  apply lucas_primality 3503795954666829551 (13 : ZMod 3503795954666829551)
  · rw [← oneHundredFourCXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (70075919093336591, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (70075919093336591, 1)] : List FactorBlock).map factorBlockValue).prod) = 3503795954666829551 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFourCX_2
      · exact prime_oneHundredFourCX_5
      · exact prime_oneHundredFourCX_70075919093336591
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (13 : ZMod 3503795954666829551) ^ 1751897977333414775 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (13 : ZMod 3503795954666829551) ^ 700759190933365910 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (13 : ZMod 3503795954666829551) ^ 50 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourCX_4432517635612128193 : Nat.Prime 4432517635612128193 := by
  apply lucas_primality 4432517635612128193 (22 : ZMod 4432517635612128193)
  · rw [← oneHundredFourCXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 2), (13, 1), (17, 1), (383, 1), (90915292669, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 2), (13, 1), (17, 1), (383, 1), (90915292669, 1)] : List FactorBlock).map factorBlockValue).prod) = 4432517635612128193 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourCX_2
      · exact prime_oneHundredFourCX_3
      · exact prime_oneHundredFourCX_13
      · exact prime_oneHundredFourCX_17
      · exact prime_oneHundredFourCX_383
      · exact prime_oneHundredFourCX_90915292669
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (22 : ZMod 4432517635612128193) ^ 2216258817806064096 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (22 : ZMod 4432517635612128193) ^ 1477505878537376064 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (22 : ZMod 4432517635612128193) ^ 340962895047086784 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (22 : ZMod 4432517635612128193) ^ 260736331506595776 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (22 : ZMod 4432517635612128193) ^ 11573153095593024 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (22 : ZMod 4432517635612128193) ^ 48754368 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourCX_7270706726899630967 : Nat.Prime 7270706726899630967 := by
  apply lucas_primality 7270706726899630967 (5 : ZMod 7270706726899630967)
  · rw [← oneHundredFourCXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (337, 1), (15373, 1), (134171, 1), (747139, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (337, 1), (15373, 1), (134171, 1), (747139, 1)] : List FactorBlock).map factorBlockValue).prod) = 7270706726899630967 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourCX_2
      · exact prime_oneHundredFourCX_7
      · exact prime_oneHundredFourCX_337
      · exact prime_oneHundredFourCX_15373
      · exact prime_oneHundredFourCX_134171
      · exact prime_oneHundredFourCX_747139
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 7270706726899630967) ^ 3635353363449815483 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (5 : ZMod 7270706726899630967) ^ 1038672389557090138 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (5 : ZMod 7270706726899630967) ^ 21574797409197718 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (5 : ZMod 7270706726899630967) ^ 472953016776142 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (5 : ZMod 7270706726899630967) ^ 54189852702146 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (5 : ZMod 7270706726899630967) ^ 9731397674194 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourCX_9310276483619584019 : Nat.Prime 9310276483619584019 := by
  apply lucas_primality 9310276483619584019 (2 : ZMod 9310276483619584019)
  · rw [← oneHundredFourCXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (13, 2), (101, 1), (37573, 1), (1036932751, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (13, 2), (101, 1), (37573, 1), (1036932751, 1)] : List FactorBlock).map factorBlockValue).prod) = 9310276483619584019 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourCX_2
      · exact prime_oneHundredFourCX_7
      · exact prime_oneHundredFourCX_13
      · exact prime_oneHundredFourCX_101
      · exact prime_oneHundredFourCX_37573
      · exact prime_oneHundredFourCX_1036932751
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 9310276483619584019) ^ 4655138241809792009 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (2 : ZMod 9310276483619584019) ^ 1330039497659940574 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (2 : ZMod 9310276483619584019) ^ 716175114124583386 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (2 : ZMod 9310276483619584019) ^ 92180955283362218 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (2 : ZMod 9310276483619584019) ^ 247791671775466 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (2 : ZMod 9310276483619584019) ^ 8978669518 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourCX_11015949079422186197 : Nat.Prime 11015949079422186197 := by
  apply lucas_primality 11015949079422186197 (2 : ZMod 11015949079422186197)
  · rw [← oneHundredFourCXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (11, 1), (56821, 1), (4406161086179, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (11, 1), (56821, 1), (4406161086179, 1)] : List FactorBlock).map factorBlockValue).prod) = 11015949079422186197 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourCX_2
      · exact prime_oneHundredFourCX_11
      · exact prime_oneHundredFourCX_56821
      · exact prime_oneHundredFourCX_4406161086179
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 11015949079422186197) ^ 5507974539711093098 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (2 : ZMod 11015949079422186197) ^ 1001449916311107836 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (2 : ZMod 11015949079422186197) ^ 193871087791876 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (2 : ZMod 11015949079422186197) ^ 2500124 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourCX_11501317095805079167 : Nat.Prime 11501317095805079167 := by
  apply lucas_primality 11501317095805079167 (5 : ZMod 11501317095805079167)
  · rw [← oneHundredFourCXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (13, 1), (19, 1), (23, 1), (32779, 1), (33739, 1), (305101, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (13, 1), (19, 1), (23, 1), (32779, 1), (33739, 1), (305101, 1)] : List FactorBlock).map factorBlockValue).prod) = 11501317095805079167 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourCX_2
      · exact prime_oneHundredFourCX_3
      · exact prime_oneHundredFourCX_13
      · exact prime_oneHundredFourCX_19
      · exact prime_oneHundredFourCX_23
      · exact prime_oneHundredFourCX_32779
      · exact prime_oneHundredFourCX_33739
      · exact prime_oneHundredFourCX_305101
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 11501317095805079167) ^ 5750658547902539583 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (5 : ZMod 11501317095805079167) ^ 3833772365268359722 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (5 : ZMod 11501317095805079167) ^ 884716699677313782 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (5 : ZMod 11501317095805079167) ^ 605332478726583114 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (5 : ZMod 11501317095805079167) ^ 500057265035003442 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (5 : ZMod 11501317095805079167) ^ 350874556752954 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (5 : ZMod 11501317095805079167) ^ 340890870974394 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (5 : ZMod 11501317095805079167) ^ 37696753192566 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourCX_13749157589070950251 : Nat.Prime 13749157589070950251 := by
  apply lucas_primality 13749157589070950251 (7 : ZMod 13749157589070950251)
  · rw [← oneHundredFourCXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 3), (43, 1), (12911, 1), (33020716279, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 3), (43, 1), (12911, 1), (33020716279, 1)] : List FactorBlock).map factorBlockValue).prod) = 13749157589070950251 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourCX_2
      · exact prime_oneHundredFourCX_3
      · exact prime_oneHundredFourCX_5
      · exact prime_oneHundredFourCX_43
      · exact prime_oneHundredFourCX_12911
      · exact prime_oneHundredFourCX_33020716279
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 13749157589070950251) ^ 6874578794535475125 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (7 : ZMod 13749157589070950251) ^ 4583052529690316750 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (7 : ZMod 13749157589070950251) ^ 2749831517814190050 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (7 : ZMod 13749157589070950251) ^ 319747850908626750 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (7 : ZMod 13749157589070950251) ^ 1064918099997750 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (7 : ZMod 13749157589070950251) ^ 416379750 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourCX_16575338863089261599 : Nat.Prime 16575338863089261599 := by
  apply lucas_primality 16575338863089261599 (7 : ZMod 16575338863089261599)
  · rw [← oneHundredFourCXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (8422787, 1), (140565441811, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (8422787, 1), (140565441811, 1)] : List FactorBlock).map factorBlockValue).prod) = 16575338863089261599 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourCX_2
      · exact prime_oneHundredFourCX_7
      · exact prime_oneHundredFourCX_8422787
      · exact prime_oneHundredFourCX_140565441811
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 16575338863089261599) ^ 8287669431544630799 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (7 : ZMod 16575338863089261599) ^ 2367905551869894514 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (7 : ZMod 16575338863089261599) ^ 1967916185354 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (7 : ZMod 16575338863089261599) ^ 117919018 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourCX_38447018787178690537 : Nat.Prime 38447018787178690537 := by
  apply lucas_primality 38447018787178690537 (5 : ZMod 38447018787178690537)
  · rw [← oneHundredFourCXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (499, 1), (38333, 1), (41513, 1), (2017409, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (499, 1), (38333, 1), (41513, 1), (2017409, 1)] : List FactorBlock).map factorBlockValue).prod) = 38447018787178690537 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourCX_2
      · exact prime_oneHundredFourCX_3
      · exact prime_oneHundredFourCX_499
      · exact prime_oneHundredFourCX_38333
      · exact prime_oneHundredFourCX_41513
      · exact prime_oneHundredFourCX_2017409
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 38447018787178690537) ^ 19223509393589345268 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (5 : ZMod 38447018787178690537) ^ 12815672929059563512 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (5 : ZMod 38447018787178690537) ^ 77048133842041464 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (5 : ZMod 38447018787178690537) ^ 1002974429008392 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (5 : ZMod 38447018787178690537) ^ 926144070223272 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (5 : ZMod 38447018787178690537) ^ 19057622320104 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourCX_43392789259089243619 : Nat.Prime 43392789259089243619 := by
  apply lucas_primality 43392789259089243619 (2 : ZMod 43392789259089243619)
  · rw [← oneHundredFourCXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (317, 1), (433, 1), (52688903207623, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (317, 1), (433, 1), (52688903207623, 1)] : List FactorBlock).map factorBlockValue).prod) = 43392789259089243619 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourCX_2
      · exact prime_oneHundredFourCX_3
      · exact prime_oneHundredFourCX_317
      · exact prime_oneHundredFourCX_433
      · exact prime_oneHundredFourCX_52688903207623
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 43392789259089243619) ^ 21696394629544621809 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (2 : ZMod 43392789259089243619) ^ 14464263086363081206 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (2 : ZMod 43392789259089243619) ^ 136885770533404554 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (2 : ZMod 43392789259089243619) ^ 100214293900898946 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (2 : ZMod 43392789259089243619) ^ 823566 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourCX_47520047431952049571 : Nat.Prime 47520047431952049571 := by
  apply lucas_primality 47520047431952049571 (3 : ZMod 47520047431952049571)
  · rw [← oneHundredFourCXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (7, 1), (11, 1), (61, 1), (359, 1), (1993, 1), (2423, 1), (194527, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (7, 1), (11, 1), (61, 1), (359, 1), (1993, 1), (2423, 1), (194527, 1)] : List FactorBlock).map factorBlockValue).prod) = 47520047431952049571 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourCX_2
      · exact prime_oneHundredFourCX_3
      · exact prime_oneHundredFourCX_5
      · exact prime_oneHundredFourCX_7
      · exact prime_oneHundredFourCX_11
      · exact prime_oneHundredFourCX_61
      · exact prime_oneHundredFourCX_359
      · exact prime_oneHundredFourCX_1993
      · exact prime_oneHundredFourCX_2423
      · exact prime_oneHundredFourCX_194527
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 47520047431952049571) ^ 23760023715976024785 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (3 : ZMod 47520047431952049571) ^ 15840015810650683190 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (3 : ZMod 47520047431952049571) ^ 9504009486390409914 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (3 : ZMod 47520047431952049571) ^ 6788578204564578510 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (3 : ZMod 47520047431952049571) ^ 4320004311995640870 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (3 : ZMod 47520047431952049571) ^ 779017171015607370 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (3 : ZMod 47520047431952049571) ^ 132367820144713230 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (3 : ZMod 47520047431952049571) ^ 23843475881561490 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (3 : ZMod 47520047431952049571) ^ 19612070751940590 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (3 : ZMod 47520047431952049571) ^ 244285098890910 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourCX_56118296425536623357 : Nat.Prime 56118296425536623357 := by
  apply lucas_primality 56118296425536623357 (2 : ZMod 56118296425536623357)
  · rw [← oneHundredFourCXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (13, 1), (431, 1), (433, 1), (5782770656261, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (13, 1), (431, 1), (433, 1), (5782770656261, 1)] : List FactorBlock).map factorBlockValue).prod) = 56118296425536623357 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourCX_2
      · exact prime_oneHundredFourCX_13
      · exact prime_oneHundredFourCX_431
      · exact prime_oneHundredFourCX_433
      · exact prime_oneHundredFourCX_5782770656261
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 56118296425536623357) ^ 28059148212768311678 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (2 : ZMod 56118296425536623357) ^ 4316792032733586412 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (2 : ZMod 56118296425536623357) ^ 130204864096372676 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (2 : ZMod 56118296425536623357) ^ 129603455948121532 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (2 : ZMod 56118296425536623357) ^ 9704396 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourCX_56459659197804545503 : Nat.Prime 56459659197804545503 := by
  apply lucas_primality 56459659197804545503 (3 : ZMod 56459659197804545503)
  · rw [← oneHundredFourCXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (47, 1), (1987, 1), (23369, 1), (1437241979, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (47, 1), (1987, 1), (23369, 1), (1437241979, 1)] : List FactorBlock).map factorBlockValue).prod) = 56459659197804545503 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourCX_2
      · exact prime_oneHundredFourCX_3
      · exact prime_oneHundredFourCX_47
      · exact prime_oneHundredFourCX_1987
      · exact prime_oneHundredFourCX_23369
      · exact prime_oneHundredFourCX_1437241979
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 56459659197804545503) ^ 28229829598902272751 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (3 : ZMod 56459659197804545503) ^ 18819886399268181834 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (3 : ZMod 56459659197804545503) ^ 1201269344634139266 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (3 : ZMod 56459659197804545503) ^ 28414524004934346 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (3 : ZMod 56459659197804545503) ^ 2416006641182958 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (3 : ZMod 56459659197804545503) ^ 39283335738 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourCX_63622374740986994431 : Nat.Prime 63622374740986994431 := by
  apply lucas_primality 63622374740986994431 (3 : ZMod 63622374740986994431)
  · rw [← oneHundredFourCXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (1152037, 1), (1840866070013, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (1152037, 1), (1840866070013, 1)] : List FactorBlock).map factorBlockValue).prod) = 63622374740986994431 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourCX_2
      · exact prime_oneHundredFourCX_3
      · exact prime_oneHundredFourCX_5
      · exact prime_oneHundredFourCX_1152037
      · exact prime_oneHundredFourCX_1840866070013
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 63622374740986994431) ^ 31811187370493497215 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (3 : ZMod 63622374740986994431) ^ 21207458246995664810 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (3 : ZMod 63622374740986994431) ^ 12724474948197398886 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (3 : ZMod 63622374740986994431) ^ 55225982100390 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (3 : ZMod 63622374740986994431) ^ 34561110 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourCX_87448879896579462137 : Nat.Prime 87448879896579462137 := by
  apply lucas_primality 87448879896579462137 (3 : ZMod 87448879896579462137)
  · rw [← oneHundredFourCXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (109, 1), (239, 1), (419604237344917, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (109, 1), (239, 1), (419604237344917, 1)] : List FactorBlock).map factorBlockValue).prod) = 87448879896579462137 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourCX_2
      · exact prime_oneHundredFourCX_109
      · exact prime_oneHundredFourCX_239
      · exact prime_oneHundredFourCX_419604237344917
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 87448879896579462137) ^ 43724439948289731068 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (3 : ZMod 87448879896579462137) ^ 802283301803481304 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (3 : ZMod 87448879896579462137) ^ 365894894964767624 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (3 : ZMod 87448879896579462137) ^ 208408 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourCX_97677412978421408647 : Nat.Prime 97677412978421408647 := by
  apply lucas_primality 97677412978421408647 (3 : ZMod 97677412978421408647)
  · rw [← oneHundredFourCXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (3947, 1), (103723, 1), (39764973961, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (3947, 1), (103723, 1), (39764973961, 1)] : List FactorBlock).map factorBlockValue).prod) = 97677412978421408647 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourCX_2
      · exact prime_oneHundredFourCX_3
      · exact prime_oneHundredFourCX_3947
      · exact prime_oneHundredFourCX_103723
      · exact prime_oneHundredFourCX_39764973961
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 97677412978421408647) ^ 48838706489210704323 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (3 : ZMod 97677412978421408647) ^ 32559137659473802882 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (3 : ZMod 97677412978421408647) ^ 24747254364940818 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (3 : ZMod 97677412978421408647) ^ 941714113344402 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (3 : ZMod 97677412978421408647) ^ 2456368086 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourCX_105131039647847779157 : Nat.Prime 105131039647847779157 := by
  apply lucas_primality 105131039647847779157 (2 : ZMod 105131039647847779157)
  · rw [← oneHundredFourCXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (31, 1), (173, 1), (1831, 1), (2676546708113, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (31, 1), (173, 1), (1831, 1), (2676546708113, 1)] : List FactorBlock).map factorBlockValue).prod) = 105131039647847779157 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourCX_2
      · exact prime_oneHundredFourCX_31
      · exact prime_oneHundredFourCX_173
      · exact prime_oneHundredFourCX_1831
      · exact prime_oneHundredFourCX_2676546708113
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 105131039647847779157) ^ 52565519823923889578 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (2 : ZMod 105131039647847779157) ^ 3391323859607992876 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (2 : ZMod 105131039647847779157) ^ 607693870796807972 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (2 : ZMod 105131039647847779157) ^ 57417279982440076 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (2 : ZMod 105131039647847779157) ^ 39278612 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourCX_173900314410901159157 : Nat.Prime 173900314410901159157 := by
  apply lucas_primality 173900314410901159157 (2 : ZMod 173900314410901159157)
  · rw [← oneHundredFourCXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (17, 3), (31, 1), (2903, 1), (98329738021, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (17, 3), (31, 1), (2903, 1), (98329738021, 1)] : List FactorBlock).map factorBlockValue).prod) = 173900314410901159157 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourCX_2
      · exact prime_oneHundredFourCX_17
      · exact prime_oneHundredFourCX_31
      · exact prime_oneHundredFourCX_2903
      · exact prime_oneHundredFourCX_98329738021
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 173900314410901159157) ^ 86950157205450579578 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (2 : ZMod 173900314410901159157) ^ 10229430259464774068 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (2 : ZMod 173900314410901159157) ^ 5609687561641972876 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (2 : ZMod 173900314410901159157) ^ 59903656359249452 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (2 : ZMod 173900314410901159157) ^ 1768542436 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourCX_233280710261778493123 : Nat.Prime 233280710261778493123 := by
  apply lucas_primality 233280710261778493123 (19 : ZMod 233280710261778493123)
  · rw [← oneHundredFourCXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (2377, 1), (16356802009660531, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (2377, 1), (16356802009660531, 1)] : List FactorBlock).map factorBlockValue).prod) = 233280710261778493123 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourCX_2
      · exact prime_oneHundredFourCX_3
      · exact prime_oneHundredFourCX_2377
      · exact prime_oneHundredFourCX_16356802009660531
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (19 : ZMod 233280710261778493123) ^ 116640355130889246561 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (19 : ZMod 233280710261778493123) ^ 77760236753926164374 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (19 : ZMod 233280710261778493123) ^ 98140812057963186 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (19 : ZMod 233280710261778493123) ^ 14262 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourCX_236188911554202791671 : Nat.Prime 236188911554202791671 := by
  apply lucas_primality 236188911554202791671 (6 : ZMod 236188911554202791671)
  · rw [← oneHundredFourCXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (23, 1), (37, 1), (1289, 1), (7177211967551, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (23, 1), (37, 1), (1289, 1), (7177211967551, 1)] : List FactorBlock).map factorBlockValue).prod) = 236188911554202791671 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourCX_2
      · exact prime_oneHundredFourCX_3
      · exact prime_oneHundredFourCX_5
      · exact prime_oneHundredFourCX_23
      · exact prime_oneHundredFourCX_37
      · exact prime_oneHundredFourCX_1289
      · exact prime_oneHundredFourCX_7177211967551
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 236188911554202791671) ^ 118094455777101395835 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (6 : ZMod 236188911554202791671) ^ 78729637184734263890 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (6 : ZMod 236188911554202791671) ^ 47237782310840558334 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (6 : ZMod 236188911554202791671) ^ 10269083111052295290 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (6 : ZMod 236188911554202791671) ^ 6383484096059534910 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (6 : ZMod 236188911554202791671) ^ 183234221531577030 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (6 : ZMod 236188911554202791671) ^ 32908170 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourCX_319893850963802161597 : Nat.Prime 319893850963802161597 := by
  apply lucas_primality 319893850963802161597 (2 : ZMod 319893850963802161597)
  · rw [← oneHundredFourCXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (11, 1), (887, 1), (12155849, 1), (224762081, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (11, 1), (887, 1), (12155849, 1), (224762081, 1)] : List FactorBlock).map factorBlockValue).prod) = 319893850963802161597 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourCX_2
      · exact prime_oneHundredFourCX_3
      · exact prime_oneHundredFourCX_11
      · exact prime_oneHundredFourCX_887
      · exact prime_oneHundredFourCX_12155849
      · exact prime_oneHundredFourCX_224762081
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 319893850963802161597) ^ 159946925481901080798 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (2 : ZMod 319893850963802161597) ^ 106631283654600720532 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (2 : ZMod 319893850963802161597) ^ 29081259178527469236 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (2 : ZMod 319893850963802161597) ^ 360646957118153508 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (2 : ZMod 319893850963802161597) ^ 26316043491804 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (2 : ZMod 319893850963802161597) ^ 1423255424316 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourCX_343619225687246264029 : Nat.Prime 343619225687246264029 := by
  apply lucas_primality 343619225687246264029 (2 : ZMod 343619225687246264029)
  · rw [← oneHundredFourCXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (7, 1), (13, 1), (23, 1), (31, 1), (367, 1), (2411, 1), (166257313, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (7, 1), (13, 1), (23, 1), (31, 1), (367, 1), (2411, 1), (166257313, 1)] : List FactorBlock).map factorBlockValue).prod) = 343619225687246264029 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourCX_2
      · exact prime_oneHundredFourCX_3
      · exact prime_oneHundredFourCX_7
      · exact prime_oneHundredFourCX_13
      · exact prime_oneHundredFourCX_23
      · exact prime_oneHundredFourCX_31
      · exact prime_oneHundredFourCX_367
      · exact prime_oneHundredFourCX_2411
      · exact prime_oneHundredFourCX_166257313
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 343619225687246264029) ^ 171809612843623132014 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (2 : ZMod 343619225687246264029) ^ 114539741895748754676 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (2 : ZMod 343619225687246264029) ^ 49088460812463752004 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (2 : ZMod 343619225687246264029) ^ 26432248129788174156 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (2 : ZMod 343619225687246264029) ^ 14939966334228098436 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (2 : ZMod 343619225687246264029) ^ 11084491151201492388 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (2 : ZMod 343619225687246264029) ^ 936292168085139684 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (2 : ZMod 343619225687246264029) ^ 142521454038675348 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (2 : ZMod 343619225687246264029) ^ 2066791646556 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourCX_601135034269270369663 : Nat.Prime 601135034269270369663 := by
  apply lucas_primality 601135034269270369663 (3 : ZMod 601135034269270369663)
  · rw [← oneHundredFourCXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (101, 1), (142641539, 1), (2318099881, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (101, 1), (142641539, 1), (2318099881, 1)] : List FactorBlock).map factorBlockValue).prod) = 601135034269270369663 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourCX_2
      · exact prime_oneHundredFourCX_3
      · exact prime_oneHundredFourCX_101
      · exact prime_oneHundredFourCX_142641539
      · exact prime_oneHundredFourCX_2318099881
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 601135034269270369663) ^ 300567517134635184831 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (3 : ZMod 601135034269270369663) ^ 200378344756423456554 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (3 : ZMod 601135034269270369663) ^ 5951832022468023462 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (3 : ZMod 601135034269270369663) ^ 4214305583658 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (3 : ZMod 601135034269270369663) ^ 259322317902 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourCX_660497175612044369329 : Nat.Prime 660497175612044369329 := by
  apply lucas_primality 660497175612044369329 (7 : ZMod 660497175612044369329)
  · rw [← oneHundredFourCXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (71, 1), (18913, 1), (10247335520207, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (71, 1), (18913, 1), (10247335520207, 1)] : List FactorBlock).map factorBlockValue).prod) = 660497175612044369329 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourCX_2
      · exact prime_oneHundredFourCX_3
      · exact prime_oneHundredFourCX_71
      · exact prime_oneHundredFourCX_18913
      · exact prime_oneHundredFourCX_10247335520207
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 660497175612044369329) ^ 330248587806022184664 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (7 : ZMod 660497175612044369329) ^ 220165725204014789776 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (7 : ZMod 660497175612044369329) ^ 9302777121296399568 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (7 : ZMod 660497175612044369329) ^ 34922919452865456 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (7 : ZMod 660497175612044369329) ^ 64455504 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourCX_3289376689400252641763 : Nat.Prime 3289376689400252641763 := by
  apply lucas_primality 3289376689400252641763 (2 : ZMod 3289376689400252641763)
  · rw [← oneHundredFourCXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (13, 1), (11501317095805079167, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (13, 1), (11501317095805079167, 1)] : List FactorBlock).map factorBlockValue).prod) = 3289376689400252641763 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourCX_2
      · exact prime_oneHundredFourCX_11
      · exact prime_oneHundredFourCX_13
      · exact prime_oneHundredFourCX_11501317095805079167
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 3289376689400252641763) ^ 1644688344700126320881 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (2 : ZMod 3289376689400252641763) ^ 299034244490932058342 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (2 : ZMod 3289376689400252641763) ^ 253028976107711741674 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (2 : ZMod 3289376689400252641763) ^ 286 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourCX_4735260346317283039861 : Nat.Prime 4735260346317283039861 := by
  apply lucas_primality 4735260346317283039861 (11 : ZMod 4735260346317283039861)
  · rw [← oneHundredFourCXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (5, 1), (46457, 1), (566265620336761, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (5, 1), (46457, 1), (566265620336761, 1)] : List FactorBlock).map factorBlockValue).prod) = 4735260346317283039861 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourCX_2
      · exact prime_oneHundredFourCX_3
      · exact prime_oneHundredFourCX_5
      · exact prime_oneHundredFourCX_46457
      · exact prime_oneHundredFourCX_566265620336761
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 4735260346317283039861) ^ 2367630173158641519930 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (11 : ZMod 4735260346317283039861) ^ 1578420115439094346620 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (11 : ZMod 4735260346317283039861) ^ 947052069263456607972 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (11 : ZMod 4735260346317283039861) ^ 101927811660616980 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (11 : ZMod 4735260346317283039861) ^ 8362260 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourCX_5946523832967403425317 : Nat.Prime 5946523832967403425317 := by
  apply lucas_primality 5946523832967403425317 (2 : ZMod 5946523832967403425317)
  · rw [← oneHundredFourCXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (17, 1), (87448879896579462137, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (17, 1), (87448879896579462137, 1)] : List FactorBlock).map factorBlockValue).prod) = 5946523832967403425317 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFourCX_2
      · exact prime_oneHundredFourCX_17
      · exact prime_oneHundredFourCX_87448879896579462137
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 5946523832967403425317) ^ 2973261916483701712658 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (2 : ZMod 5946523832967403425317) ^ 349795519586317848548 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (2 : ZMod 5946523832967403425317) ^ 68 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourCX_24039619807933217848427 : Nat.Prime 24039619807933217848427 := by
  apply lucas_primality 24039619807933217848427 (2 : ZMod 24039619807933217848427)
  · rw [← oneHundredFourCXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (74293, 1), (7928441, 1), (1855108091, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (74293, 1), (7928441, 1), (1855108091, 1)] : List FactorBlock).map factorBlockValue).prod) = 24039619807933217848427 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourCX_2
      · exact prime_oneHundredFourCX_11
      · exact prime_oneHundredFourCX_74293
      · exact prime_oneHundredFourCX_7928441
      · exact prime_oneHundredFourCX_1855108091
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 24039619807933217848427) ^ 12019809903966608924213 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (2 : ZMod 24039619807933217848427) ^ 2185419982539383440766 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (2 : ZMod 24039619807933217848427) ^ 323578531058554882 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (2 : ZMod 24039619807933217848427) ^ 3032073998902586 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (2 : ZMod 24039619807933217848427) ^ 12958608678686 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourCX_29981494017196436639153 : Nat.Prime 29981494017196436639153 := by
  apply lucas_primality 29981494017196436639153 (3 : ZMod 29981494017196436639153)
  · rw [← oneHundredFourCXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (139, 1), (10831, 1), (16831, 1), (73950312193, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (139, 1), (10831, 1), (16831, 1), (73950312193, 1)] : List FactorBlock).map factorBlockValue).prod) = 29981494017196436639153 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourCX_2
      · exact prime_oneHundredFourCX_139
      · exact prime_oneHundredFourCX_10831
      · exact prime_oneHundredFourCX_16831
      · exact prime_oneHundredFourCX_73950312193
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 29981494017196436639153) ^ 14990747008598218319576 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (3 : ZMod 29981494017196436639153) ^ 215694201562564292368 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (3 : ZMod 29981494017196436639153) ^ 2768118734853331792 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (3 : ZMod 29981494017196436639153) ^ 1781325768949939792 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (3 : ZMod 29981494017196436639153) ^ 405427551664 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourCX_42366396508405186569217 : Nat.Prime 42366396508405186569217 := by
  apply lucas_primality 42366396508405186569217 (11 : ZMod 42366396508405186569217)
  · rw [← oneHundredFourCXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 10), (3, 1), (283, 1), (29567803, 1), (1648142747, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 10), (3, 1), (283, 1), (29567803, 1), (1648142747, 1)] : List FactorBlock).map factorBlockValue).prod) = 42366396508405186569217 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourCX_2
      · exact prime_oneHundredFourCX_3
      · exact prime_oneHundredFourCX_283
      · exact prime_oneHundredFourCX_29567803
      · exact prime_oneHundredFourCX_1648142747
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 42366396508405186569217) ^ 21183198254202593284608 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (11 : ZMod 42366396508405186569217) ^ 14122132169468395523072 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (11 : ZMod 42366396508405186569217) ^ 149704581301785111552 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (11 : ZMod 42366396508405186569217) ^ 1432855748815872 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (11 : ZMod 42366396508405186569217) ^ 25705538300928 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourCX_76545614223615742483337 : Nat.Prime 76545614223615742483337 := by
  apply lucas_primality 76545614223615742483337 (3 : ZMod 76545614223615742483337)
  · rw [← oneHundredFourCXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (47, 1), (73, 1), (4066691, 1), (685754131277, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (47, 1), (73, 1), (4066691, 1), (685754131277, 1)] : List FactorBlock).map factorBlockValue).prod) = 76545614223615742483337 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourCX_2
      · exact prime_oneHundredFourCX_47
      · exact prime_oneHundredFourCX_73
      · exact prime_oneHundredFourCX_4066691
      · exact prime_oneHundredFourCX_685754131277
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 76545614223615742483337) ^ 38272807111807871241668 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (3 : ZMod 76545614223615742483337) ^ 1628630089864164733688 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (3 : ZMod 76545614223615742483337) ^ 1048570057857749897032 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (3 : ZMod 76545614223615742483337) ^ 18822579395291096 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (3 : ZMod 76545614223615742483337) ^ 111622534568 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourCX_91062081470414194548367 : Nat.Prime 91062081470414194548367 := by
  apply lucas_primality 91062081470414194548367 (5 : ZMod 91062081470414194548367)
  · rw [← oneHundredFourCXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (83357, 1), (26010350623398439, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (83357, 1), (26010350623398439, 1)] : List FactorBlock).map factorBlockValue).prod) = 91062081470414194548367 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourCX_2
      · exact prime_oneHundredFourCX_3
      · exact prime_oneHundredFourCX_7
      · exact prime_oneHundredFourCX_83357
      · exact prime_oneHundredFourCX_26010350623398439
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 91062081470414194548367) ^ 45531040735207097274183 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (5 : ZMod 91062081470414194548367) ^ 30354027156804731516122 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (5 : ZMod 91062081470414194548367) ^ 13008868781487742078338 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (5 : ZMod 91062081470414194548367) ^ 1092434726182734438 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (5 : ZMod 91062081470414194548367) ^ 3500994 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourCX_127950428888796596398181 : Nat.Prime 127950428888796596398181 := by
  apply lucas_primality 127950428888796596398181 (2 : ZMod 127950428888796596398181)
  · rw [← oneHundredFourCXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (269791169, 1), (23712864539461, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (269791169, 1), (23712864539461, 1)] : List FactorBlock).map factorBlockValue).prod) = 127950428888796596398181 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourCX_2
      · exact prime_oneHundredFourCX_5
      · exact prime_oneHundredFourCX_269791169
      · exact prime_oneHundredFourCX_23712864539461
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 127950428888796596398181) ^ 63975214444398298199090 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (2 : ZMod 127950428888796596398181) ^ 25590085777759319279636 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (2 : ZMod 127950428888796596398181) ^ 474257290789220 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (2 : ZMod 127950428888796596398181) ^ 5395823380 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourCX_170799163681273442926553 : Nat.Prime 170799163681273442926553 := by
  apply lucas_primality 170799163681273442926553 (3 : ZMod 170799163681273442926553)
  · rw [← oneHundredFourCXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (250361, 1), (85276442657439379, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (250361, 1), (85276442657439379, 1)] : List FactorBlock).map factorBlockValue).prod) = 170799163681273442926553 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFourCX_2
      · exact prime_oneHundredFourCX_250361
      · exact prime_oneHundredFourCX_85276442657439379
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 170799163681273442926553) ^ 85399581840636721463276 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (3 : ZMod 170799163681273442926553) ^ 682211541259515032 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (3 : ZMod 170799163681273442926553) ^ 2002888 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourCX_638230561724016654266947 : Nat.Prime 638230561724016654266947 := by
  apply lucas_primality 638230561724016654266947 (2 : ZMod 638230561724016654266947)
  · rw [← oneHundredFourCXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (609913, 1), (174404809025772707, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (609913, 1), (174404809025772707, 1)] : List FactorBlock).map factorBlockValue).prod) = 638230561724016654266947 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourCX_2
      · exact prime_oneHundredFourCX_3
      · exact prime_oneHundredFourCX_609913
      · exact prime_oneHundredFourCX_174404809025772707
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 638230561724016654266947) ^ 319115280862008327133473 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (2 : ZMod 638230561724016654266947) ^ 212743520574672218088982 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (2 : ZMod 638230561724016654266947) ^ 1046428854154636242 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (2 : ZMod 638230561724016654266947) ^ 3659478 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourCX_1616562660356212627677907 : Nat.Prime 1616562660356212627677907 := by
  apply lucas_primality 1616562660356212627677907 (3 : ZMod 1616562660356212627677907)
  · rw [← oneHundredFourCXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (7, 1), (71171, 1), (921517, 1), (65207015611, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (7, 1), (71171, 1), (921517, 1), (65207015611, 1)] : List FactorBlock).map factorBlockValue).prod) = 1616562660356212627677907 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourCX_2
      · exact prime_oneHundredFourCX_3
      · exact prime_oneHundredFourCX_7
      · exact prime_oneHundredFourCX_71171
      · exact prime_oneHundredFourCX_921517
      · exact prime_oneHundredFourCX_65207015611
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1616562660356212627677907) ^ 808281330178106313838953 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (3 : ZMod 1616562660356212627677907) ^ 538854220118737542559302 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (3 : ZMod 1616562660356212627677907) ^ 230937522908030375382558 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (3 : ZMod 1616562660356212627677907) ^ 22713783147015113286 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (3 : ZMod 1616562660356212627677907) ^ 1754240736043081818 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (3 : ZMod 1616562660356212627677907) ^ 24791238261846 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourCX_3099542613796504385318047 : Nat.Prime 3099542613796504385318047 := by
  apply lucas_primality 3099542613796504385318047 (3 : ZMod 3099542613796504385318047)
  · rw [← oneHundredFourCXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (1553, 1), (47520047431952049571, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (1553, 1), (47520047431952049571, 1)] : List FactorBlock).map factorBlockValue).prod) = 3099542613796504385318047 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourCX_2
      · exact prime_oneHundredFourCX_3
      · exact prime_oneHundredFourCX_7
      · exact prime_oneHundredFourCX_1553
      · exact prime_oneHundredFourCX_47520047431952049571
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 3099542613796504385318047) ^ 1549771306898252192659023 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (3 : ZMod 3099542613796504385318047) ^ 1033180871265501461772682 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (3 : ZMod 3099542613796504385318047) ^ 442791801970929197902578 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (3 : ZMod 3099542613796504385318047) ^ 1995841992141986081982 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (3 : ZMod 3099542613796504385318047) ^ 65226 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourCX_4073810746361855823377563 : Nat.Prime 4073810746361855823377563 := by
  apply lucas_primality 4073810746361855823377563 (2 : ZMod 4073810746361855823377563)
  · rw [← oneHundredFourCXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (97, 1), (151, 1), (233, 1), (198950482390006177, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (97, 1), (151, 1), (233, 1), (198950482390006177, 1)] : List FactorBlock).map factorBlockValue).prod) = 4073810746361855823377563 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourCX_2
      · exact prime_oneHundredFourCX_3
      · exact prime_oneHundredFourCX_97
      · exact prime_oneHundredFourCX_151
      · exact prime_oneHundredFourCX_233
      · exact prime_oneHundredFourCX_198950482390006177
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 4073810746361855823377563) ^ 2036905373180927911688781 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (2 : ZMod 4073810746361855823377563) ^ 1357936915453951941125854 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (2 : ZMod 4073810746361855823377563) ^ 41998048931565523952346 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (2 : ZMod 4073810746361855823377563) ^ 26978879114979177638262 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (2 : ZMod 4073810746361855823377563) ^ 17484166293398522847114 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (2 : ZMod 4073810746361855823377563) ^ 20476506 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourCX_4236639650840518656921701 : Nat.Prime 4236639650840518656921701 := by
  apply lucas_primality 4236639650840518656921701 (2 : ZMod 4236639650840518656921701)
  · rw [← oneHundredFourCXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 2), (42366396508405186569217, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 2), (42366396508405186569217, 1)] : List FactorBlock).map factorBlockValue).prod) = 4236639650840518656921701 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFourCX_2
      · exact prime_oneHundredFourCX_5
      · exact prime_oneHundredFourCX_42366396508405186569217
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 4236639650840518656921701) ^ 2118319825420259328460850 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (2 : ZMod 4236639650840518656921701) ^ 847327930168103731384340 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (2 : ZMod 4236639650840518656921701) ^ 100 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourCX_11218590871048679969085913 : Nat.Prime 11218590871048679969085913 := by
  apply lucas_primality 11218590871048679969085913 (5 : ZMod 11218590871048679969085913)
  · rw [← oneHundredFourCXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (47, 1), (241, 1), (9439, 1), (1997243, 1), (729682649, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (47, 1), (241, 1), (9439, 1), (1997243, 1), (729682649, 1)] : List FactorBlock).map factorBlockValue).prod) = 11218590871048679969085913 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourCX_2
      · exact prime_oneHundredFourCX_3
      · exact prime_oneHundredFourCX_47
      · exact prime_oneHundredFourCX_241
      · exact prime_oneHundredFourCX_9439
      · exact prime_oneHundredFourCX_1997243
      · exact prime_oneHundredFourCX_729682649
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 11218590871048679969085913) ^ 5609295435524339984542956 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (5 : ZMod 11218590871048679969085913) ^ 3739530290349559989695304 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (5 : ZMod 11218590871048679969085913) ^ 238693422788269786576296 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (5 : ZMod 11218590871048679969085913) ^ 46550169589413609830232 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (5 : ZMod 11218590871048679969085913) ^ 1188535954131653773608 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (5 : ZMod 11218590871048679969085913) ^ 5617038523128472584 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (5 : ZMod 11218590871048679969085913) ^ 15374616467067288 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourCX_27568555144998549879188701 : Nat.Prime 27568555144998549879188701 := by
  apply lucas_primality 27568555144998549879188701 (2 : ZMod 27568555144998549879188701)
  · rw [← oneHundredFourCXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (5, 2), (346417, 1), (88424436268679879, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (5, 2), (346417, 1), (88424436268679879, 1)] : List FactorBlock).map factorBlockValue).prod) = 27568555144998549879188701 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourCX_2
      · exact prime_oneHundredFourCX_3
      · exact prime_oneHundredFourCX_5
      · exact prime_oneHundredFourCX_346417
      · exact prime_oneHundredFourCX_88424436268679879
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 27568555144998549879188701) ^ 13784277572499274939594350 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (2 : ZMod 27568555144998549879188701) ^ 9189518381666183293062900 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (2 : ZMod 27568555144998549879188701) ^ 5513711028999709975837740 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (2 : ZMod 27568555144998549879188701) ^ 79581992641811891100 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (2 : ZMod 27568555144998549879188701) ^ 311775300 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourCX_111473940114862676755377703 : Nat.Prime 111473940114862676755377703 := by
  apply lucas_primality 111473940114862676755377703 (5 : ZMod 111473940114862676755377703)
  · rw [← oneHundredFourCXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (23, 1), (1811, 1), (48288841, 1), (9236959368229, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (23, 1), (1811, 1), (48288841, 1), (9236959368229, 1)] : List FactorBlock).map factorBlockValue).prod) = 111473940114862676755377703 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourCX_2
      · exact prime_oneHundredFourCX_3
      · exact prime_oneHundredFourCX_23
      · exact prime_oneHundredFourCX_1811
      · exact prime_oneHundredFourCX_48288841
      · exact prime_oneHundredFourCX_9236959368229
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 111473940114862676755377703) ^ 55736970057431338377688851 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (5 : ZMod 111473940114862676755377703) ^ 37157980038287558918459234 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (5 : ZMod 111473940114862676755377703) ^ 4846693048472290293712074 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (5 : ZMod 111473940114862676755377703) ^ 61553804591310147297282 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (5 : ZMod 111473940114862676755377703) ^ 2308482411389055222 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (5 : ZMod 111473940114862676755377703) ^ 12068250565038 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourCX_215334073461810039336570239 : Nat.Prime 215334073461810039336570239 := by
  apply lucas_primality 215334073461810039336570239 (11 : ZMod 215334073461810039336570239)
  · rw [← oneHundredFourCXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (58670586179, 1), (1835110977115861, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (58670586179, 1), (1835110977115861, 1)] : List FactorBlock).map factorBlockValue).prod) = 215334073461810039336570239 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFourCX_2
      · exact prime_oneHundredFourCX_58670586179
      · exact prime_oneHundredFourCX_1835110977115861
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (11 : ZMod 215334073461810039336570239) ^ 107667036730905019668285119 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (11 : ZMod 215334073461810039336570239) ^ 3670221954231722 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (11 : ZMod 215334073461810039336570239) ^ 117341172358 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourCX_288628535086135052725778419 : Nat.Prime 288628535086135052725778419 := by
  apply lucas_primality 288628535086135052725778419 (2 : ZMod 288628535086135052725778419)
  · rw [← oneHundredFourCXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (6502467331, 1), (821991499516457, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (6502467331, 1), (821991499516457, 1)] : List FactorBlock).map factorBlockValue).prod) = 288628535086135052725778419 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourCX_2
      · exact prime_oneHundredFourCX_3
      · exact prime_oneHundredFourCX_6502467331
      · exact prime_oneHundredFourCX_821991499516457
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 288628535086135052725778419) ^ 144314267543067526362889209 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (2 : ZMod 288628535086135052725778419) ^ 96209511695378350908592806 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (2 : ZMod 288628535086135052725778419) ^ 44387540973888678 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (2 : ZMod 288628535086135052725778419) ^ 351133235874 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourCX_5123156497778897185882566937 : Nat.Prime 5123156497778897185882566937 := by
  apply lucas_primality 5123156497778897185882566937 (17 : ZMod 5123156497778897185882566937)
  · rw [← oneHundredFourCXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (7, 2), (7247, 1), (601135034269270369663, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (7, 2), (7247, 1), (601135034269270369663, 1)] : List FactorBlock).map factorBlockValue).prod) = 5123156497778897185882566937 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourCX_2
      · exact prime_oneHundredFourCX_3
      · exact prime_oneHundredFourCX_7
      · exact prime_oneHundredFourCX_7247
      · exact prime_oneHundredFourCX_601135034269270369663
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (17 : ZMod 5123156497778897185882566937) ^ 2561578248889448592941283468 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (17 : ZMod 5123156497778897185882566937) ^ 1707718832592965728627522312 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (17 : ZMod 5123156497778897185882566937) ^ 731879499682699597983223848 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (17 : ZMod 5123156497778897185882566937) ^ 706934800300661954723688 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (17 : ZMod 5123156497778897185882566937) ^ 8522472 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourCX_6830875330371862914510089249 : Nat.Prime 6830875330371862914510089249 := by
  apply lucas_primality 6830875330371862914510089249 (3 : ZMod 6830875330371862914510089249)
  · rw [← oneHundredFourCXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (7, 2), (7247, 1), (601135034269270369663, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (7, 2), (7247, 1), (601135034269270369663, 1)] : List FactorBlock).map factorBlockValue).prod) = 6830875330371862914510089249 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourCX_2
      · exact prime_oneHundredFourCX_7
      · exact prime_oneHundredFourCX_7247
      · exact prime_oneHundredFourCX_601135034269270369663
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 6830875330371862914510089249) ^ 3415437665185931457255044624 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (3 : ZMod 6830875330371862914510089249) ^ 975839332910266130644298464 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (3 : ZMod 6830875330371862914510089249) ^ 942579733734215939631584 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (3 : ZMod 6830875330371862914510089249) ^ 11363296 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourCX_17565107992384790351597372351 : Nat.Prime 17565107992384790351597372351 := by
  apply lucas_primality 17565107992384790351597372351 (17 : ZMod 17565107992384790351597372351)
  · rw [← oneHundredFourCXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (29, 2), (31, 1), (10071353, 1), (15054001, 1), (88875769, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (29, 2), (31, 1), (10071353, 1), (15054001, 1), (88875769, 1)] : List FactorBlock).map factorBlockValue).prod) = 17565107992384790351597372351 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourCX_2
      · exact prime_oneHundredFourCX_5
      · exact prime_oneHundredFourCX_29
      · exact prime_oneHundredFourCX_31
      · exact prime_oneHundredFourCX_10071353
      · exact prime_oneHundredFourCX_15054001
      · exact prime_oneHundredFourCX_88875769
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (17 : ZMod 17565107992384790351597372351) ^ 8782553996192395175798686175 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (17 : ZMod 17565107992384790351597372351) ^ 3513021598476958070319474470 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (17 : ZMod 17565107992384790351597372351) ^ 605693379047751391434392150 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (17 : ZMod 17565107992384790351597372351) ^ 566616386851122269406366850 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (17 : ZMod 17565107992384790351597372351) ^ 1744066362521975979950 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (17 : ZMod 17565107992384790351597372351) ^ 1166806617880840472350 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (17 : ZMod 17565107992384790351597372351) ^ 197636635834732303150 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourCX_122955755946693532461181606411 : Nat.Prime 122955755946693532461181606411 := by
  apply lucas_primality 122955755946693532461181606411 (14 : ZMod 122955755946693532461181606411)
  · rw [← oneHundredFourCXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (23, 1), (37, 1), (28607, 1), (56118296425536623357, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (23, 1), (37, 1), (28607, 1), (56118296425536623357, 1)] : List FactorBlock).map factorBlockValue).prod) = 122955755946693532461181606411 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourCX_2
      · exact prime_oneHundredFourCX_3
      · exact prime_oneHundredFourCX_5
      · exact prime_oneHundredFourCX_23
      · exact prime_oneHundredFourCX_37
      · exact prime_oneHundredFourCX_28607
      · exact prime_oneHundredFourCX_56118296425536623357
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (14 : ZMod 122955755946693532461181606411) ^ 61477877973346766230590803205 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (14 : ZMod 122955755946693532461181606411) ^ 40985251982231177487060535470 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (14 : ZMod 122955755946693532461181606411) ^ 24591151189338706492236321282 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (14 : ZMod 122955755946693532461181606411) ^ 5345902432464936193964417670 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (14 : ZMod 122955755946693532461181606411) ^ 3323128539099825201653556930 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (14 : ZMod 122955755946693532461181606411) ^ 4298100323231849982912630 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (14 : ZMod 122955755946693532461181606411) ^ 2191010130 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourCX_122955755946693532461181606493 : Nat.Prime 122955755946693532461181606493 := by
  apply lucas_primality 122955755946693532461181606493 (2 : ZMod 122955755946693532461181606493)
  · rw [← oneHundredFourCXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (157, 1), (44240389, 1), (632225841986292193, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (157, 1), (44240389, 1), (632225841986292193, 1)] : List FactorBlock).map factorBlockValue).prod) = 122955755946693532461181606493 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourCX_2
      · exact prime_oneHundredFourCX_7
      · exact prime_oneHundredFourCX_157
      · exact prime_oneHundredFourCX_44240389
      · exact prime_oneHundredFourCX_632225841986292193
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 122955755946693532461181606493) ^ 61477877973346766230590803246 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (2 : ZMod 122955755946693532461181606493) ^ 17565107992384790351597372356 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (2 : ZMod 122955755946693532461181606493) ^ 783157681189130780007526156 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (2 : ZMod 122955755946693532461181606493) ^ 2779264801371740480428 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide
    · change (2 : ZMod 122955755946693532461181606493) ^ 194480750044 ≠ 1
      rw [← oneHundredFourCXFastPow_eq_pow]
      decide

private theorem phi_oneHundredFourCX_122955755946693532461181606400 : Nat.totient 122955755946693532461181606400 = 45398783408065799221592064000 := by
  rw [← show ((([(2, 9), (5, 2), (13, 1), (171401, 1), (714027719, 1), (6037638679, 1)] : List FactorBlock).map factorBlockValue).prod) = 122955755946693532461181606400 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFourCX_2, prime_oneHundredFourCX_5, prime_oneHundredFourCX_13, prime_oneHundredFourCX_171401, prime_oneHundredFourCX_714027719, prime_oneHundredFourCX_6037638679]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFourCX_122955755946693532461181606401 : Nat.totient 122955755946693532461181606401 = 70260408191640839372685818496 := by
  rw [← show ((([(3, 2), (7, 1), (2954863, 1), (660497175612044369329, 1)] : List FactorBlock).map factorBlockValue).prod) = 122955755946693532461181606401 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFourCX_3, prime_oneHundredFourCX_7, prime_oneHundredFourCX_2954863, prime_oneHundredFourCX_660497175612044369329]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFourCX_122955755946693532461181606402 : Nat.totient 122955755946693532461181606402 = 61477869782846539740005803872 := by
  rw [← show ((([(2, 1), (8532299, 1), (62402203, 1), (115465670140633, 1)] : List FactorBlock).map factorBlockValue).prod) = 122955755946693532461181606402 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFourCX_2, prime_oneHundredFourCX_8532299, prime_oneHundredFourCX_62402203, prime_oneHundredFourCX_115465670140633]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFourCX_122955755946693532461181606403 : Nat.totient 122955755946693532461181606403 = 120635830943945538101633660544 := by
  rw [← show ((([(53, 1), (23750833, 1), (97677412978421408647, 1)] : List FactorBlock).map factorBlockValue).prod) = 122955755946693532461181606403 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFourCX_53, prime_oneHundredFourCX_23750833, prime_oneHundredFourCX_97677412978421408647]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFourCX_122955755946693532461181606404 : Nat.totient 122955755946693532461181606404 = 38424107501450669847316529152 := by
  rw [← show ((([(2, 2), (3, 1), (17, 1), (257, 1), (251897, 1), (9310276483619584019, 1)] : List FactorBlock).map factorBlockValue).prod) = 122955755946693532461181606404 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFourCX_2, prime_oneHundredFourCX_3, prime_oneHundredFourCX_17, prime_oneHundredFourCX_257, prime_oneHundredFourCX_251897, prime_oneHundredFourCX_9310276483619584019]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFourCX_122955755946693532461181606405 : Nat.totient 122955755946693532461181606405 = 98363921560700100875173003008 := by
  rw [← show ((([(5, 1), (143977, 1), (170799163681273442926553, 1)] : List FactorBlock).map factorBlockValue).prod) = 122955755946693532461181606405 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFourCX_5, prime_oneHundredFourCX_143977, prime_oneHundredFourCX_170799163681273442926553]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFourCX_122955755946693532461181606406 : Nat.totient 122955755946693532461181606406 = 60310488119752198476507340800 := by
  rw [← show ((([(2, 1), (61, 1), (379, 1), (15425269, 1), (284376793, 1), (606209761, 1)] : List FactorBlock).map factorBlockValue).prod) = 122955755946693532461181606406 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFourCX_2, prime_oneHundredFourCX_61, prime_oneHundredFourCX_379, prime_oneHundredFourCX_15425269, prime_oneHundredFourCX_284376793, prime_oneHundredFourCX_606209761]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFourCX_122955755946693532461181606407 : Nat.totient 122955755946693532461181606407 = 81970503497900934450212703288 := by
  rw [← show ((([(3, 1), (175690703, 1), (233280710261778493123, 1)] : List FactorBlock).map factorBlockValue).prod) = 122955755946693532461181606407 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFourCX_3, prime_oneHundredFourCX_175690703, prime_oneHundredFourCX_233280710261778493123]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFourCX_122955755946693532461181606408 : Nat.totient 122955755946693532461181606408 = 47748807158513766903664035840 := by
  rw [← show ((([(2, 3), (7, 1), (11, 1), (317, 1), (9719, 1), (6998309863, 1), (9257508937, 1)] : List FactorBlock).map factorBlockValue).prod) = 122955755946693532461181606408 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFourCX_2, prime_oneHundredFourCX_7, prime_oneHundredFourCX_11, prime_oneHundredFourCX_317, prime_oneHundredFourCX_9719, prime_oneHundredFourCX_6998309863, prime_oneHundredFourCX_9257508937]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFourCX_122955755946693532461181606409 : Nat.totient 122955755946693532461181606409 = 122844282006578669784426227604 := by
  rw [← show ((([(1103, 1), (111473940114862676755377703, 1)] : List FactorBlock).map factorBlockValue).prod) = 122955755946693532461181606409 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFourCX_1103, prime_oneHundredFourCX_111473940114862676755377703]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFourCX_122955755946693532461181606410 : Nat.totient 122955755946693532461181606410 = 30513922323329503511894757888 := by
  rw [← show ((([(2, 1), (3, 2), (5, 1), (23, 1), (37, 1), (28607, 1), (56118296425536623357, 1)] : List FactorBlock).map factorBlockValue).prod) = 122955755946693532461181606410 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFourCX_2, prime_oneHundredFourCX_3, prime_oneHundredFourCX_5, prime_oneHundredFourCX_23, prime_oneHundredFourCX_37, prime_oneHundredFourCX_28607, prime_oneHundredFourCX_56118296425536623357]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFourCX_122955755946693532461181606411 : Nat.totient 122955755946693532461181606411 = 122955755946693532461181606410 := by
  rw [← show ((([(122955755946693532461181606411, 1)] : List FactorBlock).map factorBlockValue).prod) = 122955755946693532461181606411 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFourCX_122955755946693532461181606411]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFourCX_122955755946693532461181606412 : Nat.totient 122955755946693532461181606412 = 61472865932407640599857561600 := by
  rw [← show ((([(2, 2), (14051, 1), (172313, 1), (237467, 1), (3638827, 1), (14692609, 1)] : List FactorBlock).map factorBlockValue).prod) = 122955755946693532461181606412 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFourCX_2, prime_oneHundredFourCX_14051, prime_oneHundredFourCX_172313, prime_oneHundredFourCX_237467, prime_oneHundredFourCX_3638827, prime_oneHundredFourCX_14692609]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFourCX_122955755946693532461181606413 : Nat.totient 122955755946693532461181606413 = 74599279131199631480971504128 := by
  rw [← show ((([(3, 1), (13, 1), (89, 1), (347, 1), (2755243, 1), (37051420944511243, 1)] : List FactorBlock).map factorBlockValue).prod) = 122955755946693532461181606413 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFourCX_3, prime_oneHundredFourCX_13, prime_oneHundredFourCX_89, prime_oneHundredFourCX_347, prime_oneHundredFourCX_2755243, prime_oneHundredFourCX_37051420944511243]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFourCX_122955755946693532461181606414 : Nat.totient 122955755946693532461181606414 = 61433805802995514534308293472 := by
  rw [← show ((([(2, 1), (1427, 1), (62039, 1), (21200988013, 1), (32754728663, 1)] : List FactorBlock).map factorBlockValue).prod) = 122955755946693532461181606414 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFourCX_2, prime_oneHundredFourCX_1427, prime_oneHundredFourCX_62039, prime_oneHundredFourCX_21200988013, prime_oneHundredFourCX_32754728663]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFourCX_122955755946693532461181606415 : Nat.totient 122955755946693532461181606415 = 79784353359041781469180170240 := by
  rw [← show ((([(5, 1), (7, 2), (19, 1), (881, 1), (29981494017196436639153, 1)] : List FactorBlock).map factorBlockValue).prod) = 122955755946693532461181606415 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFourCX_5, prime_oneHundredFourCX_7, prime_oneHundredFourCX_19, prime_oneHundredFourCX_881, prime_oneHundredFourCX_29981494017196436639153]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFourCX_122955755946693532461181606416 : Nat.totient 122955755946693532461181606416 = 40690393663236518095422341760 := by
  rw [← show ((([(2, 4), (3, 1), (139, 1), (104050223, 1), (177112743868002511, 1)] : List FactorBlock).map factorBlockValue).prod) = 122955755946693532461181606416 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFourCX_2, prime_oneHundredFourCX_3, prime_oneHundredFourCX_139, prime_oneHundredFourCX_104050223, prime_oneHundredFourCX_177112743868002511]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFourCX_122955755946693532461181606417 : Nat.totient 122955755946693532461181606417 = 119956645659531057026879030400 := by
  rw [← show ((([(41, 1), (633317, 1), (4735260346317283039861, 1)] : List FactorBlock).map factorBlockValue).prod) = 122955755946693532461181606417 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFourCX_41, prime_oneHundredFourCX_633317, prime_oneHundredFourCX_4735260346317283039861]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFourCX_122955755946693532461181606418 : Nat.totient 122955755946693532461181606418 = 61439041243098163684734470160 := by
  rw [← show ((([(2, 1), (1583, 1), (146030803, 1), (265946010870138941, 1)] : List FactorBlock).map factorBlockValue).prod) = 122955755946693532461181606418 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFourCX_2, prime_oneHundredFourCX_1583, prime_oneHundredFourCX_146030803, prime_oneHundredFourCX_265946010870138941]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFourCX_122955755946693532461181606419 : Nat.totient 122955755946693532461181606419 = 70571708982929513310981120000 := by
  rw [← show ((([(3, 3), (11, 1), (31, 1), (109, 1), (131, 1), (211, 1), (4432517635612128193, 1)] : List FactorBlock).map factorBlockValue).prod) = 122955755946693532461181606419 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFourCX_3, prime_oneHundredFourCX_11, prime_oneHundredFourCX_31, prime_oneHundredFourCX_109, prime_oneHundredFourCX_131, prime_oneHundredFourCX_211, prime_oneHundredFourCX_4432517635612128193]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFourCX_122955755946693532461181606420 : Nat.totient 122955755946693532461181606420 = 49169369877394563283451188896 := by
  rw [← show ((([(2, 2), (5, 1), (3803, 1), (1616562660356212627677907, 1)] : List FactorBlock).map factorBlockValue).prod) = 122955755946693532461181606420 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFourCX_2, prime_oneHundredFourCX_5, prime_oneHundredFourCX_3803, prime_oneHundredFourCX_1616562660356212627677907]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFourCX_122955755946693532461181606421 : Nat.totient 122955755946693532461181606421 = 111729949880484499046673361920 := by
  rw [← show ((([(17, 1), (29, 1), (41941, 1), (5946523832967403425317, 1)] : List FactorBlock).map factorBlockValue).prod) = 122955755946693532461181606421 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFourCX_17, prime_oneHundredFourCX_29, prime_oneHundredFourCX_41941, prime_oneHundredFourCX_5946523832967403425317]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFourCX_122955755946693532461181606422 : Nat.totient 122955755946693532461181606422 = 35079376308959494479311676000 := by
  rw [← show ((([(2, 1), (3, 1), (7, 1), (691, 1), (4236639650840518656921701, 1)] : List FactorBlock).map factorBlockValue).prod) = 122955755946693532461181606422 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFourCX_2, prime_oneHundredFourCX_3, prime_oneHundredFourCX_7, prime_oneHundredFourCX_691, prime_oneHundredFourCX_4236639650840518656921701]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFourCX_122955755946693532461181606423 : Nat.totient 122955755946693532461181606423 = 121204283150215470313508400000 := by
  rw [← show ((([(71, 1), (6883, 1), (79379, 1), (244781, 1), (3466751, 1), (3735139, 1)] : List FactorBlock).map factorBlockValue).prod) = 122955755946693532461181606423 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFourCX_71, prime_oneHundredFourCX_6883, prime_oneHundredFourCX_79379, prime_oneHundredFourCX_244781, prime_oneHundredFourCX_3466751, prime_oneHundredFourCX_3735139]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFourCX_122955755946693532461181606424 : Nat.totient 122955755946693532461181606424 = 60169454500621025853093993984 := by
  rw [← show ((([(2, 3), (47, 1), (160183, 1), (7631857, 1), (267494201311979, 1)] : List FactorBlock).map factorBlockValue).prod) = 122955755946693532461181606424 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFourCX_2, prime_oneHundredFourCX_47, prime_oneHundredFourCX_160183, prime_oneHundredFourCX_7631857, prime_oneHundredFourCX_267494201311979]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFourCX_122955755946693532461181606425 : Nat.totient 122955755946693532461181606425 = 65424783365958240162465246720 := by
  rw [← show ((([(3, 1), (5, 2), (463, 1), (6553, 1), (102578743, 1), (5267554879547, 1)] : List FactorBlock).map factorBlockValue).prod) = 122955755946693532461181606425 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFourCX_3, prime_oneHundredFourCX_5, prime_oneHundredFourCX_463, prime_oneHundredFourCX_6553, prime_oneHundredFourCX_102578743, prime_oneHundredFourCX_5267554879547]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFourCX_122955755946693532461181606426 : Nat.totient 122955755946693532461181606426 = 56741304949830443959591236480 := by
  rw [← show ((([(2, 1), (13, 1), (7561, 1), (2416168199, 1), (258862483991359, 1)] : List FactorBlock).map factorBlockValue).prod) = 122955755946693532461181606426 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFourCX_2, prime_oneHundredFourCX_13, prime_oneHundredFourCX_7561, prime_oneHundredFourCX_2416168199, prime_oneHundredFourCX_258862483991359]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFourCX_122955755946693532461181606427 : Nat.totient 122955755946693532461181606427 = 122955755935677583370597807640 := by
  rw [← show ((([(11161612591, 1), (11015949079422186197, 1)] : List FactorBlock).map factorBlockValue).prod) = 122955755946693532461181606427 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFourCX_11161612591, prime_oneHundredFourCX_11015949079422186197]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFourCX_122955755946693532461181606428 : Nat.totient 122955755946693532461181606428 = 40982267509990202654336574720 := by
  rw [← show ((([(2, 2), (3, 2), (14107, 1), (517721, 1), (467644591344983909, 1)] : List FactorBlock).map factorBlockValue).prod) = 122955755946693532461181606428 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFourCX_2, prime_oneHundredFourCX_3, prime_oneHundredFourCX_14107, prime_oneHundredFourCX_517721, prime_oneHundredFourCX_467644591344983909]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFourCX_122955755946693532461181606429 : Nat.totient 122955755946693532461181606429 = 105276711378693816367543650240 := by
  rw [← show ((([(7, 1), (941, 1), (54323, 1), (343619225687246264029, 1)] : List FactorBlock).map factorBlockValue).prod) = 122955755946693532461181606429 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFourCX_7, prime_oneHundredFourCX_941, prime_oneHundredFourCX_54323, prime_oneHundredFourCX_343619225687246264029]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFourCX_122955755946693532461181606430 : Nat.totient 122955755946693532461181606430 = 44149320372648747866990476800 := by
  rw [← show ((([(2, 1), (5, 1), (11, 1), (83, 1), (2357, 1), (9967, 1), (12040139, 1), (47612670971, 1)] : List FactorBlock).map factorBlockValue).prod) = 122955755946693532461181606430 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFourCX_2, prime_oneHundredFourCX_5, prime_oneHundredFourCX_11, prime_oneHundredFourCX_83, prime_oneHundredFourCX_2357, prime_oneHundredFourCX_9967, prime_oneHundredFourCX_12040139, prime_oneHundredFourCX_47612670971]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFourCX_122955755946693532461181606431 : Nat.totient 122955755946693532461181606431 = 81970503964288626700963227672 := by
  rw [← show ((([(3, 1), (471834248563, 1), (86863664744673079, 1)] : List FactorBlock).map factorBlockValue).prod) = 122955755946693532461181606431 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFourCX_3, prime_oneHundredFourCX_471834248563, prime_oneHundredFourCX_86863664744673079]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFourCX_122955755946693532461181606432 : Nat.totient 122955755946693532461181606432 = 61477877973344387747660439552 := by
  rw [← show ((([(2, 5), (33312673606897, 1), (115342509540833, 1)] : List FactorBlock).map factorBlockValue).prod) = 122955755946693532461181606432 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFourCX_2, prime_oneHundredFourCX_33312673606897, prime_oneHundredFourCX_115342509540833]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFourCX_122955755946693532461181606433 : Nat.totient 122955755946693532461181606433 = 117609853513935759411528705744 := by
  rw [← show ((([(23, 1), (401634562237, 1), (13310364533096083, 1)] : List FactorBlock).map factorBlockValue).prod) = 122955755946693532461181606433 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFourCX_23, prime_oneHundredFourCX_401634562237, prime_oneHundredFourCX_13310364533096083]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFourCX_122955755946693532461181606434 : Nat.totient 122955755946693532461181606434 = 38778077468447083892059274880 := by
  rw [← show ((([(2, 1), (3, 1), (19, 1), (919, 1), (4969, 1), (236188911554202791671, 1)] : List FactorBlock).map factorBlockValue).prod) = 122955755946693532461181606434 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFourCX_2, prime_oneHundredFourCX_3, prime_oneHundredFourCX_19, prime_oneHundredFourCX_919, prime_oneHundredFourCX_4969, prime_oneHundredFourCX_236188911554202791671]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFourCX_122955755946693532461181606435 : Nat.totient 122955755946693532461181606435 = 98364600137552254647149053440 := by
  rw [← show ((([(5, 1), (23385361, 1), (237863789, 1), (4420856813203, 1)] : List FactorBlock).map factorBlockValue).prod) = 122955755946693532461181606435 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFourCX_5, prime_oneHundredFourCX_23385361, prime_oneHundredFourCX_237863789, prime_oneHundredFourCX_4420856813203]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFourCX_122955755946693532461181606436 : Nat.totient 122955755946693532461181606436 = 52384654940601522564201888000 := by
  rw [← show ((([(2, 2), (7, 1), (191, 1), (1831, 1), (8521, 1), (1473596414167950607, 1)] : List FactorBlock).map factorBlockValue).prod) = 122955755946693532461181606436 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFourCX_2, prime_oneHundredFourCX_7, prime_oneHundredFourCX_191, prime_oneHundredFourCX_1831, prime_oneHundredFourCX_8521, prime_oneHundredFourCX_1473596414167950607]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFourCX_122955755946693532461181606437 : Nat.totient 122955755946693532461181606437 = 81850432323752161756348860000 := by
  rw [← show ((([(3, 2), (683, 1), (1454821, 1), (13749157589070950251, 1)] : List FactorBlock).map factorBlockValue).prod) = 122955755946693532461181606437 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFourCX_3, prime_oneHundredFourCX_683, prime_oneHundredFourCX_1454821, prime_oneHundredFourCX_13749157589070950251]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFourCX_122955755946693532461181606438 : Nat.totient 122955755946693532461181606438 = 57725005314916375104740917248 := by
  rw [← show ((([(2, 1), (17, 1), (769, 1), (1097, 1), (6709, 1), (25356953, 1), (25198931287, 1)] : List FactorBlock).map factorBlockValue).prod) = 122955755946693532461181606438 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFourCX_2, prime_oneHundredFourCX_17, prime_oneHundredFourCX_769, prime_oneHundredFourCX_1097, prime_oneHundredFourCX_6709, prime_oneHundredFourCX_25356953, prime_oneHundredFourCX_25198931287]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFourCX_122955755946693532461181606439 : Nat.totient 122955755946693532461181606439 = 113346460683417253213611900000 := by
  rw [← show ((([(13, 1), (751, 1), (3594403, 1), (3503795954666829551, 1)] : List FactorBlock).map factorBlockValue).prod) = 122955755946693532461181606439 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFourCX_13, prime_oneHundredFourCX_751, prime_oneHundredFourCX_3594403, prime_oneHundredFourCX_3503795954666829551]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFourCX_122955755946693532461181606440 : Nat.totient 122955755946693532461181606440 = 32788201492103529042553692672 := by
  rw [← show ((([(2, 3), (3, 1), (5, 1), (349996873, 1), (2927544154246713619, 1)] : List FactorBlock).map factorBlockValue).prod) = 122955755946693532461181606440 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFourCX_2, prime_oneHundredFourCX_3, prime_oneHundredFourCX_5, prime_oneHundredFourCX_349996873, prime_oneHundredFourCX_2927544154246713619]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFourCX_122955755946693532461181606441 : Nat.totient 122955755946693532461181606441 = 109175239221721759516386171600 := by
  rw [← show ((([(11, 3), (43, 1), (33767, 1), (63622374740986994431, 1)] : List FactorBlock).map factorBlockValue).prod) = 122955755946693532461181606441 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFourCX_11, prime_oneHundredFourCX_43, prime_oneHundredFourCX_33767, prime_oneHundredFourCX_63622374740986994431]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFourCX_122955755946693532461181606442 : Nat.totient 122955755946693532461181606442 = 61337818242992207954852579520 := by
  rw [← show ((([(2, 1), (439, 1), (3227281, 1), (43392789259089243619, 1)] : List FactorBlock).map factorBlockValue).prod) = 122955755946693532461181606442 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFourCX_2, prime_oneHundredFourCX_439, prime_oneHundredFourCX_3227281, prime_oneHundredFourCX_43392789259089243619]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFourCX_122955755946693532461181606443 : Nat.totient 122955755946693532461181606443 = 70223237458173603353765650176 := by
  rw [← show ((([(3, 1), (7, 1), (1889, 1), (3099542613796504385318047, 1)] : List FactorBlock).map factorBlockValue).prod) = 122955755946693532461181606443 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFourCX_3, prime_oneHundredFourCX_7, prime_oneHundredFourCX_1889, prime_oneHundredFourCX_3099542613796504385318047]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFourCX_122955755946693532461181606444 : Nat.totient 122955755946693532461181606444 = 60608584965191211365874444288 := by
  rw [← show ((([(2, 2), (73, 1), (2293, 1), (88423, 1), (59899309, 1), (34671681157, 1)] : List FactorBlock).map factorBlockValue).prod) = 122955755946693532461181606444 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFourCX_2, prime_oneHundredFourCX_73, prime_oneHundredFourCX_2293, prime_oneHundredFourCX_88423, prime_oneHundredFourCX_59899309, prime_oneHundredFourCX_34671681157]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFourCX_122955755946693532461181606445 : Nat.totient 122955755946693532461181606445 = 98364549164114753048695878144 := by
  rw [← show ((([(5, 1), (1775737, 1), (492912293, 1), (28095098988029, 1)] : List FactorBlock).map factorBlockValue).prod) = 122955755946693532461181606445 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFourCX_5, prime_oneHundredFourCX_1775737, prime_oneHundredFourCX_492912293, prime_oneHundredFourCX_28095098988029]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFourCX_122955755946693532461181606446 : Nat.totient 122955755946693532461181606446 = 40985251290184839316778086848 := by
  rw [← show ((([(2, 1), (3, 3), (59223277, 1), (38447018787178690537, 1)] : List FactorBlock).map factorBlockValue).prod) = 122955755946693532461181606446 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFourCX_2, prime_oneHundredFourCX_3, prime_oneHundredFourCX_59223277, prime_oneHundredFourCX_38447018787178690537]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFourCX_122955755946693532461181606447 : Nat.totient 122955755946693532461181606447 = 119629349172660772348522994592 := by
  rw [← show ((([(37, 1), (36493, 1), (91062081470414194548367, 1)] : List FactorBlock).map factorBlockValue).prod) = 122955755946693532461181606447 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFourCX_37, prime_oneHundredFourCX_36493, prime_oneHundredFourCX_91062081470414194548367]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFourCX_122955755946693532461181606448 : Nat.totient 122955755946693532461181606448 = 61277616918457031252478042432 := by
  rw [← show ((([(2, 4), (307, 1), (8302403, 1), (3014995691311940443, 1)] : List FactorBlock).map factorBlockValue).prod) = 122955755946693532461181606448 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFourCX_2, prime_oneHundredFourCX_307, prime_oneHundredFourCX_8302403, prime_oneHundredFourCX_3014995691311940443]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFourCX_122955755946693532461181606449 : Nat.totient 122955755946693532461181606449 = 81968806531405783155079584000 := by
  rw [← show ((([(3, 1), (48313, 1), (105381401, 1), (8050069606855691, 1)] : List FactorBlock).map factorBlockValue).prod) = 122955755946693532461181606449 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFourCX_3, prime_oneHundredFourCX_48313, prime_oneHundredFourCX_105381401, prime_oneHundredFourCX_8050069606855691]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFourCX_122955755946693532461181606450 : Nat.totient 122955755946693532461181606450 = 39389601163395606900940800000 := by
  rw [← show ((([(2, 1), (5, 2), (7, 1), (29, 2), (31, 1), (10071353, 1), (15054001, 1), (88875769, 1)] : List FactorBlock).map factorBlockValue).prod) = 122955755946693532461181606450 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFourCX_2, prime_oneHundredFourCX_5, prime_oneHundredFourCX_7, prime_oneHundredFourCX_29, prime_oneHundredFourCX_31, prime_oneHundredFourCX_10071353, prime_oneHundredFourCX_15054001, prime_oneHundredFourCX_88875769]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFourCX_122955755946693532461181606451 : Nat.totient 122955755946693532461181606451 = 119719614447008986474074928896 := by
  rw [← show ((([(67, 1), (97, 1), (787, 1), (24039619807933217848427, 1)] : List FactorBlock).map factorBlockValue).prod) = 122955755946693532461181606451 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFourCX_67, prime_oneHundredFourCX_97, prime_oneHundredFourCX_787, prime_oneHundredFourCX_24039619807933217848427]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFourCX_122955755946693532461181606452 : Nat.totient 122955755946693532461181606452 = 34318122479790989678203392000 := by
  rw [← show ((([(2, 2), (3, 1), (11, 1), (13, 1), (461, 1), (69997, 1), (2220502305087140441, 1)] : List FactorBlock).map factorBlockValue).prod) = 122955755946693532461181606452 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFourCX_2, prime_oneHundredFourCX_3, prime_oneHundredFourCX_11, prime_oneHundredFourCX_13, prime_oneHundredFourCX_461, prime_oneHundredFourCX_69997, prime_oneHundredFourCX_2220502305087140441]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFourCX_122955755946693532461181606453 : Nat.totient 122955755946693532461181606453 = 116249196537018582581215203840 := by
  rw [← show ((([(19, 1), (1013, 1), (1033, 1), (15373, 1), (402278543675223311, 1)] : List FactorBlock).map factorBlockValue).prod) = 122955755946693532461181606453 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFourCX_19, prime_oneHundredFourCX_1013, prime_oneHundredFourCX_1033, prime_oneHundredFourCX_15373, prime_oneHundredFourCX_402278543675223311]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFourCX_122955755946693532461181606454 : Nat.totient 122955755946693532461181606454 = 60159578122230903384868800000 := by
  rw [← show ((([(2, 1), (59, 1), (251, 1), (3823, 1), (4027, 1), (15901, 1), (57397, 1), (295456519, 1)] : List FactorBlock).map factorBlockValue).prod) = 122955755946693532461181606454 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFourCX_2, prime_oneHundredFourCX_59, prime_oneHundredFourCX_251, prime_oneHundredFourCX_3823, prime_oneHundredFourCX_4027, prime_oneHundredFourCX_15901, prime_oneHundredFourCX_57397, prime_oneHundredFourCX_295456519]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFourCX_122955755946693532461181606455 : Nat.totient 122955755946693532461181606455 = 61718946010380170610711358464 := by
  rw [← show ((([(3, 2), (5, 1), (17, 1), (2846749, 1), (56459659197804545503, 1)] : List FactorBlock).map factorBlockValue).prod) = 122955755946693532461181606455 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFourCX_3, prime_oneHundredFourCX_5, prime_oneHundredFourCX_17, prime_oneHundredFourCX_2846749, prime_oneHundredFourCX_56459659197804545503]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFourCX_122955755946693532461181606456 : Nat.totient 122955755946693532461181606456 = 57694918757531316786648634368 := by
  rw [← show ((([(2, 3), (23, 1), (53, 1), (119929, 1), (105131039647847779157, 1)] : List FactorBlock).map factorBlockValue).prod) = 122955755946693532461181606456 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFourCX_2, prime_oneHundredFourCX_23, prime_oneHundredFourCX_53, prime_oneHundredFourCX_119929, prime_oneHundredFourCX_105131039647847779157]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFourCX_122955755946693532461181606457 : Nat.totient 122955755946693532461181606457 = 105390647954308742109584234100 := by
  rw [← show ((([(7, 1), (17565107992384790351597372351, 1)] : List FactorBlock).map factorBlockValue).prod) = 122955755946693532461181606457 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFourCX_7, prime_oneHundredFourCX_17565107992384790351597372351]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFourCX_122955755946693532461181606458 : Nat.totient 122955755946693532461181606458 = 39985611108325098415271959040 := by
  rw [← show ((([(2, 1), (3, 1), (41, 1), (68744369, 1), (7270706726899630967, 1)] : List FactorBlock).map factorBlockValue).prod) = 122955755946693532461181606458 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFourCX_2, prime_oneHundredFourCX_3, prime_oneHundredFourCX_41, prime_oneHundredFourCX_68744369, prime_oneHundredFourCX_7270706726899630967]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFourCX_122955755946693532461181606459 : Nat.totient 122955755946693532461181606459 = 121393383414775311541352629056 := by
  rw [← show ((([(79, 1), (20333, 1), (76545614223615742483337, 1)] : List FactorBlock).map factorBlockValue).prod) = 122955755946693532461181606459 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFourCX_79, prime_oneHundredFourCX_20333, prime_oneHundredFourCX_76545614223615742483337]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFourCX_122955755946693532461181606460 : Nat.totient 122955755946693532461181606460 = 48961753937517424585439131200 := by
  rw [← show ((([(2, 2), (5, 1), (223, 1), (27568555144998549879188701, 1)] : List FactorBlock).map factorBlockValue).prod) = 122955755946693532461181606460 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFourCX_2, prime_oneHundredFourCX_5, prime_oneHundredFourCX_223, prime_oneHundredFourCX_27568555144998549879188701]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFourCX_122955755946693532461181606461 : Nat.totient 122955755946693532461181606461 = 81690741151652416411506029760 := by
  rw [← show ((([(3, 1), (293, 1), (126757647031, 1), (1103534258950789, 1)] : List FactorBlock).map factorBlockValue).prod) = 122955755946693532461181606461 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFourCX_3, prime_oneHundredFourCX_293, prime_oneHundredFourCX_126757647031, prime_oneHundredFourCX_1103534258950789]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFourCX_122955755946693532461181606462 : Nat.totient 122955755946693532461181606462 = 61477877973335596546227288000 := by
  rw [← show ((([(2, 1), (5506709036351, 1), (11164177654478881, 1)] : List FactorBlock).map factorBlockValue).prod) = 122955755946693532461181606462 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFourCX_2, prime_oneHundredFourCX_5506709036351, prime_oneHundredFourCX_11164177654478881]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFourCX_122955755946693532461181606463 : Nat.totient 122955755946693532461181606463 = 111749972321493378990581667840 := by
  rw [← show ((([(11, 1), (6113, 1), (11519, 1), (800821243, 1), (198221802073, 1)] : List FactorBlock).map factorBlockValue).prod) = 122955755946693532461181606463 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFourCX_11, prime_oneHundredFourCX_6113, prime_oneHundredFourCX_11519, prime_oneHundredFourCX_800821243, prime_oneHundredFourCX_198221802073]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFourCX_122955755946693532461181606464 : Nat.totient 122955755946693532461181606464 = 35125368431853233306875350528 := by
  rw [← show ((([(2, 6), (3, 2), (7, 2), (7247, 1), (601135034269270369663, 1)] : List FactorBlock).map factorBlockValue).prod) = 122955755946693532461181606464 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFourCX_2, prime_oneHundredFourCX_3, prime_oneHundredFourCX_7, prime_oneHundredFourCX_7247, prime_oneHundredFourCX_601135034269270369663]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFourCX_122955755946693532461181606465 : Nat.totient 122955755946693532461181606465 = 90388695189547354175757434880 := by
  rw [← show ((([(5, 1), (13, 1), (271, 1), (1217, 1), (4440187, 1), (1291737826932829, 1)] : List FactorBlock).map factorBlockValue).prod) = 122955755946693532461181606465 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFourCX_5, prime_oneHundredFourCX_13, prime_oneHundredFourCX_271, prime_oneHundredFourCX_1217, prime_oneHundredFourCX_4440187, prime_oneHundredFourCX_1291737826932829]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFourCX_122955755946693532461181606466 : Nat.totient 122955755946693532461181606466 = 61473804162600404374767410580 := by
  rw [← show ((([(2, 1), (15091, 1), (4073810746361855823377563, 1)] : List FactorBlock).map factorBlockValue).prod) = 122955755946693532461181606466 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFourCX_2, prime_oneHundredFourCX_15091, prime_oneHundredFourCX_4073810746361855823377563]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFourCX_122955755946693532461181606467 : Nat.totient 122955755946693532461181606467 = 79446074715413256852235100160 := by
  rw [← show ((([(3, 1), (61, 1), (107, 1), (197, 1), (6277, 1), (8807, 1), (576590716499729, 1)] : List FactorBlock).map factorBlockValue).prod) = 122955755946693532461181606467 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFourCX_3, prime_oneHundredFourCX_61, prime_oneHundredFourCX_107, prime_oneHundredFourCX_197, prime_oneHundredFourCX_6277, prime_oneHundredFourCX_8807, prime_oneHundredFourCX_576590716499729]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFourCX_122955755946693532461181606468 : Nat.totient 122955755946693532461181606468 = 61476394114590305280654494400 := by
  rw [← show ((([(2, 2), (41627, 1), (8802841, 1), (83886273557254331, 1)] : List FactorBlock).map factorBlockValue).prod) = 122955755946693532461181606468 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFourCX_2, prime_oneHundredFourCX_41627, prime_oneHundredFourCX_8802841, prime_oneHundredFourCX_83886273557254331]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFourCX_122955755946693532461181606469 : Nat.totient 122955755946693532461181606469 = 122740421873231722421845035660 := by
  rw [← show ((([(571, 1), (215334073461810039336570239, 1)] : List FactorBlock).map factorBlockValue).prod) = 122955755946693532461181606469 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFourCX_571, prime_oneHundredFourCX_215334073461810039336570239]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFourCX_122955755946693532461181606470 : Nat.totient 122955755946693532461181606470 = 32788187070699744822310704000 := by
  rw [← show ((([(2, 1), (3, 1), (5, 1), (2289239, 1), (170478391, 1), (10501882035901, 1)] : List FactorBlock).map factorBlockValue).prod) = 122955755946693532461181606470 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFourCX_2, prime_oneHundredFourCX_3, prime_oneHundredFourCX_5, prime_oneHundredFourCX_2289239, prime_oneHundredFourCX_170478391, prime_oneHundredFourCX_10501882035901]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFourCX_122955755946693532461181606471 : Nat.totient 122955755946693532461181606471 = 103148293739533103645209210464 := by
  rw [← show ((([(7, 1), (47, 1), (34592326123, 1), (10803717004655213, 1)] : List FactorBlock).map factorBlockValue).prod) = 122955755946693532461181606471 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFourCX_7, prime_oneHundredFourCX_47, prime_oneHundredFourCX_34592326123, prime_oneHundredFourCX_10803717004655213]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFourCX_122955755946693532461181606472 : Nat.totient 122955755946693532461181606472 = 54448654905649770700347740160 := by
  rw [← show ((([(2, 3), (17, 1), (19, 1), (163, 1), (1759, 1), (204859, 1), (810117218002061, 1)] : List FactorBlock).map factorBlockValue).prod) = 122955755946693532461181606472 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFourCX_2, prime_oneHundredFourCX_17, prime_oneHundredFourCX_19, prime_oneHundredFourCX_163, prime_oneHundredFourCX_1759, prime_oneHundredFourCX_204859, prime_oneHundredFourCX_810117218002061]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFourCX_122955755946693532461181606473 : Nat.totient 122955755946693532461181606473 = 81831833129573720993611284480 := by
  rw [← show ((([(3, 6), (757, 1), (2711, 1), (460987, 1), (8339297, 1), (21378529, 1)] : List FactorBlock).map factorBlockValue).prod) = 122955755946693532461181606473 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFourCX_3, prime_oneHundredFourCX_757, prime_oneHundredFourCX_2711, prime_oneHundredFourCX_460987, prime_oneHundredFourCX_8339297, prime_oneHundredFourCX_21378529]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFourCX_122955755946693532461181606474 : Nat.totient 122955755946693532461181606474 = 55886319948517408133719782000 := by
  rw [← show ((([(2, 1), (11, 1), (21011, 1), (1377202471, 1), (193144198366307, 1)] : List FactorBlock).map factorBlockValue).prod) = 122955755946693532461181606474 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFourCX_2, prime_oneHundredFourCX_11, prime_oneHundredFourCX_21011, prime_oneHundredFourCX_1377202471, prime_oneHundredFourCX_193144198366307]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFourCX_122955755946693532461181606475 : Nat.totient 122955755946693532461181606475 = 98364604756022800324853566080 := by
  rw [← show ((([(5, 2), (73845961043, 1), (66601208358624913, 1)] : List FactorBlock).map factorBlockValue).prod) = 122955755946693532461181606475 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFourCX_5, prime_oneHundredFourCX_73845961043, prime_oneHundredFourCX_66601208358624913]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFourCX_122955755946693532461181606476 : Nat.totient 122955755946693532461181606476 = 40985238824724419886037508560 := by
  rw [← show ((([(2, 2), (3, 1), (3114971, 1), (3289376689400252641763, 1)] : List FactorBlock).map factorBlockValue).prod) = 122955755946693532461181606476 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFourCX_2, prime_oneHundredFourCX_3, prime_oneHundredFourCX_3114971, prime_oneHundredFourCX_3289376689400252641763]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFourCX_122955755946693532461181606477 : Nat.totient 122955755946693532461181606477 = 122687844393548830913114188800 := by
  rw [← show ((([(593, 1), (2027, 1), (21546677, 1), (45247621, 1), (104921471, 1)] : List FactorBlock).map factorBlockValue).prod) = 122955755946693532461181606477 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFourCX_593, prime_oneHundredFourCX_2027, prime_oneHundredFourCX_21546677, prime_oneHundredFourCX_45247621, prime_oneHundredFourCX_104921471]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFourCX_122955755946693532461181606478 : Nat.totient 122955755946693532461181606478 = 47633584833378981677140992000 := by
  rw [← show ((([(2, 1), (7, 1), (13, 2), (101, 1), (103, 1), (1163, 1), (3221, 1), (20357, 1), (53279, 1), (1229519, 1)] : List FactorBlock).map factorBlockValue).prod) = 122955755946693532461181606478 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFourCX_2, prime_oneHundredFourCX_7, prime_oneHundredFourCX_13, prime_oneHundredFourCX_101, prime_oneHundredFourCX_103, prime_oneHundredFourCX_1163, prime_oneHundredFourCX_3221, prime_oneHundredFourCX_20357, prime_oneHundredFourCX_53279, prime_oneHundredFourCX_1229519]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFourCX_122955755946693532461181606479 : Nat.totient 122955755946693532461181606479 = 75323465989250846667521582592 := by
  rw [← show ((([(3, 1), (23, 1), (29, 1), (229, 1), (1543, 1), (173900314410901159157, 1)] : List FactorBlock).map factorBlockValue).prod) = 122955755946693532461181606479 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFourCX_3, prime_oneHundredFourCX_23, prime_oneHundredFourCX_29, prime_oneHundredFourCX_229, prime_oneHundredFourCX_1543, prime_oneHundredFourCX_173900314410901159157]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFourCX_122955755946693532461181606480 : Nat.totient 122955755946693532461181606480 = 48823307470803855225461889024 := by
  rw [← show ((([(2, 4), (5, 1), (137, 1), (11218590871048679969085913, 1)] : List FactorBlock).map factorBlockValue).prod) = 122955755946693532461181606480 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFourCX_2, prime_oneHundredFourCX_5, prime_oneHundredFourCX_137, prime_oneHundredFourCX_11218590871048679969085913]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFourCX_122955755946693532461181606481 : Nat.totient 122955755946693532461181606481 = 118985629709597868400945703040 := by
  rw [← show ((([(31, 1), (31219, 1), (1382503337, 1), (91897139755117, 1)] : List FactorBlock).map factorBlockValue).prod) = 122955755946693532461181606481 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFourCX_31, prime_oneHundredFourCX_31219, prime_oneHundredFourCX_1382503337, prime_oneHundredFourCX_91897139755117]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFourCX_122955755946693532461181606482 : Nat.totient 122955755946693532461181606482 = 40985251982231177487060535488 := by
  rw [← show ((([(2, 1), (3, 2), (6830875330371862914510089249, 1)] : List FactorBlock).map factorBlockValue).prod) = 122955755946693532461181606482 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFourCX_2, prime_oneHundredFourCX_3, prime_oneHundredFourCX_6830875330371862914510089249]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFourCX_122955755946693532461181606483 : Nat.totient 122955755946693532461181606483 = 122952936430297453183816615488 := by
  rw [← show ((([(43609, 1), (10030579093, 1), (281090863417759, 1)] : List FactorBlock).map factorBlockValue).prod) = 122955755946693532461181606483 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFourCX_43609, prime_oneHundredFourCX_10030579093, prime_oneHundredFourCX_281090863417759]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFourCX_122955755946693532461181606484 : Nat.totient 122955755946693532461181606484 = 58038314543958136126214448000 := by
  rw [← show ((([(2, 2), (37, 1), (43, 1), (151, 1), (127950428888796596398181, 1)] : List FactorBlock).map factorBlockValue).prod) = 122955755946693532461181606484 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFourCX_2, prime_oneHundredFourCX_37, prime_oneHundredFourCX_43, prime_oneHundredFourCX_151, prime_oneHundredFourCX_127950428888796596398181]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFourCX_122955755946693532461181606485 : Nat.totient 122955755946693532461181606485 = 51098234635277702584025932800 := by
  rw [← show ((([(3, 1), (5, 1), (7, 1), (11, 1), (195893, 1), (103533119, 1), (5248904427061, 1)] : List FactorBlock).map factorBlockValue).prod) = 122955755946693532461181606485 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFourCX_3, prime_oneHundredFourCX_5, prime_oneHundredFourCX_7, prime_oneHundredFourCX_11, prime_oneHundredFourCX_195893, prime_oneHundredFourCX_103533119, prime_oneHundredFourCX_5248904427061]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFourCX_122955755946693532461181606486 : Nat.totient 122955755946693532461181606486 = 61471677390767426795469264544 := by
  rw [← show ((([(2, 1), (9923, 1), (12078173, 1), (512949524250042317, 1)] : List FactorBlock).map factorBlockValue).prod) = 122955755946693532461181606486 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFourCX_2, prime_oneHundredFourCX_9923, prime_oneHundredFourCX_12078173, prime_oneHundredFourCX_512949524250042317]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFourCX_122955755946693532461181606487 : Nat.totient 122955755946693532461181606487 = 122941077718289094631990915200 := by
  rw [← show ((([(8377, 1), (273656311, 1), (53635814563226921, 1)] : List FactorBlock).map factorBlockValue).prod) = 122955755946693532461181606487 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFourCX_8377, prime_oneHundredFourCX_273656311, prime_oneHundredFourCX_53635814563226921]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFourCX_122955755946693532461181606488 : Nat.totient 122955755946693532461181606488 = 40985251982231177487060535488 := by
  rw [← show ((([(2, 3), (3, 1), (5123156497778897185882566937, 1)] : List FactorBlock).map factorBlockValue).prod) = 122955755946693532461181606488 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFourCX_2, prime_oneHundredFourCX_3, prime_oneHundredFourCX_5123156497778897185882566937]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFourCX_122955755946693532461181606489 : Nat.totient 122955755946693532461181606489 = 115673780294162555099820337152 := by
  rw [← show ((([(17, 1), (4057, 1), (5573, 1), (319893850963802161597, 1)] : List FactorBlock).map factorBlockValue).prod) = 122955755946693532461181606489 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFourCX_17, prime_oneHundredFourCX_4057, prime_oneHundredFourCX_5573, prime_oneHundredFourCX_319893850963802161597]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFourCX_122955755946693532461181606490 : Nat.totient 122955755946693532461181606490 = 49181393038169970396175628160 := by
  rw [← show ((([(2, 1), (5, 1), (54091, 1), (550210777, 1), (413137636917107, 1)] : List FactorBlock).map factorBlockValue).prod) = 122955755946693532461181606490 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFourCX_2, prime_oneHundredFourCX_5, prime_oneHundredFourCX_54091, prime_oneHundredFourCX_550210777, prime_oneHundredFourCX_413137636917107]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFourCX_122955755946693532461181606491 : Nat.totient 122955755946693532461181606491 = 71268013282159011519016381440 := by
  rw [← show ((([(3, 2), (13, 1), (19, 1), (173, 1), (207341, 1), (1541977758959001869, 1)] : List FactorBlock).map factorBlockValue).prod) = 122955755946693532461181606491 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFourCX_3, prime_oneHundredFourCX_13, prime_oneHundredFourCX_19, prime_oneHundredFourCX_173, prime_oneHundredFourCX_207341, prime_oneHundredFourCX_1541977758959001869]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFourCX_122955755946693532461181606492 : Nat.totient 122955755946693532461181606492 = 52359683787403681582203328512 := by
  rw [← show ((([(2, 2), (7, 1), (157, 1), (44240389, 1), (632225841986292193, 1)] : List FactorBlock).map factorBlockValue).prod) = 122955755946693532461181606492 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFourCX_2, prime_oneHundredFourCX_7, prime_oneHundredFourCX_157, prime_oneHundredFourCX_44240389, prime_oneHundredFourCX_632225841986292193]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFourCX_122955755946693532461181606493 : Nat.totient 122955755946693532461181606493 = 122955755946693532461181606492 := by
  rw [← show ((([(122955755946693532461181606493, 1)] : List FactorBlock).map factorBlockValue).prod) = 122955755946693532461181606493 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFourCX_122955755946693532461181606493]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFourCX_122955755946693532461181606494 : Nat.totient 122955755946693532461181606494 = 40407994912058907381608978520 := by
  rw [← show ((([(2, 1), (3, 1), (71, 1), (288628535086135052725778419, 1)] : List FactorBlock).map factorBlockValue).prod) = 122955755946693532461181606494 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFourCX_2, prime_oneHundredFourCX_3, prime_oneHundredFourCX_71, prime_oneHundredFourCX_288628535086135052725778419]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFourCX_122955755946693532461181606495 : Nat.totient 122955755946693532461181606495 = 97158604761039716968287492096 := by
  rw [← show ((([(5, 1), (149, 1), (179, 1), (17746879697, 1), (51953828355277, 1)] : List FactorBlock).map factorBlockValue).prod) = 122955755946693532461181606495 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFourCX_5, prime_oneHundredFourCX_149, prime_oneHundredFourCX_179, prime_oneHundredFourCX_17746879697, prime_oneHundredFourCX_51953828355277]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFourCX_122955755946693532461181606496 : Nat.totient 122955755946693532461181606496 = 55622283523020442425550786560 := by
  rw [← show ((([(2, 5), (11, 1), (349, 1), (523, 1), (5509144847, 1), (347372067817, 1)] : List FactorBlock).map factorBlockValue).prod) = 122955755946693532461181606496 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFourCX_2, prime_oneHundredFourCX_11, prime_oneHundredFourCX_349, prime_oneHundredFourCX_523, prime_oneHundredFourCX_5509144847, prime_oneHundredFourCX_347372067817]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFourCX_122955755946693532461181606497 : Nat.totient 122955755946693532461181606497 = 81969227503338906940812408672 := by
  rw [← show ((([(3, 1), (64217, 1), (638230561724016654266947, 1)] : List FactorBlock).map factorBlockValue).prod) = 122955755946693532461181606497 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFourCX_3, prime_oneHundredFourCX_64217, prime_oneHundredFourCX_638230561724016654266947]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFourCX_122955755946693532461181606498 : Nat.totient 122955755946693532461181606498 = 61404947961442494456227980800 := by
  rw [← show ((([(2, 1), (1259, 1), (2549, 1), (3496915489, 1), (5478203566151, 1)] : List FactorBlock).map factorBlockValue).prod) = 122955755946693532461181606498 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFourCX_2, prime_oneHundredFourCX_1259, prime_oneHundredFourCX_2549, prime_oneHundredFourCX_3496915489, prime_oneHundredFourCX_5478203566151]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFourCX_122955755946693532461181606499 : Nat.totient 122955755946693532461181606499 = 102820143763036626046888680000 := by
  rw [← show ((([(7, 1), (41, 1), (176475751, 1), (2427626830764676027, 1)] : List FactorBlock).map factorBlockValue).prod) = 122955755946693532461181606499 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFourCX_7, prime_oneHundredFourCX_41, prime_oneHundredFourCX_176475751, prime_oneHundredFourCX_2427626830764676027]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFourCX_122955755946693532461181606500 : Nat.totient 122955755946693532461181606500 = 32788141914565034866328544000 := by
  rw [← show ((([(2, 2), (3, 3), (5, 3), (549481, 1), (16575338863089261599, 1)] : List FactorBlock).map factorBlockValue).prod) = 122955755946693532461181606500 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFourCX_2, prime_oneHundredFourCX_3, prime_oneHundredFourCX_5, prime_oneHundredFourCX_549481, prime_oneHundredFourCX_16575338863089261599]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFourCX_122955755946693532461181606501 : Nat.totient 122955755946693532461181606501 = 122947598116660719172445402112 := by
  rw [← show ((([(15073, 1), (256811773, 1), (31763930413152169, 1)] : List FactorBlock).map factorBlockValue).prod) = 122955755946693532461181606501 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFourCX_15073, prime_oneHundredFourCX_256811773, prime_oneHundredFourCX_31763930413152169]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

theorem freeKill_64OneHundredFourCX : certifiedKill 1 122955755946693532461181606399 101 := by
  norm_num [certifiedKill, windowDiscrepancy, Finset.sum_range_succ,
    phi_oneHundredFourCX_122955755946693532461181606400, phi_oneHundredFourCX_122955755946693532461181606401, phi_oneHundredFourCX_122955755946693532461181606402,
    phi_oneHundredFourCX_122955755946693532461181606403, phi_oneHundredFourCX_122955755946693532461181606404, phi_oneHundredFourCX_122955755946693532461181606405,
    phi_oneHundredFourCX_122955755946693532461181606406, phi_oneHundredFourCX_122955755946693532461181606407, phi_oneHundredFourCX_122955755946693532461181606408,
    phi_oneHundredFourCX_122955755946693532461181606409, phi_oneHundredFourCX_122955755946693532461181606410, phi_oneHundredFourCX_122955755946693532461181606411,
    phi_oneHundredFourCX_122955755946693532461181606412, phi_oneHundredFourCX_122955755946693532461181606413, phi_oneHundredFourCX_122955755946693532461181606414,
    phi_oneHundredFourCX_122955755946693532461181606415, phi_oneHundredFourCX_122955755946693532461181606416, phi_oneHundredFourCX_122955755946693532461181606417,
    phi_oneHundredFourCX_122955755946693532461181606418, phi_oneHundredFourCX_122955755946693532461181606419, phi_oneHundredFourCX_122955755946693532461181606420,
    phi_oneHundredFourCX_122955755946693532461181606421, phi_oneHundredFourCX_122955755946693532461181606422, phi_oneHundredFourCX_122955755946693532461181606423,
    phi_oneHundredFourCX_122955755946693532461181606424, phi_oneHundredFourCX_122955755946693532461181606425, phi_oneHundredFourCX_122955755946693532461181606426,
    phi_oneHundredFourCX_122955755946693532461181606427, phi_oneHundredFourCX_122955755946693532461181606428, phi_oneHundredFourCX_122955755946693532461181606429,
    phi_oneHundredFourCX_122955755946693532461181606430, phi_oneHundredFourCX_122955755946693532461181606431, phi_oneHundredFourCX_122955755946693532461181606432,
    phi_oneHundredFourCX_122955755946693532461181606433, phi_oneHundredFourCX_122955755946693532461181606434, phi_oneHundredFourCX_122955755946693532461181606435,
    phi_oneHundredFourCX_122955755946693532461181606436, phi_oneHundredFourCX_122955755946693532461181606437, phi_oneHundredFourCX_122955755946693532461181606438,
    phi_oneHundredFourCX_122955755946693532461181606439, phi_oneHundredFourCX_122955755946693532461181606440, phi_oneHundredFourCX_122955755946693532461181606441,
    phi_oneHundredFourCX_122955755946693532461181606442, phi_oneHundredFourCX_122955755946693532461181606443, phi_oneHundredFourCX_122955755946693532461181606444,
    phi_oneHundredFourCX_122955755946693532461181606445, phi_oneHundredFourCX_122955755946693532461181606446, phi_oneHundredFourCX_122955755946693532461181606447,
    phi_oneHundredFourCX_122955755946693532461181606448, phi_oneHundredFourCX_122955755946693532461181606449, phi_oneHundredFourCX_122955755946693532461181606450,
    phi_oneHundredFourCX_122955755946693532461181606451, phi_oneHundredFourCX_122955755946693532461181606452, phi_oneHundredFourCX_122955755946693532461181606453,
    phi_oneHundredFourCX_122955755946693532461181606454, phi_oneHundredFourCX_122955755946693532461181606455, phi_oneHundredFourCX_122955755946693532461181606456,
    phi_oneHundredFourCX_122955755946693532461181606457, phi_oneHundredFourCX_122955755946693532461181606458, phi_oneHundredFourCX_122955755946693532461181606459,
    phi_oneHundredFourCX_122955755946693532461181606460, phi_oneHundredFourCX_122955755946693532461181606461, phi_oneHundredFourCX_122955755946693532461181606462,
    phi_oneHundredFourCX_122955755946693532461181606463, phi_oneHundredFourCX_122955755946693532461181606464, phi_oneHundredFourCX_122955755946693532461181606465,
    phi_oneHundredFourCX_122955755946693532461181606466, phi_oneHundredFourCX_122955755946693532461181606467, phi_oneHundredFourCX_122955755946693532461181606468,
    phi_oneHundredFourCX_122955755946693532461181606469, phi_oneHundredFourCX_122955755946693532461181606470, phi_oneHundredFourCX_122955755946693532461181606471,
    phi_oneHundredFourCX_122955755946693532461181606472, phi_oneHundredFourCX_122955755946693532461181606473, phi_oneHundredFourCX_122955755946693532461181606474,
    phi_oneHundredFourCX_122955755946693532461181606475, phi_oneHundredFourCX_122955755946693532461181606476, phi_oneHundredFourCX_122955755946693532461181606477,
    phi_oneHundredFourCX_122955755946693532461181606478, phi_oneHundredFourCX_122955755946693532461181606479, phi_oneHundredFourCX_122955755946693532461181606480,
    phi_oneHundredFourCX_122955755946693532461181606481, phi_oneHundredFourCX_122955755946693532461181606482, phi_oneHundredFourCX_122955755946693532461181606483,
    phi_oneHundredFourCX_122955755946693532461181606484, phi_oneHundredFourCX_122955755946693532461181606485, phi_oneHundredFourCX_122955755946693532461181606486,
    phi_oneHundredFourCX_122955755946693532461181606487, phi_oneHundredFourCX_122955755946693532461181606488, phi_oneHundredFourCX_122955755946693532461181606489,
    phi_oneHundredFourCX_122955755946693532461181606490, phi_oneHundredFourCX_122955755946693532461181606491, phi_oneHundredFourCX_122955755946693532461181606492,
    phi_oneHundredFourCX_122955755946693532461181606493, phi_oneHundredFourCX_122955755946693532461181606494, phi_oneHundredFourCX_122955755946693532461181606495,
    phi_oneHundredFourCX_122955755946693532461181606496, phi_oneHundredFourCX_122955755946693532461181606497, phi_oneHundredFourCX_122955755946693532461181606498,
    phi_oneHundredFourCX_122955755946693532461181606499, phi_oneHundredFourCX_122955755946693532461181606500, phi_oneHundredFourCX_122955755946693532461181606501]

end TotientTailPeriodKiller
end Erdos249257
