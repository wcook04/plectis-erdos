import Erdos249257.DiagonalPincerCertificatesT64

/- Kernel-checked off-diagonal certificate at a freely chosen position. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

private def oneHundredFiftyERFastPow {M : Type*} [Monoid M] (a : M) (n : ℕ) : M :=
  Nat.binaryRec 1 (fun b _ r => if b then r * r * a else r * r) n

private theorem oneHundredFiftyERFastPow_eq_pow {M : Type*} [Monoid M] (a : M) (n : ℕ) : oneHundredFiftyERFastPow a n = a ^ n := by
  induction n using Nat.binaryRec with
  | zero => simp [oneHundredFiftyERFastPow, Nat.binaryRec_zero]
  | bit b n ih =>
      rw [oneHundredFiftyERFastPow, Nat.binaryRec_eq b n (by left; simp)]
      change (if b then oneHundredFiftyERFastPow a n * oneHundredFiftyERFastPow a n * a else oneHundredFiftyERFastPow a n * oneHundredFiftyERFastPow a n) = _
      rw [ih]
      cases b <;> simp [Nat.bit, two_mul, pow_add]

private theorem prime_oneHundredFiftyER_2 : Nat.Prime 2 := by
  norm_num

private theorem prime_oneHundredFiftyER_3 : Nat.Prime 3 := by
  norm_num

private theorem prime_oneHundredFiftyER_5 : Nat.Prime 5 := by
  norm_num

private theorem prime_oneHundredFiftyER_7 : Nat.Prime 7 := by
  norm_num

private theorem prime_oneHundredFiftyER_11 : Nat.Prime 11 := by
  norm_num

private theorem prime_oneHundredFiftyER_13 : Nat.Prime 13 := by
  norm_num

private theorem prime_oneHundredFiftyER_17 : Nat.Prime 17 := by
  norm_num

private theorem prime_oneHundredFiftyER_19 : Nat.Prime 19 := by
  norm_num

private theorem prime_oneHundredFiftyER_23 : Nat.Prime 23 := by
  norm_num

private theorem prime_oneHundredFiftyER_29 : Nat.Prime 29 := by
  norm_num

private theorem prime_oneHundredFiftyER_31 : Nat.Prime 31 := by
  norm_num

private theorem prime_oneHundredFiftyER_37 : Nat.Prime 37 := by
  norm_num

private theorem prime_oneHundredFiftyER_41 : Nat.Prime 41 := by
  norm_num

private theorem prime_oneHundredFiftyER_43 : Nat.Prime 43 := by
  norm_num

private theorem prime_oneHundredFiftyER_47 : Nat.Prime 47 := by
  norm_num

private theorem prime_oneHundredFiftyER_53 : Nat.Prime 53 := by
  norm_num

private theorem prime_oneHundredFiftyER_59 : Nat.Prime 59 := by
  norm_num

private theorem prime_oneHundredFiftyER_61 : Nat.Prime 61 := by
  norm_num

private theorem prime_oneHundredFiftyER_67 : Nat.Prime 67 := by
  norm_num

private theorem prime_oneHundredFiftyER_71 : Nat.Prime 71 := by
  norm_num

private theorem prime_oneHundredFiftyER_73 : Nat.Prime 73 := by
  norm_num

private theorem prime_oneHundredFiftyER_79 : Nat.Prime 79 := by
  norm_num

private theorem prime_oneHundredFiftyER_83 : Nat.Prime 83 := by
  norm_num

private theorem prime_oneHundredFiftyER_89 : Nat.Prime 89 := by
  norm_num

private theorem prime_oneHundredFiftyER_97 : Nat.Prime 97 := by
  norm_num

private theorem prime_oneHundredFiftyER_101 : Nat.Prime 101 := by
  norm_num

private theorem prime_oneHundredFiftyER_103 : Nat.Prime 103 := by
  norm_num

private theorem prime_oneHundredFiftyER_107 : Nat.Prime 107 := by
  norm_num

private theorem prime_oneHundredFiftyER_109 : Nat.Prime 109 := by
  norm_num

private theorem prime_oneHundredFiftyER_113 : Nat.Prime 113 := by
  norm_num

private theorem prime_oneHundredFiftyER_127 : Nat.Prime 127 := by
  norm_num

private theorem prime_oneHundredFiftyER_131 : Nat.Prime 131 := by
  norm_num

private theorem prime_oneHundredFiftyER_137 : Nat.Prime 137 := by
  norm_num

private theorem prime_oneHundredFiftyER_139 : Nat.Prime 139 := by
  norm_num

private theorem prime_oneHundredFiftyER_149 : Nat.Prime 149 := by
  norm_num

private theorem prime_oneHundredFiftyER_151 : Nat.Prime 151 := by
  norm_num

private theorem prime_oneHundredFiftyER_157 : Nat.Prime 157 := by
  norm_num

private theorem prime_oneHundredFiftyER_163 : Nat.Prime 163 := by
  norm_num

private theorem prime_oneHundredFiftyER_167 : Nat.Prime 167 := by
  norm_num

private theorem prime_oneHundredFiftyER_173 : Nat.Prime 173 := by
  norm_num

private theorem prime_oneHundredFiftyER_179 : Nat.Prime 179 := by
  norm_num

private theorem prime_oneHundredFiftyER_181 : Nat.Prime 181 := by
  norm_num

private theorem prime_oneHundredFiftyER_191 : Nat.Prime 191 := by
  norm_num

private theorem prime_oneHundredFiftyER_193 : Nat.Prime 193 := by
  norm_num

private theorem prime_oneHundredFiftyER_197 : Nat.Prime 197 := by
  norm_num

private theorem prime_oneHundredFiftyER_199 : Nat.Prime 199 := by
  norm_num

private theorem prime_oneHundredFiftyER_227 : Nat.Prime 227 := by
  norm_num

private theorem prime_oneHundredFiftyER_229 : Nat.Prime 229 := by
  norm_num

private theorem prime_oneHundredFiftyER_233 : Nat.Prime 233 := by
  norm_num

private theorem prime_oneHundredFiftyER_241 : Nat.Prime 241 := by
  norm_num

private theorem prime_oneHundredFiftyER_271 : Nat.Prime 271 := by
  norm_num

private theorem prime_oneHundredFiftyER_281 : Nat.Prime 281 := by
  norm_num

private theorem prime_oneHundredFiftyER_283 : Nat.Prime 283 := by
  norm_num

private theorem prime_oneHundredFiftyER_293 : Nat.Prime 293 := by
  norm_num

private theorem prime_oneHundredFiftyER_307 : Nat.Prime 307 := by
  norm_num

private theorem prime_oneHundredFiftyER_311 : Nat.Prime 311 := by
  norm_num

private theorem prime_oneHundredFiftyER_367 : Nat.Prime 367 := by
  norm_num

private theorem prime_oneHundredFiftyER_373 : Nat.Prime 373 := by
  norm_num

private theorem prime_oneHundredFiftyER_383 : Nat.Prime 383 := by
  norm_num

private theorem prime_oneHundredFiftyER_397 : Nat.Prime 397 := by
  norm_num

private theorem prime_oneHundredFiftyER_409 : Nat.Prime 409 := by
  norm_num

private theorem prime_oneHundredFiftyER_419 : Nat.Prime 419 := by
  norm_num

private theorem prime_oneHundredFiftyER_421 : Nat.Prime 421 := by
  norm_num

private theorem prime_oneHundredFiftyER_431 : Nat.Prime 431 := by
  norm_num

private theorem prime_oneHundredFiftyER_433 : Nat.Prime 433 := by
  norm_num

private theorem prime_oneHundredFiftyER_449 : Nat.Prime 449 := by
  norm_num

private theorem prime_oneHundredFiftyER_457 : Nat.Prime 457 := by
  norm_num

private theorem prime_oneHundredFiftyER_461 : Nat.Prime 461 := by
  norm_num

private theorem prime_oneHundredFiftyER_463 : Nat.Prime 463 := by
  norm_num

private theorem prime_oneHundredFiftyER_467 : Nat.Prime 467 := by
  norm_num

private theorem prime_oneHundredFiftyER_479 : Nat.Prime 479 := by
  norm_num

private theorem prime_oneHundredFiftyER_491 : Nat.Prime 491 := by
  norm_num

private theorem prime_oneHundredFiftyER_503 : Nat.Prime 503 := by
  norm_num

private theorem prime_oneHundredFiftyER_521 : Nat.Prime 521 := by
  norm_num

private theorem prime_oneHundredFiftyER_523 : Nat.Prime 523 := by
  norm_num

private theorem prime_oneHundredFiftyER_541 : Nat.Prime 541 := by
  norm_num

private theorem prime_oneHundredFiftyER_557 : Nat.Prime 557 := by
  norm_num

private theorem prime_oneHundredFiftyER_569 : Nat.Prime 569 := by
  norm_num

private theorem prime_oneHundredFiftyER_593 : Nat.Prime 593 := by
  norm_num

private theorem prime_oneHundredFiftyER_601 : Nat.Prime 601 := by
  norm_num

private theorem prime_oneHundredFiftyER_607 : Nat.Prime 607 := by
  norm_num

private theorem prime_oneHundredFiftyER_619 : Nat.Prime 619 := by
  norm_num

private theorem prime_oneHundredFiftyER_631 : Nat.Prime 631 := by
  norm_num

private theorem prime_oneHundredFiftyER_641 : Nat.Prime 641 := by
  norm_num

private theorem prime_oneHundredFiftyER_643 : Nat.Prime 643 := by
  norm_num

private theorem prime_oneHundredFiftyER_647 : Nat.Prime 647 := by
  norm_num

private theorem prime_oneHundredFiftyER_653 : Nat.Prime 653 := by
  norm_num

private theorem prime_oneHundredFiftyER_659 : Nat.Prime 659 := by
  norm_num

private theorem prime_oneHundredFiftyER_683 : Nat.Prime 683 := by
  norm_num

private theorem prime_oneHundredFiftyER_709 : Nat.Prime 709 := by
  norm_num

private theorem prime_oneHundredFiftyER_719 : Nat.Prime 719 := by
  norm_num

private theorem prime_oneHundredFiftyER_727 : Nat.Prime 727 := by
  norm_num

private theorem prime_oneHundredFiftyER_743 : Nat.Prime 743 := by
  norm_num

private theorem prime_oneHundredFiftyER_797 : Nat.Prime 797 := by
  norm_num

private theorem prime_oneHundredFiftyER_809 : Nat.Prime 809 := by
  norm_num

private theorem prime_oneHundredFiftyER_811 : Nat.Prime 811 := by
  norm_num

private theorem prime_oneHundredFiftyER_821 : Nat.Prime 821 := by
  norm_num

private theorem prime_oneHundredFiftyER_839 : Nat.Prime 839 := by
  norm_num

private theorem prime_oneHundredFiftyER_853 : Nat.Prime 853 := by
  norm_num

private theorem prime_oneHundredFiftyER_947 : Nat.Prime 947 := by
  norm_num

private theorem prime_oneHundredFiftyER_977 : Nat.Prime 977 := by
  norm_num

private theorem prime_oneHundredFiftyER_997 : Nat.Prime 997 := by
  norm_num

private theorem prime_oneHundredFiftyER_1009 : Nat.Prime 1009 := by
  norm_num

private theorem prime_oneHundredFiftyER_1013 : Nat.Prime 1013 := by
  norm_num

private theorem prime_oneHundredFiftyER_1019 : Nat.Prime 1019 := by
  norm_num

private theorem prime_oneHundredFiftyER_1039 : Nat.Prime 1039 := by
  norm_num

private theorem prime_oneHundredFiftyER_1061 : Nat.Prime 1061 := by
  norm_num

private theorem prime_oneHundredFiftyER_1063 : Nat.Prime 1063 := by
  norm_num

private theorem prime_oneHundredFiftyER_1069 : Nat.Prime 1069 := by
  norm_num

private theorem prime_oneHundredFiftyER_1087 : Nat.Prime 1087 := by
  norm_num

private theorem prime_oneHundredFiftyER_1097 : Nat.Prime 1097 := by
  norm_num

private theorem prime_oneHundredFiftyER_1109 : Nat.Prime 1109 := by
  norm_num

private theorem prime_oneHundredFiftyER_1151 : Nat.Prime 1151 := by
  norm_num

private theorem prime_oneHundredFiftyER_1153 : Nat.Prime 1153 := by
  norm_num

private theorem prime_oneHundredFiftyER_1163 : Nat.Prime 1163 := by
  norm_num

private theorem prime_oneHundredFiftyER_1187 : Nat.Prime 1187 := by
  norm_num

private theorem prime_oneHundredFiftyER_1249 : Nat.Prime 1249 := by
  norm_num

private theorem prime_oneHundredFiftyER_1289 : Nat.Prime 1289 := by
  norm_num

private theorem prime_oneHundredFiftyER_1307 : Nat.Prime 1307 := by
  norm_num

private theorem prime_oneHundredFiftyER_1429 : Nat.Prime 1429 := by
  norm_num

private theorem prime_oneHundredFiftyER_1471 : Nat.Prime 1471 := by
  norm_num

private theorem prime_oneHundredFiftyER_1481 : Nat.Prime 1481 := by
  norm_num

private theorem prime_oneHundredFiftyER_1487 : Nat.Prime 1487 := by
  norm_num

private theorem prime_oneHundredFiftyER_1493 : Nat.Prime 1493 := by
  norm_num

private theorem prime_oneHundredFiftyER_1499 : Nat.Prime 1499 := by
  norm_num

private theorem prime_oneHundredFiftyER_1549 : Nat.Prime 1549 := by
  norm_num

private theorem prime_oneHundredFiftyER_1553 : Nat.Prime 1553 := by
  norm_num

private theorem prime_oneHundredFiftyER_1571 : Nat.Prime 1571 := by
  norm_num

private theorem prime_oneHundredFiftyER_1583 : Nat.Prime 1583 := by
  norm_num

private theorem prime_oneHundredFiftyER_1597 : Nat.Prime 1597 := by
  norm_num

private theorem prime_oneHundredFiftyER_1613 : Nat.Prime 1613 := by
  norm_num

private theorem prime_oneHundredFiftyER_1663 : Nat.Prime 1663 := by
  norm_num

private theorem prime_oneHundredFiftyER_1667 : Nat.Prime 1667 := by
  norm_num

private theorem prime_oneHundredFiftyER_1693 : Nat.Prime 1693 := by
  norm_num

private theorem prime_oneHundredFiftyER_1697 : Nat.Prime 1697 := by
  norm_num

private theorem prime_oneHundredFiftyER_1699 : Nat.Prime 1699 := by
  norm_num

private theorem prime_oneHundredFiftyER_1811 : Nat.Prime 1811 := by
  norm_num

private theorem prime_oneHundredFiftyER_1867 : Nat.Prime 1867 := by
  norm_num

private theorem prime_oneHundredFiftyER_1889 : Nat.Prime 1889 := by
  norm_num

private theorem prime_oneHundredFiftyER_1907 : Nat.Prime 1907 := by
  norm_num

private theorem prime_oneHundredFiftyER_1949 : Nat.Prime 1949 := by
  norm_num

private theorem prime_oneHundredFiftyER_2017 : Nat.Prime 2017 := by
  norm_num

private theorem prime_oneHundredFiftyER_2063 : Nat.Prime 2063 := by
  norm_num

private theorem prime_oneHundredFiftyER_2297 : Nat.Prime 2297 := by
  norm_num

private theorem prime_oneHundredFiftyER_2341 : Nat.Prime 2341 := by
  norm_num

private theorem prime_oneHundredFiftyER_2383 : Nat.Prime 2383 := by
  norm_num

private theorem prime_oneHundredFiftyER_2473 : Nat.Prime 2473 := by
  norm_num

private theorem prime_oneHundredFiftyER_2593 : Nat.Prime 2593 := by
  norm_num

private theorem prime_oneHundredFiftyER_2609 : Nat.Prime 2609 := by
  norm_num

private theorem prime_oneHundredFiftyER_2647 : Nat.Prime 2647 := by
  norm_num

private theorem prime_oneHundredFiftyER_2657 : Nat.Prime 2657 := by
  norm_num

private theorem prime_oneHundredFiftyER_2731 : Nat.Prime 2731 := by
  norm_num

private theorem prime_oneHundredFiftyER_2777 : Nat.Prime 2777 := by
  norm_num

private theorem prime_oneHundredFiftyER_2797 : Nat.Prime 2797 := by
  norm_num

private theorem prime_oneHundredFiftyER_2819 : Nat.Prime 2819 := by
  norm_num

private theorem prime_oneHundredFiftyER_2861 : Nat.Prime 2861 := by
  norm_num

private theorem prime_oneHundredFiftyER_3067 : Nat.Prime 3067 := by
  norm_num

private theorem prime_oneHundredFiftyER_3449 : Nat.Prime 3449 := by
  norm_num

private theorem prime_oneHundredFiftyER_3461 : Nat.Prime 3461 := by
  norm_num

private theorem prime_oneHundredFiftyER_3463 : Nat.Prime 3463 := by
  norm_num

private theorem prime_oneHundredFiftyER_3467 : Nat.Prime 3467 := by
  norm_num

private theorem prime_oneHundredFiftyER_3697 : Nat.Prime 3697 := by
  norm_num

private theorem prime_oneHundredFiftyER_3917 : Nat.Prime 3917 := by
  norm_num

private theorem prime_oneHundredFiftyER_4177 : Nat.Prime 4177 := by
  norm_num

private theorem prime_oneHundredFiftyER_4621 : Nat.Prime 4621 := by
  norm_num

private theorem prime_oneHundredFiftyER_4999 : Nat.Prime 4999 := by
  norm_num

private theorem prime_oneHundredFiftyER_5273 : Nat.Prime 5273 := by
  norm_num

private theorem prime_oneHundredFiftyER_5419 : Nat.Prime 5419 := by
  norm_num

private theorem prime_oneHundredFiftyER_5689 : Nat.Prime 5689 := by
  norm_num

private theorem prime_oneHundredFiftyER_5821 : Nat.Prime 5821 := by
  norm_num

private theorem prime_oneHundredFiftyER_6491 : Nat.Prime 6491 := by
  norm_num

private theorem prime_oneHundredFiftyER_6793 : Nat.Prime 6793 := by
  norm_num

private theorem prime_oneHundredFiftyER_6863 : Nat.Prime 6863 := by
  norm_num

private theorem prime_oneHundredFiftyER_7043 : Nat.Prime 7043 := by
  norm_num

private theorem prime_oneHundredFiftyER_7351 : Nat.Prime 7351 := by
  norm_num

private theorem prime_oneHundredFiftyER_8273 : Nat.Prime 8273 := by
  norm_num

private theorem prime_oneHundredFiftyER_8821 : Nat.Prime 8821 := by
  norm_num

private theorem prime_oneHundredFiftyER_8999 : Nat.Prime 8999 := by
  norm_num

private theorem prime_oneHundredFiftyER_9283 : Nat.Prime 9283 := by
  norm_num

private theorem prime_oneHundredFiftyER_9371 : Nat.Prime 9371 := by
  norm_num

private theorem prime_oneHundredFiftyER_10499 : Nat.Prime 10499 := by
  norm_num

private theorem prime_oneHundredFiftyER_10909 : Nat.Prime 10909 := by
  norm_num

private theorem prime_oneHundredFiftyER_11059 : Nat.Prime 11059 := by
  norm_num

private theorem prime_oneHundredFiftyER_11161 : Nat.Prime 11161 := by
  norm_num

private theorem prime_oneHundredFiftyER_11353 : Nat.Prime 11353 := by
  norm_num

private theorem prime_oneHundredFiftyER_11437 : Nat.Prime 11437 := by
  norm_num

private theorem prime_oneHundredFiftyER_11491 : Nat.Prime 11491 := by
  norm_num

private theorem prime_oneHundredFiftyER_11551 : Nat.Prime 11551 := by
  norm_num

private theorem prime_oneHundredFiftyER_11593 : Nat.Prime 11593 := by
  norm_num

private theorem prime_oneHundredFiftyER_11923 : Nat.Prime 11923 := by
  norm_num

private theorem prime_oneHundredFiftyER_12113 : Nat.Prime 12113 := by
  norm_num

private theorem prime_oneHundredFiftyER_12539 : Nat.Prime 12539 := by
  norm_num

private theorem prime_oneHundredFiftyER_12697 : Nat.Prime 12697 := by
  norm_num

private theorem prime_oneHundredFiftyER_12823 : Nat.Prime 12823 := by
  norm_num

private theorem prime_oneHundredFiftyER_13043 : Nat.Prime 13043 := by
  norm_num

private theorem prime_oneHundredFiftyER_13147 : Nat.Prime 13147 := by
  norm_num

private theorem prime_oneHundredFiftyER_13159 : Nat.Prime 13159 := by
  norm_num

private theorem prime_oneHundredFiftyER_13417 : Nat.Prime 13417 := by
  norm_num

private theorem prime_oneHundredFiftyER_13463 : Nat.Prime 13463 := by
  norm_num

private theorem prime_oneHundredFiftyER_13711 : Nat.Prime 13711 := by
  norm_num

private theorem prime_oneHundredFiftyER_14029 : Nat.Prime 14029 := by
  norm_num

private theorem prime_oneHundredFiftyER_14389 : Nat.Prime 14389 := by
  norm_num

private theorem prime_oneHundredFiftyER_14437 : Nat.Prime 14437 := by
  norm_num

private theorem prime_oneHundredFiftyER_14843 : Nat.Prime 14843 := by
  norm_num

private theorem prime_oneHundredFiftyER_15259 : Nat.Prime 15259 := by
  norm_num

private theorem prime_oneHundredFiftyER_15269 : Nat.Prime 15269 := by
  norm_num

private theorem prime_oneHundredFiftyER_15377 : Nat.Prime 15377 := by
  norm_num

private theorem prime_oneHundredFiftyER_16187 : Nat.Prime 16187 := by
  norm_num

private theorem prime_oneHundredFiftyER_16189 : Nat.Prime 16189 := by
  norm_num

private theorem prime_oneHundredFiftyER_16349 : Nat.Prime 16349 := by
  norm_num

private theorem prime_oneHundredFiftyER_16763 : Nat.Prime 16763 := by
  norm_num

private theorem prime_oneHundredFiftyER_17203 : Nat.Prime 17203 := by
  norm_num

private theorem prime_oneHundredFiftyER_18911 : Nat.Prime 18911 := by
  norm_num

private theorem prime_oneHundredFiftyER_18973 : Nat.Prime 18973 := by
  norm_num

private theorem prime_oneHundredFiftyER_19471 : Nat.Prime 19471 := by
  norm_num

private theorem prime_oneHundredFiftyER_20753 : Nat.Prime 20753 := by
  norm_num

private theorem prime_oneHundredFiftyER_21221 : Nat.Prime 21221 := by
  norm_num

private theorem prime_oneHundredFiftyER_21617 : Nat.Prime 21617 := by
  norm_num

private theorem prime_oneHundredFiftyER_21991 : Nat.Prime 21991 := by
  norm_num

private theorem prime_oneHundredFiftyER_22003 : Nat.Prime 22003 := by
  norm_num

private theorem prime_oneHundredFiftyER_22943 : Nat.Prime 22943 := by
  norm_num

private theorem prime_oneHundredFiftyER_23027 : Nat.Prime 23027 := by
  norm_num

private theorem prime_oneHundredFiftyER_24659 : Nat.Prime 24659 := by
  norm_num

private theorem prime_oneHundredFiftyER_25117 : Nat.Prime 25117 := by
  norm_num

private theorem prime_oneHundredFiftyER_25541 : Nat.Prime 25541 := by
  norm_num

private theorem prime_oneHundredFiftyER_27817 : Nat.Prime 27817 := by
  norm_num

private theorem prime_oneHundredFiftyER_28411 : Nat.Prime 28411 := by
  norm_num

private theorem prime_oneHundredFiftyER_28541 : Nat.Prime 28541 := by
  norm_num

private theorem prime_oneHundredFiftyER_29399 : Nat.Prime 29399 := by
  norm_num

private theorem prime_oneHundredFiftyER_29411 : Nat.Prime 29411 := by
  norm_num

private theorem prime_oneHundredFiftyER_29527 : Nat.Prime 29527 := by
  norm_num

private theorem prime_oneHundredFiftyER_30097 : Nat.Prime 30097 := by
  norm_num

private theorem prime_oneHundredFiftyER_30491 : Nat.Prime 30491 := by
  norm_num

private theorem prime_oneHundredFiftyER_31177 : Nat.Prime 31177 := by
  norm_num

private theorem prime_oneHundredFiftyER_32371 : Nat.Prime 32371 := by
  norm_num

private theorem prime_oneHundredFiftyER_32609 : Nat.Prime 32609 := by
  norm_num

private theorem prime_oneHundredFiftyER_33427 : Nat.Prime 33427 := by
  norm_num

private theorem prime_oneHundredFiftyER_33721 : Nat.Prime 33721 := by
  norm_num

private theorem prime_oneHundredFiftyER_33757 : Nat.Prime 33757 := by
  norm_num

private theorem prime_oneHundredFiftyER_33811 : Nat.Prime 33811 := by
  norm_num

private theorem prime_oneHundredFiftyER_33827 : Nat.Prime 33827 := by
  norm_num

private theorem prime_oneHundredFiftyER_34603 : Nat.Prime 34603 := by
  norm_num

private theorem prime_oneHundredFiftyER_35069 : Nat.Prime 35069 := by
  norm_num

private theorem prime_oneHundredFiftyER_37493 : Nat.Prime 37493 := by
  norm_num

private theorem prime_oneHundredFiftyER_37657 : Nat.Prime 37657 := by
  norm_num

private theorem prime_oneHundredFiftyER_39341 : Nat.Prime 39341 := by
  norm_num

private theorem prime_oneHundredFiftyER_39511 : Nat.Prime 39511 := by
  norm_num

private theorem prime_oneHundredFiftyER_40151 : Nat.Prime 40151 := by
  norm_num

private theorem prime_oneHundredFiftyER_40357 : Nat.Prime 40357 := by
  norm_num

private theorem prime_oneHundredFiftyER_45691 : Nat.Prime 45691 := by
  norm_num

private theorem prime_oneHundredFiftyER_47417 : Nat.Prime 47417 := by
  norm_num

private theorem prime_oneHundredFiftyER_47713 : Nat.Prime 47713 := by
  norm_num

private theorem prime_oneHundredFiftyER_48017 : Nat.Prime 48017 := by
  norm_num

private theorem prime_oneHundredFiftyER_49157 : Nat.Prime 49157 := by
  norm_num

private theorem prime_oneHundredFiftyER_49823 : Nat.Prime 49823 := by
  norm_num

private theorem prime_oneHundredFiftyER_51683 : Nat.Prime 51683 := by
  norm_num

private theorem prime_oneHundredFiftyER_51749 : Nat.Prime 51749 := by
  norm_num

private theorem prime_oneHundredFiftyER_52457 : Nat.Prime 52457 := by
  norm_num

private theorem prime_oneHundredFiftyER_54581 : Nat.Prime 54581 := by
  norm_num

private theorem prime_oneHundredFiftyER_54829 : Nat.Prime 54829 := by
  norm_num

private theorem prime_oneHundredFiftyER_55541 : Nat.Prime 55541 := by
  norm_num

private theorem prime_oneHundredFiftyER_55921 : Nat.Prime 55921 := by
  norm_num

private theorem prime_oneHundredFiftyER_56237 : Nat.Prime 56237 := by
  norm_num

private theorem prime_oneHundredFiftyER_59399 : Nat.Prime 59399 := by
  norm_num

private theorem prime_oneHundredFiftyER_62303 : Nat.Prime 62303 := by
  norm_num

private theorem prime_oneHundredFiftyER_62903 : Nat.Prime 62903 := by
  norm_num

private theorem prime_oneHundredFiftyER_63907 : Nat.Prime 63907 := by
  norm_num

private theorem prime_oneHundredFiftyER_67231 : Nat.Prime 67231 := by
  norm_num

private theorem prime_oneHundredFiftyER_69997 : Nat.Prime 69997 := by
  norm_num

private theorem prime_oneHundredFiftyER_70157 : Nat.Prime 70157 := by
  norm_num

private theorem prime_oneHundredFiftyER_70901 : Nat.Prime 70901 := by
  norm_num

private theorem prime_oneHundredFiftyER_70957 : Nat.Prime 70957 := by
  norm_num

private theorem prime_oneHundredFiftyER_71191 : Nat.Prime 71191 := by
  norm_num

private theorem prime_oneHundredFiftyER_73013 : Nat.Prime 73013 := by
  norm_num

private theorem prime_oneHundredFiftyER_74923 : Nat.Prime 74923 := by
  norm_num

private theorem prime_oneHundredFiftyER_77041 : Nat.Prime 77041 := by
  norm_num

private theorem prime_oneHundredFiftyER_81559 : Nat.Prime 81559 := by
  norm_num

private theorem prime_oneHundredFiftyER_84317 : Nat.Prime 84317 := by
  norm_num

private theorem prime_oneHundredFiftyER_84443 : Nat.Prime 84443 := by
  norm_num

private theorem prime_oneHundredFiftyER_88003 : Nat.Prime 88003 := by
  norm_num

private theorem prime_oneHundredFiftyER_90023 : Nat.Prime 90023 := by
  norm_num

private theorem prime_oneHundredFiftyER_90173 : Nat.Prime 90173 := by
  norm_num

private theorem prime_oneHundredFiftyER_93337 : Nat.Prime 93337 := by
  norm_num

private theorem prime_oneHundredFiftyER_93629 : Nat.Prime 93629 := by
  norm_num

private theorem prime_oneHundredFiftyER_93997 : Nat.Prime 93997 := by
  norm_num

private theorem prime_oneHundredFiftyER_95273 : Nat.Prime 95273 := by
  norm_num

private theorem prime_oneHundredFiftyER_96697 : Nat.Prime 96697 := by
  norm_num

private theorem prime_oneHundredFiftyER_98947 : Nat.Prime 98947 := by
  norm_num

private theorem prime_oneHundredFiftyER_100183 : Nat.Prime 100183 := by
  norm_num

private theorem prime_oneHundredFiftyER_100517 : Nat.Prime 100517 := by
  norm_num

private theorem prime_oneHundredFiftyER_106753 : Nat.Prime 106753 := by
  norm_num

private theorem prime_oneHundredFiftyER_115763 : Nat.Prime 115763 := by
  norm_num

private theorem prime_oneHundredFiftyER_115883 : Nat.Prime 115883 := by
  norm_num

private theorem prime_oneHundredFiftyER_120091 : Nat.Prime 120091 := by
  norm_num

private theorem prime_oneHundredFiftyER_125183 : Nat.Prime 125183 := by
  norm_num

private theorem prime_oneHundredFiftyER_125287 : Nat.Prime 125287 := by
  norm_num

private theorem prime_oneHundredFiftyER_126151 : Nat.Prime 126151 := by
  norm_num

private theorem prime_oneHundredFiftyER_131893 : Nat.Prime 131893 := by
  norm_num

private theorem prime_oneHundredFiftyER_140053 : Nat.Prime 140053 := by
  norm_num

private theorem prime_oneHundredFiftyER_152597 : Nat.Prime 152597 := by
  norm_num

private theorem prime_oneHundredFiftyER_171401 : Nat.Prime 171401 := by
  norm_num

private theorem prime_oneHundredFiftyER_171733 : Nat.Prime 171733 := by
  norm_num

private theorem prime_oneHundredFiftyER_174481 : Nat.Prime 174481 := by
  norm_num

private theorem prime_oneHundredFiftyER_179969 : Nat.Prime 179969 := by
  norm_num

private theorem prime_oneHundredFiftyER_183263 : Nat.Prime 183263 := by
  norm_num

private theorem prime_oneHundredFiftyER_185153 : Nat.Prime 185153 := by
  norm_num

private theorem prime_oneHundredFiftyER_192749 : Nat.Prime 192749 := by
  norm_num

private theorem prime_oneHundredFiftyER_195253 : Nat.Prime 195253 := by
  norm_num

private theorem prime_oneHundredFiftyER_198637 : Nat.Prime 198637 := by
  norm_num

private theorem prime_oneHundredFiftyER_213079 : Nat.Prime 213079 := by
  norm_num

private theorem prime_oneHundredFiftyER_219979 : Nat.Prime 219979 := by
  norm_num

private theorem prime_oneHundredFiftyER_251917 : Nat.Prime 251917 := by
  norm_num

private theorem prime_oneHundredFiftyER_253543 : Nat.Prime 253543 := by
  norm_num

private theorem prime_oneHundredFiftyER_264757 : Nat.Prime 264757 := by
  norm_num

private theorem prime_oneHundredFiftyER_266797 : Nat.Prime 266797 := by
  norm_num

private theorem prime_oneHundredFiftyER_279029 : Nat.Prime 279029 := by
  norm_num

private theorem prime_oneHundredFiftyER_287149 : Nat.Prime 287149 := by
  norm_num

private theorem prime_oneHundredFiftyER_306389 : Nat.Prime 306389 := by
  norm_num

private theorem prime_oneHundredFiftyER_322757 : Nat.Prime 322757 := by
  norm_num

private theorem prime_oneHundredFiftyER_335633 : Nat.Prime 335633 := by
  norm_num

private theorem prime_oneHundredFiftyER_341461 : Nat.Prime 341461 := by
  norm_num

private theorem prime_oneHundredFiftyER_351031 : Nat.Prime 351031 := by
  norm_num

private theorem prime_oneHundredFiftyER_366287 : Nat.Prime 366287 := by
  norm_num

private theorem prime_oneHundredFiftyER_390781 : Nat.Prime 390781 := by
  norm_num

private theorem prime_oneHundredFiftyER_401311 : Nat.Prime 401311 := by
  norm_num

private theorem prime_oneHundredFiftyER_414707 : Nat.Prime 414707 := by
  norm_num

private theorem prime_oneHundredFiftyER_415447 : Nat.Prime 415447 := by
  norm_num

private theorem prime_oneHundredFiftyER_417671 : Nat.Prime 417671 := by
  norm_num

private theorem prime_oneHundredFiftyER_447817 : Nat.Prime 447817 := by
  norm_num

private theorem prime_oneHundredFiftyER_519119 : Nat.Prime 519119 := by
  norm_num

private theorem prime_oneHundredFiftyER_542947 : Nat.Prime 542947 := by
  norm_num

private theorem prime_oneHundredFiftyER_546241 : Nat.Prime 546241 := by
  norm_num

private theorem prime_oneHundredFiftyER_588229 : Nat.Prime 588229 := by
  norm_num

private theorem prime_oneHundredFiftyER_588827 : Nat.Prime 588827 := by
  norm_num

private theorem prime_oneHundredFiftyER_590377 : Nat.Prime 590377 := by
  norm_num

private theorem prime_oneHundredFiftyER_607213 : Nat.Prime 607213 := by
  norm_num

private theorem prime_oneHundredFiftyER_673817 : Nat.Prime 673817 := by
  norm_num

private theorem prime_oneHundredFiftyER_679883 : Nat.Prime 679883 := by
  norm_num

private theorem prime_oneHundredFiftyER_681823 : Nat.Prime 681823 := by
  norm_num

private theorem prime_oneHundredFiftyER_691381 : Nat.Prime 691381 := by
  norm_num

private theorem prime_oneHundredFiftyER_700643 : Nat.Prime 700643 := by
  norm_num

private theorem prime_oneHundredFiftyER_702239 : Nat.Prime 702239 := by
  norm_num

private theorem prime_oneHundredFiftyER_716003 : Nat.Prime 716003 := by
  norm_num

private theorem prime_oneHundredFiftyER_725317 : Nat.Prime 725317 := by
  norm_num

private theorem prime_oneHundredFiftyER_725393 : Nat.Prime 725393 := by
  norm_num

private theorem prime_oneHundredFiftyER_734057 : Nat.Prime 734057 := by
  norm_num

private theorem prime_oneHundredFiftyER_743173 : Nat.Prime 743173 := by
  norm_num

private theorem prime_oneHundredFiftyER_744859 : Nat.Prime 744859 := by
  norm_num

private theorem prime_oneHundredFiftyER_771643 : Nat.Prime 771643 := by
  norm_num

private theorem prime_oneHundredFiftyER_781063 : Nat.Prime 781063 := by
  norm_num

private theorem prime_oneHundredFiftyER_785287 : Nat.Prime 785287 := by
  norm_num

private theorem prime_oneHundredFiftyER_888109 : Nat.Prime 888109 := by
  norm_num

private theorem prime_oneHundredFiftyER_898727 : Nat.Prime 898727 := by
  norm_num

private theorem prime_oneHundredFiftyER_926657 : Nat.Prime 926657 := by
  norm_num

private theorem prime_oneHundredFiftyER_1024589 : Nat.Prime 1024589 := by
  norm_num

private theorem prime_oneHundredFiftyER_1033741 : Nat.Prime 1033741 := by
  norm_num

private theorem prime_oneHundredFiftyER_1045123 : Nat.Prime 1045123 := by
  norm_num

private theorem prime_oneHundredFiftyER_1090151 : Nat.Prime 1090151 := by
  norm_num

private theorem prime_oneHundredFiftyER_1104739 : Nat.Prime 1104739 := by
  norm_num

private theorem prime_oneHundredFiftyER_1150063 : Nat.Prime 1150063 := by
  norm_num

private theorem prime_oneHundredFiftyER_1243169 : Nat.Prime 1243169 := by
  norm_num

private theorem prime_oneHundredFiftyER_1260341 : Nat.Prime 1260341 := by
  norm_num

private theorem prime_oneHundredFiftyER_1314113 : Nat.Prime 1314113 := by
  norm_num

private theorem prime_oneHundredFiftyER_1336579 : Nat.Prime 1336579 := by
  norm_num

private theorem prime_oneHundredFiftyER_1369483 : Nat.Prime 1369483 := by
  norm_num

private theorem prime_oneHundredFiftyER_1375981 : Nat.Prime 1375981 := by
  norm_num

private theorem prime_oneHundredFiftyER_1419233 : Nat.Prime 1419233 := by
  norm_num

private theorem prime_oneHundredFiftyER_1429249 : Nat.Prime 1429249 := by
  norm_num

private theorem prime_oneHundredFiftyER_1450747 : Nat.Prime 1450747 := by
  norm_num

private theorem prime_oneHundredFiftyER_1489021 : Nat.Prime 1489021 := by
  norm_num

private theorem prime_oneHundredFiftyER_1524007 : Nat.Prime 1524007 := by
  norm_num

private theorem prime_oneHundredFiftyER_1577353 : Nat.Prime 1577353 := by
  norm_num

private theorem prime_oneHundredFiftyER_1601107 : Nat.Prime 1601107 := by
  norm_num

private theorem prime_oneHundredFiftyER_1729747 : Nat.Prime 1729747 := by
  norm_num

private theorem prime_oneHundredFiftyER_1890641 : Nat.Prime 1890641 := by
  norm_num

private theorem prime_oneHundredFiftyER_1924837 : Nat.Prime 1924837 := by
  norm_num

private theorem prime_oneHundredFiftyER_1983853 : Nat.Prime 1983853 := by
  norm_num

private theorem prime_oneHundredFiftyER_2227417 : Nat.Prime 2227417 := by
  norm_num

private theorem prime_oneHundredFiftyER_2231857 : Nat.Prime 2231857 := by
  norm_num

private theorem prime_oneHundredFiftyER_2347153 : Nat.Prime 2347153 := by
  norm_num

private theorem prime_oneHundredFiftyER_2688467 : Nat.Prime 2688467 := by
  norm_num

private theorem prime_oneHundredFiftyER_2834047 : Nat.Prime 2834047 := by
  norm_num

private theorem prime_oneHundredFiftyER_3090781 : Nat.Prime 3090781 := by
  norm_num

private theorem prime_oneHundredFiftyER_3095341 : Nat.Prime 3095341 := by
  norm_num

private theorem prime_oneHundredFiftyER_3422563 : Nat.Prime 3422563 := by
  norm_num

private theorem prime_oneHundredFiftyER_3506891 : Nat.Prime 3506891 := by
  norm_num

private theorem prime_oneHundredFiftyER_3556321 : Nat.Prime 3556321 := by
  norm_num

private theorem prime_oneHundredFiftyER_3586907 : Nat.Prime 3586907 := by
  norm_num

private theorem prime_oneHundredFiftyER_3591073 : Nat.Prime 3591073 := by
  norm_num

private theorem prime_oneHundredFiftyER_3599009 : Nat.Prime 3599009 := by
  norm_num

private theorem prime_oneHundredFiftyER_3756097 : Nat.Prime 3756097 := by
  norm_num

private theorem prime_oneHundredFiftyER_3797837 : Nat.Prime 3797837 := by
  norm_num

private theorem prime_oneHundredFiftyER_4059113 : Nat.Prime 4059113 := by
  norm_num

private theorem prime_oneHundredFiftyER_4130039 : Nat.Prime 4130039 := by
  norm_num

private theorem prime_oneHundredFiftyER_4308277 : Nat.Prime 4308277 := by
  norm_num

private theorem prime_oneHundredFiftyER_4419907 : Nat.Prime 4419907 := by
  norm_num

private theorem prime_oneHundredFiftyER_4671071 : Nat.Prime 4671071 := by
  norm_num

private theorem prime_oneHundredFiftyER_4674151 : Nat.Prime 4674151 := by
  norm_num

private theorem prime_oneHundredFiftyER_4824163 : Nat.Prime 4824163 := by
  norm_num

private theorem prime_oneHundredFiftyER_4972199 : Nat.Prime 4972199 := by
  norm_num

private theorem prime_oneHundredFiftyER_5730737 : Nat.Prime 5730737 := by
  norm_num

private theorem prime_oneHundredFiftyER_5795123 : Nat.Prime 5795123 := by
  norm_num

private theorem prime_oneHundredFiftyER_6039659 : Nat.Prime 6039659 := by
  norm_num

private theorem prime_oneHundredFiftyER_6336347 : Nat.Prime 6336347 := by
  norm_num

private theorem prime_oneHundredFiftyER_6380281 : Nat.Prime 6380281 := by
  norm_num

private theorem prime_oneHundredFiftyER_6478453 : Nat.Prime 6478453 := by
  norm_num

private theorem prime_oneHundredFiftyER_6496339 : Nat.Prime 6496339 := by
  norm_num

private theorem prime_oneHundredFiftyER_6697657 : Nat.Prime 6697657 := by
  norm_num

private theorem prime_oneHundredFiftyER_6703889 : Nat.Prime 6703889 := by
  norm_num

private theorem prime_oneHundredFiftyER_6953333 : Nat.Prime 6953333 := by
  norm_num

private theorem prime_oneHundredFiftyER_7537657 : Nat.Prime 7537657 := by
  norm_num

private theorem prime_oneHundredFiftyER_7695671 : Nat.Prime 7695671 := by
  norm_num

private theorem prime_oneHundredFiftyER_7821643 : Nat.Prime 7821643 := by
  norm_num

private theorem prime_oneHundredFiftyER_8095547 : Nat.Prime 8095547 := by
  norm_num

private theorem prime_oneHundredFiftyER_8105401 : Nat.Prime 8105401 := by
  norm_num

private theorem prime_oneHundredFiftyER_8116753 : Nat.Prime 8116753 := by
  norm_num

private theorem prime_oneHundredFiftyER_8120677 : Nat.Prime 8120677 := by
  norm_num

private theorem prime_oneHundredFiftyER_9024679 : Nat.Prime 9024679 := by
  norm_num

private theorem prime_oneHundredFiftyER_9407971 : Nat.Prime 9407971 := by
  norm_num

private theorem prime_oneHundredFiftyER_9500191 : Nat.Prime 9500191 := by
  norm_num

private theorem prime_oneHundredFiftyER_9554807 : Nat.Prime 9554807 := by
  norm_num

private theorem prime_oneHundredFiftyER_10820141 : Nat.Prime 10820141 := by
  norm_num

private theorem prime_oneHundredFiftyER_10845649 : Nat.Prime 10845649 := by
  norm_num

private theorem prime_oneHundredFiftyER_12042907 : Nat.Prime 12042907 := by
  norm_num

private theorem prime_oneHundredFiftyER_12844297 : Nat.Prime 12844297 := by
  norm_num

private theorem prime_oneHundredFiftyER_13617913 : Nat.Prime 13617913 := by
  norm_num

private theorem prime_oneHundredFiftyER_14030411 : Nat.Prime 14030411 := by
  norm_num

private theorem prime_oneHundredFiftyER_14483401 : Nat.Prime 14483401 := by
  norm_num

private theorem prime_oneHundredFiftyER_20347321 : Nat.Prime 20347321 := by
  norm_num

private theorem prime_oneHundredFiftyER_20653001 : Nat.Prime 20653001 := by
  norm_num

private theorem prime_oneHundredFiftyER_22363529 : Nat.Prime 22363529 := by
  norm_num

private theorem prime_oneHundredFiftyER_22998923 : Nat.Prime 22998923 := by
  norm_num

private theorem prime_oneHundredFiftyER_23871599 : Nat.Prime 23871599 := by
  norm_num

private theorem prime_oneHundredFiftyER_24205387 : Nat.Prime 24205387 := by
  norm_num

private theorem prime_oneHundredFiftyER_25717303 : Nat.Prime 25717303 := by
  norm_num

private theorem prime_oneHundredFiftyER_26198603 : Nat.Prime 26198603 := by
  norm_num

private theorem prime_oneHundredFiftyER_26270561 : Nat.Prime 26270561 := by
  norm_num

private theorem prime_oneHundredFiftyER_27340603 : Nat.Prime 27340603 := by
  norm_num

private theorem prime_oneHundredFiftyER_29967017 : Nat.Prime 29967017 := by
  norm_num

private theorem prime_oneHundredFiftyER_30189371 : Nat.Prime 30189371 := by
  apply lucas_primality 30189371 (2 : ZMod 30189371)
  · rw [← oneHundredFiftyERFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (1667, 1), (1811, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (1667, 1), (1811, 1)] : List FactorBlock).map factorBlockValue).prod) = 30189371 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyER_2
      · exact prime_oneHundredFiftyER_5
      · exact prime_oneHundredFiftyER_1667
      · exact prime_oneHundredFiftyER_1811
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 30189371) ^ 15094685 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 30189371) ^ 6037874 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 30189371) ^ 18110 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 30189371) ^ 16670 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyER_33323471 : Nat.Prime 33323471 := by
  apply lucas_primality 33323471 (11 : ZMod 33323471)
  · rw [← oneHundredFiftyERFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (47, 1), (70901, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (47, 1), (70901, 1)] : List FactorBlock).map factorBlockValue).prod) = 33323471 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyER_2
      · exact prime_oneHundredFiftyER_5
      · exact prime_oneHundredFiftyER_47
      · exact prime_oneHundredFiftyER_70901
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 33323471) ^ 16661735 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (11 : ZMod 33323471) ^ 6664694 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (11 : ZMod 33323471) ^ 709010 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (11 : ZMod 33323471) ^ 470 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyER_37561127 : Nat.Prime 37561127 := by
  apply lucas_primality 37561127 (5 : ZMod 37561127)
  · rw [← oneHundredFiftyERFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 1), (1104739, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 1), (1104739, 1)] : List FactorBlock).map factorBlockValue).prod) = 37561127 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyER_2
      · exact prime_oneHundredFiftyER_17
      · exact prime_oneHundredFiftyER_1104739
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 37561127) ^ 18780563 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (5 : ZMod 37561127) ^ 2209478 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (5 : ZMod 37561127) ^ 34 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyER_39568549 : Nat.Prime 39568549 := by
  apply lucas_primality 39568549 (2 : ZMod 39568549)
  · rw [← oneHundredFiftyERFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (47, 1), (70157, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (47, 1), (70157, 1)] : List FactorBlock).map factorBlockValue).prod) = 39568549 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyER_2
      · exact prime_oneHundredFiftyER_3
      · exact prime_oneHundredFiftyER_47
      · exact prime_oneHundredFiftyER_70157
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 39568549) ^ 19784274 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 39568549) ^ 13189516 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 39568549) ^ 841884 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 39568549) ^ 564 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyER_40429021 : Nat.Prime 40429021 := by
  apply lucas_primality 40429021 (6 : ZMod 40429021)
  · rw [← oneHundredFiftyERFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (673817, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (673817, 1)] : List FactorBlock).map factorBlockValue).prod) = 40429021 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyER_2
      · exact prime_oneHundredFiftyER_3
      · exact prime_oneHundredFiftyER_5
      · exact prime_oneHundredFiftyER_673817
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 40429021) ^ 20214510 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (6 : ZMod 40429021) ^ 13476340 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (6 : ZMod 40429021) ^ 8085804 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (6 : ZMod 40429021) ^ 60 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyER_41291881 : Nat.Prime 41291881 := by
  apply lucas_primality 41291881 (34 : ZMod 41291881)
  · rw [← oneHundredFiftyERFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 1), (7, 1), (49157, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 1), (7, 1), (49157, 1)] : List FactorBlock).map factorBlockValue).prod) = 41291881 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyER_2
      · exact prime_oneHundredFiftyER_3
      · exact prime_oneHundredFiftyER_5
      · exact prime_oneHundredFiftyER_7
      · exact prime_oneHundredFiftyER_49157
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (34 : ZMod 41291881) ^ 20645940 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (34 : ZMod 41291881) ^ 13763960 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (34 : ZMod 41291881) ^ 8258376 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (34 : ZMod 41291881) ^ 5898840 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (34 : ZMod 41291881) ^ 840 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyER_41692589 : Nat.Prime 41692589 := by
  apply lucas_primality 41692589 (2 : ZMod 41692589)
  · rw [← oneHundredFiftyERFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (1489021, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (1489021, 1)] : List FactorBlock).map factorBlockValue).prod) = 41692589 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyER_2
      · exact prime_oneHundredFiftyER_7
      · exact prime_oneHundredFiftyER_1489021
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 41692589) ^ 20846294 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 41692589) ^ 5956084 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 41692589) ^ 28 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyER_43092877 : Nat.Prime 43092877 := by
  apply lucas_primality 43092877 (2 : ZMod 43092877)
  · rw [← oneHundredFiftyERFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (3591073, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (3591073, 1)] : List FactorBlock).map factorBlockValue).prod) = 43092877 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyER_2
      · exact prime_oneHundredFiftyER_3
      · exact prime_oneHundredFiftyER_3591073
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 43092877) ^ 21546438 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 43092877) ^ 14364292 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 43092877) ^ 12 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyER_44016979 : Nat.Prime 44016979 := by
  apply lucas_primality 44016979 (2 : ZMod 44016979)
  · rw [← oneHundredFiftyERFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (17, 1), (397, 1), (1087, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (17, 1), (397, 1), (1087, 1)] : List FactorBlock).map factorBlockValue).prod) = 44016979 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyER_2
      · exact prime_oneHundredFiftyER_3
      · exact prime_oneHundredFiftyER_17
      · exact prime_oneHundredFiftyER_397
      · exact prime_oneHundredFiftyER_1087
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 44016979) ^ 22008489 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 44016979) ^ 14672326 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 44016979) ^ 2589234 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 44016979) ^ 110874 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 44016979) ^ 40494 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyER_46174027 : Nat.Prime 46174027 := by
  apply lucas_primality 46174027 (2 : ZMod 46174027)
  · rw [← oneHundredFiftyERFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7695671, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7695671, 1)] : List FactorBlock).map factorBlockValue).prod) = 46174027 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyER_2
      · exact prime_oneHundredFiftyER_3
      · exact prime_oneHundredFiftyER_7695671
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 46174027) ^ 23087013 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 46174027) ^ 15391342 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 46174027) ^ 6 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyER_48503657 : Nat.Prime 48503657 := by
  apply lucas_primality 48503657 (3 : ZMod 48503657)
  · rw [← oneHundredFiftyERFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (19, 1), (41, 1), (43, 1), (181, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (19, 1), (41, 1), (43, 1), (181, 1)] : List FactorBlock).map factorBlockValue).prod) = 48503657 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyER_2
      · exact prime_oneHundredFiftyER_19
      · exact prime_oneHundredFiftyER_41
      · exact prime_oneHundredFiftyER_43
      · exact prime_oneHundredFiftyER_181
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 48503657) ^ 24251828 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (3 : ZMod 48503657) ^ 2552824 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (3 : ZMod 48503657) ^ 1183016 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (3 : ZMod 48503657) ^ 1127992 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (3 : ZMod 48503657) ^ 267976 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyER_49988033 : Nat.Prime 49988033 := by
  apply lucas_primality 49988033 (3 : ZMod 49988033)
  · rw [← oneHundredFiftyERFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (781063, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (781063, 1)] : List FactorBlock).map factorBlockValue).prod) = 49988033 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredFiftyER_2
      · exact prime_oneHundredFiftyER_781063
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 49988033) ^ 24994016 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (3 : ZMod 49988033) ^ 64 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyER_52864081 : Nat.Prime 52864081 := by
  apply lucas_primality 52864081 (17 : ZMod 52864081)
  · rw [← oneHundredFiftyERFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (5, 1), (19, 1), (11593, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (5, 1), (19, 1), (11593, 1)] : List FactorBlock).map factorBlockValue).prod) = 52864081 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyER_2
      · exact prime_oneHundredFiftyER_3
      · exact prime_oneHundredFiftyER_5
      · exact prime_oneHundredFiftyER_19
      · exact prime_oneHundredFiftyER_11593
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (17 : ZMod 52864081) ^ 26432040 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (17 : ZMod 52864081) ^ 17621360 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (17 : ZMod 52864081) ^ 10572816 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (17 : ZMod 52864081) ^ 2782320 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (17 : ZMod 52864081) ^ 4560 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyER_55212427 : Nat.Prime 55212427 := by
  apply lucas_primality 55212427 (2 : ZMod 55212427)
  · rw [← oneHundredFiftyERFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (31, 1), (98947, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (31, 1), (98947, 1)] : List FactorBlock).map factorBlockValue).prod) = 55212427 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyER_2
      · exact prime_oneHundredFiftyER_3
      · exact prime_oneHundredFiftyER_31
      · exact prime_oneHundredFiftyER_98947
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 55212427) ^ 27606213 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 55212427) ^ 18404142 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 55212427) ^ 1781046 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 55212427) ^ 558 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyER_59929613 : Nat.Prime 59929613 := by
  apply lucas_primality 59929613 (2 : ZMod 59929613)
  · rw [← oneHundredFiftyERFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (1811, 1), (8273, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (1811, 1), (8273, 1)] : List FactorBlock).map factorBlockValue).prod) = 59929613 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyER_2
      · exact prime_oneHundredFiftyER_1811
      · exact prime_oneHundredFiftyER_8273
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 59929613) ^ 29964806 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 59929613) ^ 33092 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 59929613) ^ 7244 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyER_67997183 : Nat.Prime 67997183 := by
  apply lucas_primality 67997183 (5 : ZMod 67997183)
  · rw [← oneHundredFiftyERFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (3090781, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (3090781, 1)] : List FactorBlock).map factorBlockValue).prod) = 67997183 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyER_2
      · exact prime_oneHundredFiftyER_11
      · exact prime_oneHundredFiftyER_3090781
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 67997183) ^ 33998591 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (5 : ZMod 67997183) ^ 6181562 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (5 : ZMod 67997183) ^ 22 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyER_77599139 : Nat.Prime 77599139 := by
  apply lucas_primality 77599139 (2 : ZMod 77599139)
  · rw [← oneHundredFiftyERFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (31, 1), (37, 1), (33827, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (31, 1), (37, 1), (33827, 1)] : List FactorBlock).map factorBlockValue).prod) = 77599139 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyER_2
      · exact prime_oneHundredFiftyER_31
      · exact prime_oneHundredFiftyER_37
      · exact prime_oneHundredFiftyER_33827
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 77599139) ^ 38799569 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 77599139) ^ 2503198 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 77599139) ^ 2097274 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 77599139) ^ 2294 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyER_77741437 : Nat.Prime 77741437 := by
  apply lucas_primality 77741437 (2 : ZMod 77741437)
  · rw [← oneHundredFiftyERFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (6478453, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (6478453, 1)] : List FactorBlock).map factorBlockValue).prod) = 77741437 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyER_2
      · exact prime_oneHundredFiftyER_3
      · exact prime_oneHundredFiftyER_6478453
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 77741437) ^ 38870718 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 77741437) ^ 25913812 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 77741437) ^ 12 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyER_79952801 : Nat.Prime 79952801 := by
  apply lucas_primality 79952801 (6 : ZMod 79952801)
  · rw [← oneHundredFiftyERFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (5, 2), (139, 1), (719, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (5, 2), (139, 1), (719, 1)] : List FactorBlock).map factorBlockValue).prod) = 79952801 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyER_2
      · exact prime_oneHundredFiftyER_5
      · exact prime_oneHundredFiftyER_139
      · exact prime_oneHundredFiftyER_719
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 79952801) ^ 39976400 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (6 : ZMod 79952801) ^ 15990560 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (6 : ZMod 79952801) ^ 575200 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (6 : ZMod 79952801) ^ 111200 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyER_81182261 : Nat.Prime 81182261 := by
  apply lucas_primality 81182261 (2 : ZMod 81182261)
  · rw [← oneHundredFiftyERFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (4059113, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (4059113, 1)] : List FactorBlock).map factorBlockValue).prod) = 81182261 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyER_2
      · exact prime_oneHundredFiftyER_5
      · exact prime_oneHundredFiftyER_4059113
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 81182261) ^ 40591130 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 81182261) ^ 16236452 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 81182261) ^ 20 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyER_82829821 : Nat.Prime 82829821 := by
  apply lucas_primality 82829821 (2 : ZMod 82829821)
  · rw [← oneHundredFiftyERFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (601, 1), (2297, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (601, 1), (2297, 1)] : List FactorBlock).map factorBlockValue).prod) = 82829821 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyER_2
      · exact prime_oneHundredFiftyER_3
      · exact prime_oneHundredFiftyER_5
      · exact prime_oneHundredFiftyER_601
      · exact prime_oneHundredFiftyER_2297
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 82829821) ^ 41414910 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 82829821) ^ 27609940 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 82829821) ^ 16565964 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 82829821) ^ 137820 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 82829821) ^ 36060 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyER_89111779 : Nat.Prime 89111779 := by
  apply lucas_primality 89111779 (2 : ZMod 89111779)
  · rw [← oneHundredFiftyERFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (41, 1), (51749, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (41, 1), (51749, 1)] : List FactorBlock).map factorBlockValue).prod) = 89111779 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyER_2
      · exact prime_oneHundredFiftyER_3
      · exact prime_oneHundredFiftyER_7
      · exact prime_oneHundredFiftyER_41
      · exact prime_oneHundredFiftyER_51749
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 89111779) ^ 44555889 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 89111779) ^ 29703926 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 89111779) ^ 12730254 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 89111779) ^ 2173458 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 89111779) ^ 1722 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyER_90131191 : Nat.Prime 90131191 := by
  apply lucas_primality 90131191 (13 : ZMod 90131191)
  · rw [← oneHundredFiftyERFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (89, 1), (33757, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (89, 1), (33757, 1)] : List FactorBlock).map factorBlockValue).prod) = 90131191 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyER_2
      · exact prime_oneHundredFiftyER_3
      · exact prime_oneHundredFiftyER_5
      · exact prime_oneHundredFiftyER_89
      · exact prime_oneHundredFiftyER_33757
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 90131191) ^ 45065595 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (13 : ZMod 90131191) ^ 30043730 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (13 : ZMod 90131191) ^ 18026238 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (13 : ZMod 90131191) ^ 1012710 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (13 : ZMod 90131191) ^ 2670 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyER_96003997 : Nat.Prime 96003997 := by
  apply lucas_primality 96003997 (5 : ZMod 96003997)
  · rw [← oneHundredFiftyERFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (11, 1), (61, 1), (11923, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (11, 1), (61, 1), (11923, 1)] : List FactorBlock).map factorBlockValue).prod) = 96003997 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyER_2
      · exact prime_oneHundredFiftyER_3
      · exact prime_oneHundredFiftyER_11
      · exact prime_oneHundredFiftyER_61
      · exact prime_oneHundredFiftyER_11923
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 96003997) ^ 48001998 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (5 : ZMod 96003997) ^ 32001332 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (5 : ZMod 96003997) ^ 8727636 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (5 : ZMod 96003997) ^ 1573836 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (5 : ZMod 96003997) ^ 8052 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyER_97346663 : Nat.Prime 97346663 := by
  apply lucas_primality 97346663 (5 : ZMod 97346663)
  · rw [← oneHundredFiftyERFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (6953333, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (6953333, 1)] : List FactorBlock).map factorBlockValue).prod) = 97346663 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyER_2
      · exact prime_oneHundredFiftyER_7
      · exact prime_oneHundredFiftyER_6953333
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 97346663) ^ 48673331 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (5 : ZMod 97346663) ^ 13906666 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (5 : ZMod 97346663) ^ 14 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyER_102406289 : Nat.Prime 102406289 := by
  apply lucas_primality 102406289 (3 : ZMod 102406289)
  · rw [← oneHundredFiftyERFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (683, 1), (9371, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (683, 1), (9371, 1)] : List FactorBlock).map factorBlockValue).prod) = 102406289 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyER_2
      · exact prime_oneHundredFiftyER_683
      · exact prime_oneHundredFiftyER_9371
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 102406289) ^ 51203144 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (3 : ZMod 102406289) ^ 149936 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (3 : ZMod 102406289) ^ 10928 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyER_110796689 : Nat.Prime 110796689 := by
  apply lucas_primality 110796689 (3 : ZMod 110796689)
  · rw [← oneHundredFiftyERFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (103, 1), (67231, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (103, 1), (67231, 1)] : List FactorBlock).map factorBlockValue).prod) = 110796689 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyER_2
      · exact prime_oneHundredFiftyER_103
      · exact prime_oneHundredFiftyER_67231
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 110796689) ^ 55398344 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (3 : ZMod 110796689) ^ 1075696 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (3 : ZMod 110796689) ^ 1648 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyER_122658787 : Nat.Prime 122658787 := by
  apply lucas_primality 122658787 (3 : ZMod 122658787)
  · rw [← oneHundredFiftyERFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 4), (103, 1), (7351, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 4), (103, 1), (7351, 1)] : List FactorBlock).map factorBlockValue).prod) = 122658787 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyER_2
      · exact prime_oneHundredFiftyER_3
      · exact prime_oneHundredFiftyER_103
      · exact prime_oneHundredFiftyER_7351
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 122658787) ^ 61329393 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (3 : ZMod 122658787) ^ 40886262 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (3 : ZMod 122658787) ^ 1190862 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (3 : ZMod 122658787) ^ 16686 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyER_152138407 : Nat.Prime 152138407 := by
  apply lucas_primality 152138407 (3 : ZMod 152138407)
  · rw [← oneHundredFiftyERFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (17, 1), (213079, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (17, 1), (213079, 1)] : List FactorBlock).map factorBlockValue).prod) = 152138407 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyER_2
      · exact prime_oneHundredFiftyER_3
      · exact prime_oneHundredFiftyER_7
      · exact prime_oneHundredFiftyER_17
      · exact prime_oneHundredFiftyER_213079
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 152138407) ^ 76069203 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (3 : ZMod 152138407) ^ 50712802 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (3 : ZMod 152138407) ^ 21734058 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (3 : ZMod 152138407) ^ 8949318 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (3 : ZMod 152138407) ^ 714 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyER_154727593 : Nat.Prime 154727593 := by
  apply lucas_primality 154727593 (5 : ZMod 154727593)
  · rw [← oneHundredFiftyERFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (281, 1), (22943, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (281, 1), (22943, 1)] : List FactorBlock).map factorBlockValue).prod) = 154727593 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyER_2
      · exact prime_oneHundredFiftyER_3
      · exact prime_oneHundredFiftyER_281
      · exact prime_oneHundredFiftyER_22943
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 154727593) ^ 77363796 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (5 : ZMod 154727593) ^ 51575864 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (5 : ZMod 154727593) ^ 550632 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (5 : ZMod 154727593) ^ 6744 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyER_157668683 : Nat.Prime 157668683 := by
  apply lucas_primality 157668683 (2 : ZMod 157668683)
  · rw [← oneHundredFiftyERFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (409, 1), (192749, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (409, 1), (192749, 1)] : List FactorBlock).map factorBlockValue).prod) = 157668683 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyER_2
      · exact prime_oneHundredFiftyER_409
      · exact prime_oneHundredFiftyER_192749
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 157668683) ^ 78834341 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 157668683) ^ 385498 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 157668683) ^ 818 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyER_159935459 : Nat.Prime 159935459 := by
  apply lucas_primality 159935459 (2 : ZMod 159935459)
  · rw [← oneHundredFiftyERFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (2657, 1), (30097, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (2657, 1), (30097, 1)] : List FactorBlock).map factorBlockValue).prod) = 159935459 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyER_2
      · exact prime_oneHundredFiftyER_2657
      · exact prime_oneHundredFiftyER_30097
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 159935459) ^ 79967729 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 159935459) ^ 60194 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 159935459) ^ 5314 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyER_165224009 : Nat.Prime 165224009 := by
  apply lucas_primality 165224009 (3 : ZMod 165224009)
  · rw [← oneHundredFiftyERFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (20653001, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (20653001, 1)] : List FactorBlock).map factorBlockValue).prod) = 165224009 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredFiftyER_2
      · exact prime_oneHundredFiftyER_20653001
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 165224009) ^ 82612004 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (3 : ZMod 165224009) ^ 8 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyER_171509881 : Nat.Prime 171509881 := by
  apply lucas_primality 171509881 (41 : ZMod 171509881)
  · rw [← oneHundredFiftyERFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 1), (1429249, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 1), (1429249, 1)] : List FactorBlock).map factorBlockValue).prod) = 171509881 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyER_2
      · exact prime_oneHundredFiftyER_3
      · exact prime_oneHundredFiftyER_5
      · exact prime_oneHundredFiftyER_1429249
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (41 : ZMod 171509881) ^ 85754940 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (41 : ZMod 171509881) ^ 57169960 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (41 : ZMod 171509881) ^ 34301976 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (41 : ZMod 171509881) ^ 120 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyER_178427983 : Nat.Prime 178427983 := by
  apply lucas_primality 178427983 (3 : ZMod 178427983)
  · rw [← oneHundredFiftyERFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (41, 1), (725317, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (41, 1), (725317, 1)] : List FactorBlock).map factorBlockValue).prod) = 178427983 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyER_2
      · exact prime_oneHundredFiftyER_3
      · exact prime_oneHundredFiftyER_41
      · exact prime_oneHundredFiftyER_725317
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 178427983) ^ 89213991 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (3 : ZMod 178427983) ^ 59475994 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (3 : ZMod 178427983) ^ 4351902 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (3 : ZMod 178427983) ^ 246 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyER_184175687 : Nat.Prime 184175687 := by
  apply lucas_primality 184175687 (5 : ZMod 184175687)
  · rw [← oneHundredFiftyERFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5689, 1), (16187, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5689, 1), (16187, 1)] : List FactorBlock).map factorBlockValue).prod) = 184175687 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyER_2
      · exact prime_oneHundredFiftyER_5689
      · exact prime_oneHundredFiftyER_16187
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 184175687) ^ 92087843 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (5 : ZMod 184175687) ^ 32374 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (5 : ZMod 184175687) ^ 11378 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyER_204812579 : Nat.Prime 204812579 := by
  apply lucas_primality 204812579 (2 : ZMod 204812579)
  · rw [← oneHundredFiftyERFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (102406289, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (102406289, 1)] : List FactorBlock).map factorBlockValue).prod) = 204812579 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredFiftyER_2
      · exact prime_oneHundredFiftyER_102406289
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 204812579) ^ 102406289 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 204812579) ^ 2 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyER_228486491 : Nat.Prime 228486491 := by
  apply lucas_primality 228486491 (2 : ZMod 228486491)
  · rw [← oneHundredFiftyERFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (1039, 1), (21991, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (1039, 1), (21991, 1)] : List FactorBlock).map factorBlockValue).prod) = 228486491 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyER_2
      · exact prime_oneHundredFiftyER_5
      · exact prime_oneHundredFiftyER_1039
      · exact prime_oneHundredFiftyER_21991
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 228486491) ^ 114243245 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 228486491) ^ 45697298 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 228486491) ^ 219910 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 228486491) ^ 10390 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyER_231295423 : Nat.Prime 231295423 := by
  apply lucas_primality 231295423 (3 : ZMod 231295423)
  · rw [← oneHundredFiftyERFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (71, 1), (542947, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (71, 1), (542947, 1)] : List FactorBlock).map factorBlockValue).prod) = 231295423 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyER_2
      · exact prime_oneHundredFiftyER_3
      · exact prime_oneHundredFiftyER_71
      · exact prime_oneHundredFiftyER_542947
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 231295423) ^ 115647711 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (3 : ZMod 231295423) ^ 77098474 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (3 : ZMod 231295423) ^ 3257682 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (3 : ZMod 231295423) ^ 426 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyER_248048113 : Nat.Prime 248048113 := by
  apply lucas_primality 248048113 (7 : ZMod 248048113)
  · rw [← oneHundredFiftyERFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (13, 1), (31, 1), (12823, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (13, 1), (31, 1), (12823, 1)] : List FactorBlock).map factorBlockValue).prod) = 248048113 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyER_2
      · exact prime_oneHundredFiftyER_3
      · exact prime_oneHundredFiftyER_13
      · exact prime_oneHundredFiftyER_31
      · exact prime_oneHundredFiftyER_12823
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 248048113) ^ 124024056 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (7 : ZMod 248048113) ^ 82682704 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (7 : ZMod 248048113) ^ 19080624 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (7 : ZMod 248048113) ^ 8001552 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (7 : ZMod 248048113) ^ 19344 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyER_267097681 : Nat.Prime 267097681 := by
  apply lucas_primality 267097681 (13 : ZMod 267097681)
  · rw [← oneHundredFiftyERFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 2), (5, 1), (107, 1), (3467, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 2), (5, 1), (107, 1), (3467, 1)] : List FactorBlock).map factorBlockValue).prod) = 267097681 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyER_2
      · exact prime_oneHundredFiftyER_3
      · exact prime_oneHundredFiftyER_5
      · exact prime_oneHundredFiftyER_107
      · exact prime_oneHundredFiftyER_3467
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 267097681) ^ 133548840 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (13 : ZMod 267097681) ^ 89032560 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (13 : ZMod 267097681) ^ 53419536 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (13 : ZMod 267097681) ^ 2496240 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (13 : ZMod 267097681) ^ 77040 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyER_296585903 : Nat.Prime 296585903 := by
  apply lucas_primality 296585903 (5 : ZMod 296585903)
  · rw [← oneHundredFiftyERFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (113, 1), (503, 1), (2609, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (113, 1), (503, 1), (2609, 1)] : List FactorBlock).map factorBlockValue).prod) = 296585903 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyER_2
      · exact prime_oneHundredFiftyER_113
      · exact prime_oneHundredFiftyER_503
      · exact prime_oneHundredFiftyER_2609
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 296585903) ^ 148292951 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (5 : ZMod 296585903) ^ 2624654 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (5 : ZMod 296585903) ^ 589634 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (5 : ZMod 296585903) ^ 113678 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyER_335860201 : Nat.Prime 335860201 := by
  apply lucas_primality 335860201 (21 : ZMod 335860201)
  · rw [← oneHundredFiftyERFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (5, 2), (13, 1), (31, 1), (463, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (5, 2), (13, 1), (31, 1), (463, 1)] : List FactorBlock).map factorBlockValue).prod) = 335860201 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyER_2
      · exact prime_oneHundredFiftyER_3
      · exact prime_oneHundredFiftyER_5
      · exact prime_oneHundredFiftyER_13
      · exact prime_oneHundredFiftyER_31
      · exact prime_oneHundredFiftyER_463
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (21 : ZMod 335860201) ^ 167930100 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (21 : ZMod 335860201) ^ 111953400 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (21 : ZMod 335860201) ^ 67172040 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (21 : ZMod 335860201) ^ 25835400 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (21 : ZMod 335860201) ^ 10834200 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (21 : ZMod 335860201) ^ 725400 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyER_343676093 : Nat.Prime 343676093 := by
  apply lucas_primality 343676093 (2 : ZMod 343676093)
  · rw [← oneHundredFiftyERFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (1019, 1), (84317, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (1019, 1), (84317, 1)] : List FactorBlock).map factorBlockValue).prod) = 343676093 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyER_2
      · exact prime_oneHundredFiftyER_1019
      · exact prime_oneHundredFiftyER_84317
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 343676093) ^ 171838046 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 343676093) ^ 337268 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 343676093) ^ 4076 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyER_362051087 : Nat.Prime 362051087 := by
  apply lucas_primality 362051087 (5 : ZMod 362051087)
  · rw [← oneHundredFiftyERFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (12539, 1), (14437, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (12539, 1), (14437, 1)] : List FactorBlock).map factorBlockValue).prod) = 362051087 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyER_2
      · exact prime_oneHundredFiftyER_12539
      · exact prime_oneHundredFiftyER_14437
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 362051087) ^ 181025543 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (5 : ZMod 362051087) ^ 28874 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (5 : ZMod 362051087) ^ 25078 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyER_426966413 : Nat.Prime 426966413 := by
  apply lucas_primality 426966413 (2 : ZMod 426966413)
  · rw [← oneHundredFiftyERFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (421, 1), (253543, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (421, 1), (253543, 1)] : List FactorBlock).map factorBlockValue).prod) = 426966413 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyER_2
      · exact prime_oneHundredFiftyER_421
      · exact prime_oneHundredFiftyER_253543
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 426966413) ^ 213483206 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 426966413) ^ 1014172 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 426966413) ^ 1684 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyER_446511433 : Nat.Prime 446511433 := by
  apply lucas_primality 446511433 (10 : ZMod 446511433)
  · rw [← oneHundredFiftyERFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (53, 1), (351031, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (53, 1), (351031, 1)] : List FactorBlock).map factorBlockValue).prod) = 446511433 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyER_2
      · exact prime_oneHundredFiftyER_3
      · exact prime_oneHundredFiftyER_53
      · exact prime_oneHundredFiftyER_351031
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (10 : ZMod 446511433) ^ 223255716 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (10 : ZMod 446511433) ^ 148837144 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (10 : ZMod 446511433) ^ 8424744 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (10 : ZMod 446511433) ^ 1272 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyER_462579641 : Nat.Prime 462579641 := by
  apply lucas_primality 462579641 (6 : ZMod 462579641)
  · rw [← oneHundredFiftyERFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (47, 1), (197, 1), (1249, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (47, 1), (197, 1), (1249, 1)] : List FactorBlock).map factorBlockValue).prod) = 462579641 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyER_2
      · exact prime_oneHundredFiftyER_5
      · exact prime_oneHundredFiftyER_47
      · exact prime_oneHundredFiftyER_197
      · exact prime_oneHundredFiftyER_1249
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 462579641) ^ 231289820 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (6 : ZMod 462579641) ^ 92515928 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (6 : ZMod 462579641) ^ 9842120 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (6 : ZMod 462579641) ^ 2348120 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (6 : ZMod 462579641) ^ 370360 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyER_466587599 : Nat.Prime 466587599 := by
  apply lucas_primality 466587599 (14 : ZMod 466587599)
  · rw [← oneHundredFiftyERFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (19, 1), (67, 1), (183263, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (19, 1), (67, 1), (183263, 1)] : List FactorBlock).map factorBlockValue).prod) = 466587599 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyER_2
      · exact prime_oneHundredFiftyER_19
      · exact prime_oneHundredFiftyER_67
      · exact prime_oneHundredFiftyER_183263
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (14 : ZMod 466587599) ^ 233293799 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (14 : ZMod 466587599) ^ 24557242 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (14 : ZMod 466587599) ^ 6963994 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (14 : ZMod 466587599) ^ 2546 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyER_487066871 : Nat.Prime 487066871 := by
  apply lucas_primality 487066871 (7 : ZMod 487066871)
  · rw [← oneHundredFiftyERFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (1907, 1), (25541, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (1907, 1), (25541, 1)] : List FactorBlock).map factorBlockValue).prod) = 487066871 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyER_2
      · exact prime_oneHundredFiftyER_5
      · exact prime_oneHundredFiftyER_1907
      · exact prime_oneHundredFiftyER_25541
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 487066871) ^ 243533435 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (7 : ZMod 487066871) ^ 97413374 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (7 : ZMod 487066871) ^ 255410 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (7 : ZMod 487066871) ^ 19070 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyER_492432713 : Nat.Prime 492432713 := by
  apply lucas_primality 492432713 (3 : ZMod 492432713)
  · rw [← oneHundredFiftyERFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (71, 1), (811, 1), (1069, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (71, 1), (811, 1), (1069, 1)] : List FactorBlock).map factorBlockValue).prod) = 492432713 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyER_2
      · exact prime_oneHundredFiftyER_71
      · exact prime_oneHundredFiftyER_811
      · exact prime_oneHundredFiftyER_1069
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 492432713) ^ 246216356 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (3 : ZMod 492432713) ^ 6935672 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (3 : ZMod 492432713) ^ 607192 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (3 : ZMod 492432713) ^ 460648 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyER_593171807 : Nat.Prime 593171807 := by
  apply lucas_primality 593171807 (5 : ZMod 593171807)
  · rw [← oneHundredFiftyERFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (296585903, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (296585903, 1)] : List FactorBlock).map factorBlockValue).prod) = 593171807 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredFiftyER_2
      · exact prime_oneHundredFiftyER_296585903
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 593171807) ^ 296585903 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (5 : ZMod 593171807) ^ 2 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyER_640433267 : Nat.Prime 640433267 := by
  apply lucas_primality 640433267 (2 : ZMod 640433267)
  · rw [← oneHundredFiftyERFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (19, 1), (61, 1), (25117, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (19, 1), (61, 1), (25117, 1)] : List FactorBlock).map factorBlockValue).prod) = 640433267 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyER_2
      · exact prime_oneHundredFiftyER_11
      · exact prime_oneHundredFiftyER_19
      · exact prime_oneHundredFiftyER_61
      · exact prime_oneHundredFiftyER_25117
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 640433267) ^ 320216633 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 640433267) ^ 58221206 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 640433267) ^ 33707014 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 640433267) ^ 10498906 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 640433267) ^ 25498 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyER_642820147 : Nat.Prime 642820147 := by
  apply lucas_primality 642820147 (2 : ZMod 642820147)
  · rw [← oneHundredFiftyERFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (23, 1), (53, 1), (179, 1), (491, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (23, 1), (53, 1), (179, 1), (491, 1)] : List FactorBlock).map factorBlockValue).prod) = 642820147 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyER_2
      · exact prime_oneHundredFiftyER_3
      · exact prime_oneHundredFiftyER_23
      · exact prime_oneHundredFiftyER_53
      · exact prime_oneHundredFiftyER_179
      · exact prime_oneHundredFiftyER_491
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 642820147) ^ 321410073 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 642820147) ^ 214273382 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 642820147) ^ 27948702 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 642820147) ^ 12128682 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 642820147) ^ 3591174 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 642820147) ^ 1309206 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyER_643509151 : Nat.Prime 643509151 := by
  apply lucas_primality 643509151 (33 : ZMod 643509151)
  · rw [← oneHundredFiftyERFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 2), (151, 1), (28411, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 2), (151, 1), (28411, 1)] : List FactorBlock).map factorBlockValue).prod) = 643509151 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyER_2
      · exact prime_oneHundredFiftyER_3
      · exact prime_oneHundredFiftyER_5
      · exact prime_oneHundredFiftyER_151
      · exact prime_oneHundredFiftyER_28411
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (33 : ZMod 643509151) ^ 321754575 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (33 : ZMod 643509151) ^ 214503050 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (33 : ZMod 643509151) ^ 128701830 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (33 : ZMod 643509151) ^ 4261650 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (33 : ZMod 643509151) ^ 22650 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyER_654507199 : Nat.Prime 654507199 := by
  apply lucas_primality 654507199 (3 : ZMod 654507199)
  · rw [← oneHundredFiftyERFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (3917, 1), (9283, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (3917, 1), (9283, 1)] : List FactorBlock).map factorBlockValue).prod) = 654507199 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyER_2
      · exact prime_oneHundredFiftyER_3
      · exact prime_oneHundredFiftyER_3917
      · exact prime_oneHundredFiftyER_9283
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 654507199) ^ 327253599 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (3 : ZMod 654507199) ^ 218169066 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (3 : ZMod 654507199) ^ 167094 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (3 : ZMod 654507199) ^ 70506 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyER_711291017 : Nat.Prime 711291017 := by
  apply lucas_primality 711291017 (5 : ZMod 711291017)
  · rw [← oneHundredFiftyERFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (17, 1), (2017, 1), (2593, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (17, 1), (2017, 1), (2593, 1)] : List FactorBlock).map factorBlockValue).prod) = 711291017 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyER_2
      · exact prime_oneHundredFiftyER_17
      · exact prime_oneHundredFiftyER_2017
      · exact prime_oneHundredFiftyER_2593
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 711291017) ^ 355645508 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (5 : ZMod 711291017) ^ 41840648 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (5 : ZMod 711291017) ^ 352648 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (5 : ZMod 711291017) ^ 274312 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyER_714027719 : Nat.Prime 714027719 := by
  apply lucas_primality 714027719 (11 : ZMod 714027719)
  · rw [← oneHundredFiftyERFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17203, 1), (20753, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17203, 1), (20753, 1)] : List FactorBlock).map factorBlockValue).prod) = 714027719 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyER_2
      · exact prime_oneHundredFiftyER_17203
      · exact prime_oneHundredFiftyER_20753
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (11 : ZMod 714027719) ^ 357013859 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (11 : ZMod 714027719) ^ 41506 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (11 : ZMod 714027719) ^ 34406 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyER_765941959 : Nat.Prime 765941959 := by
  apply lucas_primality 765941959 (3 : ZMod 765941959)
  · rw [← oneHundredFiftyERFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (37, 1), (1150063, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (37, 1), (1150063, 1)] : List FactorBlock).map factorBlockValue).prod) = 765941959 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyER_2
      · exact prime_oneHundredFiftyER_3
      · exact prime_oneHundredFiftyER_37
      · exact prime_oneHundredFiftyER_1150063
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 765941959) ^ 382970979 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (3 : ZMod 765941959) ^ 255313986 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (3 : ZMod 765941959) ^ 20701134 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (3 : ZMod 765941959) ^ 666 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyER_905401751 : Nat.Prime 905401751 := by
  apply lucas_primality 905401751 (7 : ZMod 905401751)
  · rw [← oneHundredFiftyERFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 3), (11, 1), (29, 1), (11353, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 3), (11, 1), (29, 1), (11353, 1)] : List FactorBlock).map factorBlockValue).prod) = 905401751 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyER_2
      · exact prime_oneHundredFiftyER_5
      · exact prime_oneHundredFiftyER_11
      · exact prime_oneHundredFiftyER_29
      · exact prime_oneHundredFiftyER_11353
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 905401751) ^ 452700875 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (7 : ZMod 905401751) ^ 181080350 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (7 : ZMod 905401751) ^ 82309250 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (7 : ZMod 905401751) ^ 31220750 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (7 : ZMod 905401751) ^ 79750 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyER_905681131 : Nat.Prime 905681131 := by
  apply lucas_primality 905681131 (3 : ZMod 905681131)
  · rw [← oneHundredFiftyERFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (30189371, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (30189371, 1)] : List FactorBlock).map factorBlockValue).prod) = 905681131 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyER_2
      · exact prime_oneHundredFiftyER_3
      · exact prime_oneHundredFiftyER_5
      · exact prime_oneHundredFiftyER_30189371
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 905681131) ^ 452840565 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (3 : ZMod 905681131) ^ 301893710 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (3 : ZMod 905681131) ^ 181136226 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (3 : ZMod 905681131) ^ 30 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyER_1239011701 : Nat.Prime 1239011701 := by
  apply lucas_primality 1239011701 (2 : ZMod 1239011701)
  · rw [← oneHundredFiftyERFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 2), (4130039, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 2), (4130039, 1)] : List FactorBlock).map factorBlockValue).prod) = 1239011701 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyER_2
      · exact prime_oneHundredFiftyER_3
      · exact prime_oneHundredFiftyER_5
      · exact prime_oneHundredFiftyER_4130039
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1239011701) ^ 619505850 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 1239011701) ^ 413003900 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 1239011701) ^ 247802340 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 1239011701) ^ 300 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyER_1279484057 : Nat.Prime 1279484057 := by
  apply lucas_primality 1279484057 (3 : ZMod 1279484057)
  · rw [← oneHundredFiftyERFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (17, 1), (9407971, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (17, 1), (9407971, 1)] : List FactorBlock).map factorBlockValue).prod) = 1279484057 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyER_2
      · exact prime_oneHundredFiftyER_17
      · exact prime_oneHundredFiftyER_9407971
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 1279484057) ^ 639742028 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (3 : ZMod 1279484057) ^ 75263768 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (3 : ZMod 1279484057) ^ 136 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyER_1603768073 : Nat.Prime 1603768073 := by
  apply lucas_primality 1603768073 (3 : ZMod 1603768073)
  · rw [← oneHundredFiftyERFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (383, 1), (647, 1), (809, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (383, 1), (647, 1), (809, 1)] : List FactorBlock).map factorBlockValue).prod) = 1603768073 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyER_2
      · exact prime_oneHundredFiftyER_383
      · exact prime_oneHundredFiftyER_647
      · exact prime_oneHundredFiftyER_809
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1603768073) ^ 801884036 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (3 : ZMod 1603768073) ^ 4187384 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (3 : ZMod 1603768073) ^ 2478776 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (3 : ZMod 1603768073) ^ 1982408 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyER_1606937041 : Nat.Prime 1606937041 := by
  apply lucas_primality 1606937041 (11 : ZMod 1606937041)
  · rw [← oneHundredFiftyERFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 2), (5, 1), (2231857, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 2), (5, 1), (2231857, 1)] : List FactorBlock).map factorBlockValue).prod) = 1606937041 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyER_2
      · exact prime_oneHundredFiftyER_3
      · exact prime_oneHundredFiftyER_5
      · exact prime_oneHundredFiftyER_2231857
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 1606937041) ^ 803468520 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (11 : ZMod 1606937041) ^ 535645680 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (11 : ZMod 1606937041) ^ 321387408 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (11 : ZMod 1606937041) ^ 720 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyER_1715098811 : Nat.Prime 1715098811 := by
  apply lucas_primality 1715098811 (6 : ZMod 1715098811)
  · rw [← oneHundredFiftyERFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (171509881, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (171509881, 1)] : List FactorBlock).map factorBlockValue).prod) = 1715098811 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyER_2
      · exact prime_oneHundredFiftyER_5
      · exact prime_oneHundredFiftyER_171509881
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (6 : ZMod 1715098811) ^ 857549405 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (6 : ZMod 1715098811) ^ 343019762 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (6 : ZMod 1715098811) ^ 10 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyER_1861975811 : Nat.Prime 1861975811 := by
  apply lucas_primality 1861975811 (2 : ZMod 1861975811)
  · rw [← oneHundredFiftyERFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (23, 1), (8095547, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (23, 1), (8095547, 1)] : List FactorBlock).map factorBlockValue).prod) = 1861975811 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyER_2
      · exact prime_oneHundredFiftyER_5
      · exact prime_oneHundredFiftyER_23
      · exact prime_oneHundredFiftyER_8095547
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1861975811) ^ 930987905 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 1861975811) ^ 372395162 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 1861975811) ^ 80955470 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 1861975811) ^ 230 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyER_1899290353 : Nat.Prime 1899290353 := by
  apply lucas_primality 1899290353 (5 : ZMod 1899290353)
  · rw [← oneHundredFiftyERFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (39568549, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (39568549, 1)] : List FactorBlock).map factorBlockValue).prod) = 1899290353 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyER_2
      · exact prime_oneHundredFiftyER_3
      · exact prime_oneHundredFiftyER_39568549
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 1899290353) ^ 949645176 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (5 : ZMod 1899290353) ^ 633096784 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (5 : ZMod 1899290353) ^ 48 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyER_2149724321 : Nat.Prime 2149724321 := by
  apply lucas_primality 2149724321 (3 : ZMod 2149724321)
  · rw [← oneHundredFiftyERFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (5, 1), (149, 1), (90173, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (5, 1), (149, 1), (90173, 1)] : List FactorBlock).map factorBlockValue).prod) = 2149724321 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyER_2
      · exact prime_oneHundredFiftyER_5
      · exact prime_oneHundredFiftyER_149
      · exact prime_oneHundredFiftyER_90173
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 2149724321) ^ 1074862160 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (3 : ZMod 2149724321) ^ 429944864 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (3 : ZMod 2149724321) ^ 14427680 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (3 : ZMod 2149724321) ^ 23840 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyER_2177774321 : Nat.Prime 2177774321 := by
  apply lucas_primality 2177774321 (3 : ZMod 2177774321)
  · rw [← oneHundredFiftyERFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (5, 1), (23, 1), (103, 1), (11491, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (5, 1), (23, 1), (103, 1), (11491, 1)] : List FactorBlock).map factorBlockValue).prod) = 2177774321 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyER_2
      · exact prime_oneHundredFiftyER_5
      · exact prime_oneHundredFiftyER_23
      · exact prime_oneHundredFiftyER_103
      · exact prime_oneHundredFiftyER_11491
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 2177774321) ^ 1088887160 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (3 : ZMod 2177774321) ^ 435554864 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (3 : ZMod 2177774321) ^ 94685840 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (3 : ZMod 2177774321) ^ 21143440 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (3 : ZMod 2177774321) ^ 189520 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyER_2342290187 : Nat.Prime 2342290187 := by
  apply lucas_primality 2342290187 (2 : ZMod 2342290187)
  · rw [← oneHundredFiftyERFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (2819, 1), (415447, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (2819, 1), (415447, 1)] : List FactorBlock).map factorBlockValue).prod) = 2342290187 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyER_2
      · exact prime_oneHundredFiftyER_2819
      · exact prime_oneHundredFiftyER_415447
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 2342290187) ^ 1171145093 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 2342290187) ^ 830894 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 2342290187) ^ 5638 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyER_2663500913 : Nat.Prime 2663500913 := by
  apply lucas_primality 2663500913 (3 : ZMod 2663500913)
  · rw [← oneHundredFiftyERFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (283, 1), (588229, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (283, 1), (588229, 1)] : List FactorBlock).map factorBlockValue).prod) = 2663500913 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyER_2
      · exact prime_oneHundredFiftyER_283
      · exact prime_oneHundredFiftyER_588229
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 2663500913) ^ 1331750456 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (3 : ZMod 2663500913) ^ 9411664 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (3 : ZMod 2663500913) ^ 4528 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyER_2720280181 : Nat.Prime 2720280181 := by
  apply lucas_primality 2720280181 (6 : ZMod 2720280181)
  · rw [← oneHundredFiftyERFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (83, 1), (546241, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (83, 1), (546241, 1)] : List FactorBlock).map factorBlockValue).prod) = 2720280181 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyER_2
      · exact prime_oneHundredFiftyER_3
      · exact prime_oneHundredFiftyER_5
      · exact prime_oneHundredFiftyER_83
      · exact prime_oneHundredFiftyER_546241
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 2720280181) ^ 1360140090 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (6 : ZMod 2720280181) ^ 906760060 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (6 : ZMod 2720280181) ^ 544056036 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (6 : ZMod 2720280181) ^ 32774460 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (6 : ZMod 2720280181) ^ 4980 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyER_3165480589 : Nat.Prime 3165480589 := by
  apply lucas_primality 3165480589 (6 : ZMod 3165480589)
  · rw [← oneHundredFiftyERFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (127, 1), (1249, 1), (1663, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (127, 1), (1249, 1), (1663, 1)] : List FactorBlock).map factorBlockValue).prod) = 3165480589 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyER_2
      · exact prime_oneHundredFiftyER_3
      · exact prime_oneHundredFiftyER_127
      · exact prime_oneHundredFiftyER_1249
      · exact prime_oneHundredFiftyER_1663
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 3165480589) ^ 1582740294 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (6 : ZMod 3165480589) ^ 1055160196 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (6 : ZMod 3165480589) ^ 24925044 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (6 : ZMod 3165480589) ^ 2534412 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (6 : ZMod 3165480589) ^ 1903476 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyER_3414362117 : Nat.Prime 3414362117 := by
  apply lucas_primality 3414362117 (2 : ZMod 3414362117)
  · rw [← oneHundredFiftyERFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (11, 1), (77599139, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (11, 1), (77599139, 1)] : List FactorBlock).map factorBlockValue).prod) = 3414362117 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyER_2
      · exact prime_oneHundredFiftyER_11
      · exact prime_oneHundredFiftyER_77599139
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 3414362117) ^ 1707181058 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 3414362117) ^ 310396556 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 3414362117) ^ 44 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyER_3566049547 : Nat.Prime 3566049547 := by
  apply lucas_primality 3566049547 (2 : ZMod 3566049547)
  · rw [← oneHundredFiftyERFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (1481, 1), (401311, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (1481, 1), (401311, 1)] : List FactorBlock).map factorBlockValue).prod) = 3566049547 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyER_2
      · exact prime_oneHundredFiftyER_3
      · exact prime_oneHundredFiftyER_1481
      · exact prime_oneHundredFiftyER_401311
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 3566049547) ^ 1783024773 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 3566049547) ^ 1188683182 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 3566049547) ^ 2407866 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 3566049547) ^ 8886 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyER_3782782589 : Nat.Prime 3782782589 := by
  apply lucas_primality 3782782589 (3 : ZMod 3782782589)
  · rw [← oneHundredFiftyERFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (13, 1), (71, 1), (1024589, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (13, 1), (71, 1), (1024589, 1)] : List FactorBlock).map factorBlockValue).prod) = 3782782589 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyER_2
      · exact prime_oneHundredFiftyER_13
      · exact prime_oneHundredFiftyER_71
      · exact prime_oneHundredFiftyER_1024589
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 3782782589) ^ 1891391294 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (3 : ZMod 3782782589) ^ 290983276 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (3 : ZMod 3782782589) ^ 53278628 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (3 : ZMod 3782782589) ^ 3692 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyER_4168160089 : Nat.Prime 4168160089 := by
  apply lucas_primality 4168160089 (19 : ZMod 4168160089)
  · rw [← oneHundredFiftyERFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (7043, 1), (24659, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (7043, 1), (24659, 1)] : List FactorBlock).map factorBlockValue).prod) = 4168160089 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyER_2
      · exact prime_oneHundredFiftyER_3
      · exact prime_oneHundredFiftyER_7043
      · exact prime_oneHundredFiftyER_24659
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (19 : ZMod 4168160089) ^ 2084080044 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (19 : ZMod 4168160089) ^ 1389386696 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (19 : ZMod 4168160089) ^ 591816 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (19 : ZMod 4168160089) ^ 169032 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyER_4171314503 : Nat.Prime 4171314503 := by
  apply lucas_primality 4171314503 (5 : ZMod 4171314503)
  · rw [← oneHundredFiftyERFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (43, 1), (48503657, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (43, 1), (48503657, 1)] : List FactorBlock).map factorBlockValue).prod) = 4171314503 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyER_2
      · exact prime_oneHundredFiftyER_43
      · exact prime_oneHundredFiftyER_48503657
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 4171314503) ^ 2085657251 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (5 : ZMod 4171314503) ^ 97007314 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (5 : ZMod 4171314503) ^ 86 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyER_4204343453 : Nat.Prime 4204343453 := by
  apply lucas_primality 4204343453 (3 : ZMod 4204343453)
  · rw [← oneHundredFiftyERFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (47, 1), (22363529, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (47, 1), (22363529, 1)] : List FactorBlock).map factorBlockValue).prod) = 4204343453 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyER_2
      · exact prime_oneHundredFiftyER_47
      · exact prime_oneHundredFiftyER_22363529
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 4204343453) ^ 2102171726 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (3 : ZMod 4204343453) ^ 89454116 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (3 : ZMod 4204343453) ^ 188 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyER_4212348149 : Nat.Prime 4212348149 := by
  apply lucas_primality 4212348149 (2 : ZMod 4212348149)
  · rw [← oneHundredFiftyERFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (557, 1), (1890641, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (557, 1), (1890641, 1)] : List FactorBlock).map factorBlockValue).prod) = 4212348149 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyER_2
      · exact prime_oneHundredFiftyER_557
      · exact prime_oneHundredFiftyER_1890641
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 4212348149) ^ 2106174074 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 4212348149) ^ 7562564 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 4212348149) ^ 2228 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyER_4264513499 : Nat.Prime 4264513499 := by
  apply lucas_primality 4264513499 (2 : ZMod 4264513499)
  · rw [← oneHundredFiftyERFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (89, 1), (3422563, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (89, 1), (3422563, 1)] : List FactorBlock).map factorBlockValue).prod) = 4264513499 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyER_2
      · exact prime_oneHundredFiftyER_7
      · exact prime_oneHundredFiftyER_89
      · exact prime_oneHundredFiftyER_3422563
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 4264513499) ^ 2132256749 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 4264513499) ^ 609216214 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 4264513499) ^ 47915882 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 4264513499) ^ 1246 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyER_4433223419 : Nat.Prime 4433223419 := by
  apply lucas_primality 4433223419 (2 : ZMod 4433223419)
  · rw [← oneHundredFiftyERFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (271, 1), (541, 1), (1163, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (271, 1), (541, 1), (1163, 1)] : List FactorBlock).map factorBlockValue).prod) = 4433223419 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyER_2
      · exact prime_oneHundredFiftyER_13
      · exact prime_oneHundredFiftyER_271
      · exact prime_oneHundredFiftyER_541
      · exact prime_oneHundredFiftyER_1163
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 4433223419) ^ 2216611709 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 4433223419) ^ 341017186 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 4433223419) ^ 16358758 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 4433223419) ^ 8194498 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 4433223419) ^ 3811886 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyER_5157765017 : Nat.Prime 5157765017 := by
  apply lucas_primality 5157765017 (3 : ZMod 5157765017)
  · rw [← oneHundredFiftyERFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (821, 1), (785287, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (821, 1), (785287, 1)] : List FactorBlock).map factorBlockValue).prod) = 5157765017 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyER_2
      · exact prime_oneHundredFiftyER_821
      · exact prime_oneHundredFiftyER_785287
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 5157765017) ^ 2578882508 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (3 : ZMod 5157765017) ^ 6282296 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (3 : ZMod 5157765017) ^ 6568 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyER_5192430209 : Nat.Prime 5192430209 := by
  apply lucas_primality 5192430209 (3 : ZMod 5192430209)
  · rw [← oneHundredFiftyERFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (7, 1), (5795123, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (7, 1), (5795123, 1)] : List FactorBlock).map factorBlockValue).prod) = 5192430209 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyER_2
      · exact prime_oneHundredFiftyER_7
      · exact prime_oneHundredFiftyER_5795123
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 5192430209) ^ 2596215104 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (3 : ZMod 5192430209) ^ 741775744 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (3 : ZMod 5192430209) ^ 896 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyER_6037638679 : Nat.Prime 6037638679 := by
  apply lucas_primality 6037638679 (3 : ZMod 6037638679)
  · rw [← oneHundredFiftyERFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (31, 1), (10820141, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (31, 1), (10820141, 1)] : List FactorBlock).map factorBlockValue).prod) = 6037638679 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyER_2
      · exact prime_oneHundredFiftyER_3
      · exact prime_oneHundredFiftyER_31
      · exact prime_oneHundredFiftyER_10820141
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 6037638679) ^ 3018819339 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (3 : ZMod 6037638679) ^ 2012546226 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (3 : ZMod 6037638679) ^ 194762538 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (3 : ZMod 6037638679) ^ 558 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyER_7369330403 : Nat.Prime 7369330403 := by
  apply lucas_primality 7369330403 (2 : ZMod 7369330403)
  · rw [← oneHundredFiftyERFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 2), (67, 1), (709, 1), (1583, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 2), (67, 1), (709, 1), (1583, 1)] : List FactorBlock).map factorBlockValue).prod) = 7369330403 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyER_2
      · exact prime_oneHundredFiftyER_7
      · exact prime_oneHundredFiftyER_67
      · exact prime_oneHundredFiftyER_709
      · exact prime_oneHundredFiftyER_1583
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 7369330403) ^ 3684665201 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 7369330403) ^ 1052761486 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 7369330403) ^ 109990006 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 7369330403) ^ 10393978 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 7369330403) ^ 4655294 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyER_7597751389 : Nat.Prime 7597751389 := by
  apply lucas_primality 7597751389 (2 : ZMod 7597751389)
  · rw [← oneHundredFiftyERFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (19, 1), (33323471, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (19, 1), (33323471, 1)] : List FactorBlock).map factorBlockValue).prod) = 7597751389 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyER_2
      · exact prime_oneHundredFiftyER_3
      · exact prime_oneHundredFiftyER_19
      · exact prime_oneHundredFiftyER_33323471
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 7597751389) ^ 3798875694 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 7597751389) ^ 2532583796 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 7597751389) ^ 399881652 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 7597751389) ^ 228 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyER_8866446839 : Nat.Prime 8866446839 := by
  apply lucas_primality 8866446839 (17 : ZMod 8866446839)
  · rw [← oneHundredFiftyERFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (4433223419, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (4433223419, 1)] : List FactorBlock).map factorBlockValue).prod) = 8866446839 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredFiftyER_2
      · exact prime_oneHundredFiftyER_4433223419
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (17 : ZMod 8866446839) ^ 4433223419 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (17 : ZMod 8866446839) ^ 2 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyER_10622806927 : Nat.Prime 10622806927 := by
  apply lucas_primality 10622806927 (6 : ZMod 10622806927)
  · rw [← oneHundredFiftyERFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (367, 1), (4824163, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (367, 1), (4824163, 1)] : List FactorBlock).map factorBlockValue).prod) = 10622806927 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyER_2
      · exact prime_oneHundredFiftyER_3
      · exact prime_oneHundredFiftyER_367
      · exact prime_oneHundredFiftyER_4824163
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 10622806927) ^ 5311403463 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (6 : ZMod 10622806927) ^ 3540935642 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (6 : ZMod 10622806927) ^ 28944978 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (6 : ZMod 10622806927) ^ 2202 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyER_10868173573 : Nat.Prime 10868173573 := by
  apply lucas_primality 10868173573 (2 : ZMod 10868173573)
  · rw [← oneHundredFiftyERFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (905681131, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (905681131, 1)] : List FactorBlock).map factorBlockValue).prod) = 10868173573 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyER_2
      · exact prime_oneHundredFiftyER_3
      · exact prime_oneHundredFiftyER_905681131
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 10868173573) ^ 5434086786 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 10868173573) ^ 3622724524 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 10868173573) ^ 12 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyER_11061581833 : Nat.Prime 11061581833 := by
  apply lucas_primality 11061581833 (5 : ZMod 11061581833)
  · rw [← oneHundredFiftyERFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 3), (7, 2), (1045123, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 3), (7, 2), (1045123, 1)] : List FactorBlock).map factorBlockValue).prod) = 11061581833 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyER_2
      · exact prime_oneHundredFiftyER_3
      · exact prime_oneHundredFiftyER_7
      · exact prime_oneHundredFiftyER_1045123
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 11061581833) ^ 5530790916 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (5 : ZMod 11061581833) ^ 3687193944 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (5 : ZMod 11061581833) ^ 1580225976 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (5 : ZMod 11061581833) ^ 10584 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyER_11075391241 : Nat.Prime 11075391241 := by
  apply lucas_primality 11075391241 (14 : ZMod 11075391241)
  · rw [← oneHundredFiftyERFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 1), (659, 1), (140053, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 1), (659, 1), (140053, 1)] : List FactorBlock).map factorBlockValue).prod) = 11075391241 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyER_2
      · exact prime_oneHundredFiftyER_3
      · exact prime_oneHundredFiftyER_5
      · exact prime_oneHundredFiftyER_659
      · exact prime_oneHundredFiftyER_140053
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (14 : ZMod 11075391241) ^ 5537695620 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (14 : ZMod 11075391241) ^ 3691797080 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (14 : ZMod 11075391241) ^ 2215078248 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (14 : ZMod 11075391241) ^ 16806360 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (14 : ZMod 11075391241) ^ 79080 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyER_12748193219 : Nat.Prime 12748193219 := by
  apply lucas_primality 12748193219 (2 : ZMod 12748193219)
  · rw [← oneHundredFiftyERFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (1697, 1), (3756097, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (1697, 1), (3756097, 1)] : List FactorBlock).map factorBlockValue).prod) = 12748193219 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyER_2
      · exact prime_oneHundredFiftyER_1697
      · exact prime_oneHundredFiftyER_3756097
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 12748193219) ^ 6374096609 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 12748193219) ^ 7512194 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 12748193219) ^ 3394 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyER_13587090151 : Nat.Prime 13587090151 := by
  apply lucas_primality 13587090151 (3 : ZMod 13587090151)
  · rw [← oneHundredFiftyERFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 2), (23, 1), (29, 1), (139, 1), (977, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 2), (23, 1), (29, 1), (139, 1), (977, 1)] : List FactorBlock).map factorBlockValue).prod) = 13587090151 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyER_2
      · exact prime_oneHundredFiftyER_3
      · exact prime_oneHundredFiftyER_5
      · exact prime_oneHundredFiftyER_23
      · exact prime_oneHundredFiftyER_29
      · exact prime_oneHundredFiftyER_139
      · exact prime_oneHundredFiftyER_977
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 13587090151) ^ 6793545075 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (3 : ZMod 13587090151) ^ 4529030050 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (3 : ZMod 13587090151) ^ 2717418030 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (3 : ZMod 13587090151) ^ 590743050 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (3 : ZMod 13587090151) ^ 468520350 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (3 : ZMod 13587090151) ^ 97748850 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (3 : ZMod 13587090151) ^ 13906950 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyER_16100632501 : Nat.Prime 16100632501 := by
  apply lucas_primality 16100632501 (2 : ZMod 16100632501)
  · rw [← oneHundredFiftyERFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 4), (23, 1), (93337, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 4), (23, 1), (93337, 1)] : List FactorBlock).map factorBlockValue).prod) = 16100632501 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyER_2
      · exact prime_oneHundredFiftyER_3
      · exact prime_oneHundredFiftyER_5
      · exact prime_oneHundredFiftyER_23
      · exact prime_oneHundredFiftyER_93337
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 16100632501) ^ 8050316250 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 16100632501) ^ 5366877500 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 16100632501) ^ 3220126500 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 16100632501) ^ 700027500 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 16100632501) ^ 172500 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyER_16937230103 : Nat.Prime 16937230103 := by
  apply lucas_primality 16937230103 (5 : ZMod 16937230103)
  · rw [← oneHundredFiftyERFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (1667, 1), (390781, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (1667, 1), (390781, 1)] : List FactorBlock).map factorBlockValue).prod) = 16937230103 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyER_2
      · exact prime_oneHundredFiftyER_13
      · exact prime_oneHundredFiftyER_1667
      · exact prime_oneHundredFiftyER_390781
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 16937230103) ^ 8468615051 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (5 : ZMod 16937230103) ^ 1302863854 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (5 : ZMod 16937230103) ^ 10160306 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (5 : ZMod 16937230103) ^ 43342 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyER_18239870917 : Nat.Prime 18239870917 := by
  apply lucas_primality 18239870917 (2 : ZMod 18239870917)
  · rw [← oneHundredFiftyERFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (22003, 1), (23027, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (22003, 1), (23027, 1)] : List FactorBlock).map factorBlockValue).prod) = 18239870917 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyER_2
      · exact prime_oneHundredFiftyER_3
      · exact prime_oneHundredFiftyER_22003
      · exact prime_oneHundredFiftyER_23027
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 18239870917) ^ 9119935458 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 18239870917) ^ 6079956972 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 18239870917) ^ 828972 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 18239870917) ^ 792108 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyER_23096547757 : Nat.Prime 23096547757 := by
  apply lucas_primality 23096547757 (5 : ZMod 23096547757)
  · rw [← oneHundredFiftyERFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (79, 1), (163, 1), (49823, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (79, 1), (163, 1), (49823, 1)] : List FactorBlock).map factorBlockValue).prod) = 23096547757 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyER_2
      · exact prime_oneHundredFiftyER_3
      · exact prime_oneHundredFiftyER_79
      · exact prime_oneHundredFiftyER_163
      · exact prime_oneHundredFiftyER_49823
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 23096547757) ^ 11548273878 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (5 : ZMod 23096547757) ^ 7698849252 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (5 : ZMod 23096547757) ^ 292361364 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (5 : ZMod 23096547757) ^ 141696612 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (5 : ZMod 23096547757) ^ 463572 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyER_25011911983 : Nat.Prime 25011911983 := by
  apply lucas_primality 25011911983 (3 : ZMod 25011911983)
  · rw [← oneHundredFiftyERFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (23, 1), (307, 1), (590377, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (23, 1), (307, 1), (590377, 1)] : List FactorBlock).map factorBlockValue).prod) = 25011911983 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyER_2
      · exact prime_oneHundredFiftyER_3
      · exact prime_oneHundredFiftyER_23
      · exact prime_oneHundredFiftyER_307
      · exact prime_oneHundredFiftyER_590377
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 25011911983) ^ 12505955991 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (3 : ZMod 25011911983) ^ 8337303994 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (3 : ZMod 25011911983) ^ 1087474434 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (3 : ZMod 25011911983) ^ 81472026 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (3 : ZMod 25011911983) ^ 42366 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyER_25232620319 : Nat.Prime 25232620319 := by
  apply lucas_primality 25232620319 (7 : ZMod 25232620319)
  · rw [← oneHundredFiftyERFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (1613, 1), (7821643, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (1613, 1), (7821643, 1)] : List FactorBlock).map factorBlockValue).prod) = 25232620319 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyER_2
      · exact prime_oneHundredFiftyER_1613
      · exact prime_oneHundredFiftyER_7821643
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 25232620319) ^ 12616310159 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (7 : ZMod 25232620319) ^ 15643286 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (7 : ZMod 25232620319) ^ 3226 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyER_30129387137 : Nat.Prime 30129387137 := by
  apply lucas_primality 30129387137 (3 : ZMod 30129387137)
  · rw [← oneHundredFiftyERFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (29, 1), (8116753, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (29, 1), (8116753, 1)] : List FactorBlock).map factorBlockValue).prod) = 30129387137 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyER_2
      · exact prime_oneHundredFiftyER_29
      · exact prime_oneHundredFiftyER_8116753
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 30129387137) ^ 15064693568 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (3 : ZMod 30129387137) ^ 1038944384 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (3 : ZMod 30129387137) ^ 3712 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyER_44997410291 : Nat.Prime 44997410291 := by
  apply lucas_primality 44997410291 (2 : ZMod 44997410291)
  · rw [← oneHundredFiftyERFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 1), (642820147, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 1), (642820147, 1)] : List FactorBlock).map factorBlockValue).prod) = 44997410291 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyER_2
      · exact prime_oneHundredFiftyER_5
      · exact prime_oneHundredFiftyER_7
      · exact prime_oneHundredFiftyER_642820147
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 44997410291) ^ 22498705145 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 44997410291) ^ 8999482058 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 44997410291) ^ 6428201470 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 44997410291) ^ 70 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyER_45988787941 : Nat.Prime 45988787941 := by
  apply lucas_primality 45988787941 (2 : ZMod 45988787941)
  · rw [← oneHundredFiftyERFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (17, 1), (53, 1), (67, 1), (12697, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (17, 1), (53, 1), (67, 1), (12697, 1)] : List FactorBlock).map factorBlockValue).prod) = 45988787941 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyER_2
      · exact prime_oneHundredFiftyER_3
      · exact prime_oneHundredFiftyER_5
      · exact prime_oneHundredFiftyER_17
      · exact prime_oneHundredFiftyER_53
      · exact prime_oneHundredFiftyER_67
      · exact prime_oneHundredFiftyER_12697
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 45988787941) ^ 22994393970 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 45988787941) ^ 15329595980 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 45988787941) ^ 9197757588 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 45988787941) ^ 2705222820 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 45988787941) ^ 867712980 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 45988787941) ^ 686399820 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 45988787941) ^ 3622020 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyER_47423310787 : Nat.Prime 47423310787 := by
  apply lucas_primality 47423310787 (2 : ZMod 47423310787)
  · rw [← oneHundredFiftyERFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (131, 1), (6703889, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (131, 1), (6703889, 1)] : List FactorBlock).map factorBlockValue).prod) = 47423310787 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyER_2
      · exact prime_oneHundredFiftyER_3
      · exact prime_oneHundredFiftyER_131
      · exact prime_oneHundredFiftyER_6703889
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 47423310787) ^ 23711655393 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 47423310787) ^ 15807770262 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 47423310787) ^ 362010006 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 47423310787) ^ 7074 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyER_47591935099 : Nat.Prime 47591935099 := by
  apply lucas_primality 47591935099 (2 : ZMod 47591935099)
  · rw [← oneHundredFiftyERFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (17, 1), (466587599, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (17, 1), (466587599, 1)] : List FactorBlock).map factorBlockValue).prod) = 47591935099 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyER_2
      · exact prime_oneHundredFiftyER_3
      · exact prime_oneHundredFiftyER_17
      · exact prime_oneHundredFiftyER_466587599
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 47591935099) ^ 23795967549 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 47591935099) ^ 15863978366 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 47591935099) ^ 2799525594 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 47591935099) ^ 102 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyER_53270018261 : Nat.Prime 53270018261 := by
  apply lucas_primality 53270018261 (2 : ZMod 53270018261)
  · rw [← oneHundredFiftyERFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (2663500913, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (2663500913, 1)] : List FactorBlock).map factorBlockValue).prod) = 53270018261 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyER_2
      · exact prime_oneHundredFiftyER_5
      · exact prime_oneHundredFiftyER_2663500913
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 53270018261) ^ 26635009130 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 53270018261) ^ 10654003652 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 53270018261) ^ 20 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyER_55723393783 : Nat.Prime 55723393783 := by
  apply lucas_primality 55723393783 (3 : ZMod 55723393783)
  · rw [← oneHundredFiftyERFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (7, 3), (307, 1), (29399, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (7, 3), (307, 1), (29399, 1)] : List FactorBlock).map factorBlockValue).prod) = 55723393783 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyER_2
      · exact prime_oneHundredFiftyER_3
      · exact prime_oneHundredFiftyER_7
      · exact prime_oneHundredFiftyER_307
      · exact prime_oneHundredFiftyER_29399
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 55723393783) ^ 27861696891 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (3 : ZMod 55723393783) ^ 18574464594 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (3 : ZMod 55723393783) ^ 7960484826 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (3 : ZMod 55723393783) ^ 181509426 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (3 : ZMod 55723393783) ^ 1895418 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyER_71149999567 : Nat.Prime 71149999567 := by
  apply lucas_primality 71149999567 (6 : ZMod 71149999567)
  · rw [← oneHundredFiftyERFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (23, 2), (47, 1), (53, 1), (8999, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (23, 2), (47, 1), (53, 1), (8999, 1)] : List FactorBlock).map factorBlockValue).prod) = 71149999567 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyER_2
      · exact prime_oneHundredFiftyER_3
      · exact prime_oneHundredFiftyER_23
      · exact prime_oneHundredFiftyER_47
      · exact prime_oneHundredFiftyER_53
      · exact prime_oneHundredFiftyER_8999
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 71149999567) ^ 35574999783 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (6 : ZMod 71149999567) ^ 23716666522 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (6 : ZMod 71149999567) ^ 3093478242 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (6 : ZMod 71149999567) ^ 1513829778 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (6 : ZMod 71149999567) ^ 1342452822 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (6 : ZMod 71149999567) ^ 7906434 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyER_71718628717 : Nat.Prime 71718628717 := by
  apply lucas_primality 71718628717 (2 : ZMod 71718628717)
  · rw [← oneHundredFiftyERFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (7, 5), (39511, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (7, 5), (39511, 1)] : List FactorBlock).map factorBlockValue).prod) = 71718628717 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyER_2
      · exact prime_oneHundredFiftyER_3
      · exact prime_oneHundredFiftyER_7
      · exact prime_oneHundredFiftyER_39511
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 71718628717) ^ 35859314358 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 71718628717) ^ 23906209572 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 71718628717) ^ 10245518388 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 71718628717) ^ 1815156 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyER_74775919583 : Nat.Prime 74775919583 := by
  apply lucas_primality 74775919583 (5 : ZMod 74775919583)
  · rw [← oneHundredFiftyERFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (13, 1), (43, 1), (9554807, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (13, 1), (43, 1), (9554807, 1)] : List FactorBlock).map factorBlockValue).prod) = 74775919583 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyER_2
      · exact prime_oneHundredFiftyER_7
      · exact prime_oneHundredFiftyER_13
      · exact prime_oneHundredFiftyER_43
      · exact prime_oneHundredFiftyER_9554807
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 74775919583) ^ 37387959791 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (5 : ZMod 74775919583) ^ 10682274226 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (5 : ZMod 74775919583) ^ 5751993814 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (5 : ZMod 74775919583) ^ 1738974874 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (5 : ZMod 74775919583) ^ 7826 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyER_87683238689 : Nat.Prime 87683238689 := by
  apply lucas_primality 87683238689 (3 : ZMod 87683238689)
  · rw [← oneHundredFiftyERFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (73, 1), (149, 1), (251917, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (73, 1), (149, 1), (251917, 1)] : List FactorBlock).map factorBlockValue).prod) = 87683238689 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyER_2
      · exact prime_oneHundredFiftyER_73
      · exact prime_oneHundredFiftyER_149
      · exact prime_oneHundredFiftyER_251917
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 87683238689) ^ 43841619344 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (3 : ZMod 87683238689) ^ 1201140256 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (3 : ZMod 87683238689) ^ 588478112 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (3 : ZMod 87683238689) ^ 348064 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyER_103060768229 : Nat.Prime 103060768229 := by
  apply lucas_primality 103060768229 (2 : ZMod 103060768229)
  · rw [← oneHundredFiftyERFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (11, 1), (2342290187, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (11, 1), (2342290187, 1)] : List FactorBlock).map factorBlockValue).prod) = 103060768229 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyER_2
      · exact prime_oneHundredFiftyER_11
      · exact prime_oneHundredFiftyER_2342290187
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 103060768229) ^ 51530384114 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 103060768229) ^ 9369160748 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 103060768229) ^ 44 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyER_106701766939 : Nat.Prime 106701766939 := by
  apply lucas_primality 106701766939 (10 : ZMod 106701766939)
  · rw [← oneHundredFiftyERFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (13, 2), (101, 1), (115763, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (13, 2), (101, 1), (115763, 1)] : List FactorBlock).map factorBlockValue).prod) = 106701766939 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyER_2
      · exact prime_oneHundredFiftyER_3
      · exact prime_oneHundredFiftyER_13
      · exact prime_oneHundredFiftyER_101
      · exact prime_oneHundredFiftyER_115763
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 106701766939) ^ 53350883469 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (10 : ZMod 106701766939) ^ 35567255646 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (10 : ZMod 106701766939) ^ 8207828226 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (10 : ZMod 106701766939) ^ 1056453138 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (10 : ZMod 106701766939) ^ 921726 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyER_107373267763 : Nat.Prime 107373267763 := by
  apply lucas_primality 107373267763 (2 : ZMod 107373267763)
  · rw [← oneHundredFiftyERFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (67, 1), (267097681, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (67, 1), (267097681, 1)] : List FactorBlock).map factorBlockValue).prod) = 107373267763 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyER_2
      · exact prime_oneHundredFiftyER_3
      · exact prime_oneHundredFiftyER_67
      · exact prime_oneHundredFiftyER_267097681
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 107373267763) ^ 53686633881 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 107373267763) ^ 35791089254 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 107373267763) ^ 1602586086 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 107373267763) ^ 402 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyER_120055286693 : Nat.Prime 120055286693 := by
  apply lucas_primality 120055286693 (2 : ZMod 120055286693)
  · rw [← oneHundredFiftyERFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (11, 2), (248048113, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (11, 2), (248048113, 1)] : List FactorBlock).map factorBlockValue).prod) = 120055286693 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyER_2
      · exact prime_oneHundredFiftyER_11
      · exact prime_oneHundredFiftyER_248048113
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 120055286693) ^ 60027643346 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 120055286693) ^ 10914116972 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 120055286693) ^ 484 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyER_123786360409 : Nat.Prime 123786360409 := by
  apply lucas_primality 123786360409 (11 : ZMod 123786360409)
  · rw [← oneHundredFiftyERFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5157765017, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5157765017, 1)] : List FactorBlock).map factorBlockValue).prod) = 123786360409 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyER_2
      · exact prime_oneHundredFiftyER_3
      · exact prime_oneHundredFiftyER_5157765017
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (11 : ZMod 123786360409) ^ 61893180204 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (11 : ZMod 123786360409) ^ 41262120136 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (11 : ZMod 123786360409) ^ 24 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyER_140168308879 : Nat.Prime 140168308879 := by
  apply lucas_primality 140168308879 (3 : ZMod 140168308879)
  · rw [← oneHundredFiftyERFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (13, 1), (853, 1), (702239, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (13, 1), (853, 1), (702239, 1)] : List FactorBlock).map factorBlockValue).prod) = 140168308879 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyER_2
      · exact prime_oneHundredFiftyER_3
      · exact prime_oneHundredFiftyER_13
      · exact prime_oneHundredFiftyER_853
      · exact prime_oneHundredFiftyER_702239
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 140168308879) ^ 70084154439 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (3 : ZMod 140168308879) ^ 46722769626 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (3 : ZMod 140168308879) ^ 10782177606 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (3 : ZMod 140168308879) ^ 164323926 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (3 : ZMod 140168308879) ^ 199602 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyER_175198156807 : Nat.Prime 175198156807 := by
  apply lucas_primality 175198156807 (5 : ZMod 175198156807)
  · rw [← oneHundredFiftyERFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (21221, 1), (1375981, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (21221, 1), (1375981, 1)] : List FactorBlock).map factorBlockValue).prod) = 175198156807 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyER_2
      · exact prime_oneHundredFiftyER_3
      · exact prime_oneHundredFiftyER_21221
      · exact prime_oneHundredFiftyER_1375981
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 175198156807) ^ 87599078403 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (5 : ZMod 175198156807) ^ 58399385602 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (5 : ZMod 175198156807) ^ 8255886 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (5 : ZMod 175198156807) ^ 127326 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyER_217774395623 : Nat.Prime 217774395623 := by
  apply lucas_primality 217774395623 (5 : ZMod 217774395623)
  · rw [← oneHundredFiftyERFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (17, 1), (29, 1), (1949, 1), (16189, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (17, 1), (29, 1), (1949, 1), (16189, 1)] : List FactorBlock).map factorBlockValue).prod) = 217774395623 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyER_2
      · exact prime_oneHundredFiftyER_7
      · exact prime_oneHundredFiftyER_17
      · exact prime_oneHundredFiftyER_29
      · exact prime_oneHundredFiftyER_1949
      · exact prime_oneHundredFiftyER_16189
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 217774395623) ^ 108887197811 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (5 : ZMod 217774395623) ^ 31110627946 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (5 : ZMod 217774395623) ^ 12810258566 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (5 : ZMod 217774395623) ^ 7509461918 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (5 : ZMod 217774395623) ^ 111736478 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (5 : ZMod 217774395623) ^ 13451998 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyER_222133410637 : Nat.Prime 222133410637 := by
  apply lucas_primality 222133410637 (5 : ZMod 222133410637)
  · rw [← oneHundredFiftyERFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (373, 1), (3449, 1), (14389, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (373, 1), (3449, 1), (14389, 1)] : List FactorBlock).map factorBlockValue).prod) = 222133410637 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyER_2
      · exact prime_oneHundredFiftyER_3
      · exact prime_oneHundredFiftyER_373
      · exact prime_oneHundredFiftyER_3449
      · exact prime_oneHundredFiftyER_14389
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 222133410637) ^ 111066705318 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (5 : ZMod 222133410637) ^ 74044470212 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (5 : ZMod 222133410637) ^ 595531932 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (5 : ZMod 222133410637) ^ 64405164 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (5 : ZMod 222133410637) ^ 15437724 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyER_243364641461 : Nat.Prime 243364641461 := by
  apply lucas_primality 243364641461 (2 : ZMod 243364641461)
  · rw [← oneHundredFiftyERFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (19, 1), (640433267, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (19, 1), (640433267, 1)] : List FactorBlock).map factorBlockValue).prod) = 243364641461 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyER_2
      · exact prime_oneHundredFiftyER_5
      · exact prime_oneHundredFiftyER_19
      · exact prime_oneHundredFiftyER_640433267
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 243364641461) ^ 121682320730 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 243364641461) ^ 48672928292 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 243364641461) ^ 12808665340 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 243364641461) ^ 380 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyER_259397143063 : Nat.Prime 259397143063 := by
  apply lucas_primality 259397143063 (3 : ZMod 259397143063)
  · rw [← oneHundredFiftyERFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (1151, 1), (37561127, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (1151, 1), (37561127, 1)] : List FactorBlock).map factorBlockValue).prod) = 259397143063 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyER_2
      · exact prime_oneHundredFiftyER_3
      · exact prime_oneHundredFiftyER_1151
      · exact prime_oneHundredFiftyER_37561127
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 259397143063) ^ 129698571531 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (3 : ZMod 259397143063) ^ 86465714354 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (3 : ZMod 259397143063) ^ 225366762 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (3 : ZMod 259397143063) ^ 6906 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyER_276887636227 : Nat.Prime 276887636227 := by
  apply lucas_primality 276887636227 (2 : ZMod 276887636227)
  · rw [← oneHundredFiftyERFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (107, 1), (181, 1), (264757, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (107, 1), (181, 1), (264757, 1)] : List FactorBlock).map factorBlockValue).prod) = 276887636227 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyER_2
      · exact prime_oneHundredFiftyER_3
      · exact prime_oneHundredFiftyER_107
      · exact prime_oneHundredFiftyER_181
      · exact prime_oneHundredFiftyER_264757
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 276887636227) ^ 138443818113 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 276887636227) ^ 92295878742 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 276887636227) ^ 2587734918 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 276887636227) ^ 1529765946 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 276887636227) ^ 1045818 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyER_284599998269 : Nat.Prime 284599998269 := by
  apply lucas_primality 284599998269 (2 : ZMod 284599998269)
  · rw [← oneHundredFiftyERFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (71149999567, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (71149999567, 1)] : List FactorBlock).map factorBlockValue).prod) = 284599998269 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredFiftyER_2
      · exact prime_oneHundredFiftyER_71149999567
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 284599998269) ^ 142299999134 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 284599998269) ^ 4 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyER_371214717911 : Nat.Prime 371214717911 := by
  apply lucas_primality 371214717911 (7 : ZMod 371214717911)
  · rw [← oneHundredFiftyERFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (41, 1), (905401751, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (41, 1), (905401751, 1)] : List FactorBlock).map factorBlockValue).prod) = 371214717911 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyER_2
      · exact prime_oneHundredFiftyER_5
      · exact prime_oneHundredFiftyER_41
      · exact prime_oneHundredFiftyER_905401751
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 371214717911) ^ 185607358955 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (7 : ZMod 371214717911) ^ 74242943582 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (7 : ZMod 371214717911) ^ 9054017510 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (7 : ZMod 371214717911) ^ 410 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyER_423182745173 : Nat.Prime 423182745173 := by
  apply lucas_primality 423182745173 (2 : ZMod 423182745173)
  · rw [← oneHundredFiftyERFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (11, 1), (61, 1), (157668683, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (11, 1), (61, 1), (157668683, 1)] : List FactorBlock).map factorBlockValue).prod) = 423182745173 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyER_2
      · exact prime_oneHundredFiftyER_11
      · exact prime_oneHundredFiftyER_61
      · exact prime_oneHundredFiftyER_157668683
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 423182745173) ^ 211591372586 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 423182745173) ^ 38471158652 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 423182745173) ^ 6937422052 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 423182745173) ^ 2684 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyER_435548791247 : Nat.Prime 435548791247 := by
  apply lucas_primality 435548791247 (5 : ZMod 435548791247)
  · rw [← oneHundredFiftyERFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (217774395623, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (217774395623, 1)] : List FactorBlock).map factorBlockValue).prod) = 435548791247 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredFiftyER_2
      · exact prime_oneHundredFiftyER_217774395623
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 435548791247) ^ 217774395623 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (5 : ZMod 435548791247) ^ 2 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyER_615051349459 : Nat.Prime 615051349459 := by
  apply lucas_primality 615051349459 (7 : ZMod 615051349459)
  · rw [← oneHundredFiftyERFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (13, 1), (419, 1), (2688467, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (13, 1), (419, 1), (2688467, 1)] : List FactorBlock).map factorBlockValue).prod) = 615051349459 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyER_2
      · exact prime_oneHundredFiftyER_3
      · exact prime_oneHundredFiftyER_7
      · exact prime_oneHundredFiftyER_13
      · exact prime_oneHundredFiftyER_419
      · exact prime_oneHundredFiftyER_2688467
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 615051349459) ^ 307525674729 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (7 : ZMod 615051349459) ^ 205017116486 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (7 : ZMod 615051349459) ^ 87864478494 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (7 : ZMod 615051349459) ^ 47311642266 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (7 : ZMod 615051349459) ^ 1467902982 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (7 : ZMod 615051349459) ^ 228774 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyER_659795388823 : Nat.Prime 659795388823 := by
  apply lucas_primality 659795388823 (6 : ZMod 659795388823)
  · rw [← oneHundredFiftyERFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (37, 1), (83, 1), (103, 1), (115883, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (37, 1), (83, 1), (103, 1), (115883, 1)] : List FactorBlock).map factorBlockValue).prod) = 659795388823 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyER_2
      · exact prime_oneHundredFiftyER_3
      · exact prime_oneHundredFiftyER_37
      · exact prime_oneHundredFiftyER_83
      · exact prime_oneHundredFiftyER_103
      · exact prime_oneHundredFiftyER_115883
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 659795388823) ^ 329897694411 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (6 : ZMod 659795388823) ^ 219931796274 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (6 : ZMod 659795388823) ^ 17832307806 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (6 : ZMod 659795388823) ^ 7949342034 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (6 : ZMod 659795388823) ^ 6405780474 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (6 : ZMod 659795388823) ^ 5693634 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyER_671678220533 : Nat.Prime 671678220533 := by
  apply lucas_primality 671678220533 (2 : ZMod 671678220533)
  · rw [← oneHundredFiftyERFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (11, 1), (31, 1), (492432713, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (11, 1), (31, 1), (492432713, 1)] : List FactorBlock).map factorBlockValue).prod) = 671678220533 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyER_2
      · exact prime_oneHundredFiftyER_11
      · exact prime_oneHundredFiftyER_31
      · exact prime_oneHundredFiftyER_492432713
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 671678220533) ^ 335839110266 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 671678220533) ^ 61061656412 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 671678220533) ^ 21667039372 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 671678220533) ^ 1364 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyER_738747629527 : Nat.Prime 738747629527 := by
  apply lucas_primality 738747629527 (5 : ZMod 738747629527)
  · rw [← oneHundredFiftyERFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (52457, 1), (2347153, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (52457, 1), (2347153, 1)] : List FactorBlock).map factorBlockValue).prod) = 738747629527 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyER_2
      · exact prime_oneHundredFiftyER_3
      · exact prime_oneHundredFiftyER_52457
      · exact prime_oneHundredFiftyER_2347153
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 738747629527) ^ 369373814763 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (5 : ZMod 738747629527) ^ 246249209842 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (5 : ZMod 738747629527) ^ 14082918 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (5 : ZMod 738747629527) ^ 314742 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyER_896134490989 : Nat.Prime 896134490989 := by
  apply lucas_primality 896134490989 (7 : ZMod 896134490989)
  · rw [← oneHundredFiftyERFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (11, 1), (173, 1), (2341, 1), (16763, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (11, 1), (173, 1), (2341, 1), (16763, 1)] : List FactorBlock).map factorBlockValue).prod) = 896134490989 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyER_2
      · exact prime_oneHundredFiftyER_3
      · exact prime_oneHundredFiftyER_11
      · exact prime_oneHundredFiftyER_173
      · exact prime_oneHundredFiftyER_2341
      · exact prime_oneHundredFiftyER_16763
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 896134490989) ^ 448067245494 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (7 : ZMod 896134490989) ^ 298711496996 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (7 : ZMod 896134490989) ^ 81466771908 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (7 : ZMod 896134490989) ^ 5179968156 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (7 : ZMod 896134490989) ^ 382799868 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (7 : ZMod 896134490989) ^ 53459076 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyER_1067017669391 : Nat.Prime 1067017669391 := by
  apply lucas_primality 1067017669391 (11 : ZMod 1067017669391)
  · rw [← oneHundredFiftyERFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (106701766939, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (106701766939, 1)] : List FactorBlock).map factorBlockValue).prod) = 1067017669391 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyER_2
      · exact prime_oneHundredFiftyER_5
      · exact prime_oneHundredFiftyER_106701766939
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (11 : ZMod 1067017669391) ^ 533508834695 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (11 : ZMod 1067017669391) ^ 213403533878 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (11 : ZMod 1067017669391) ^ 10 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyER_1250873909741 : Nat.Prime 1250873909741 := by
  apply lucas_primality 1250873909741 (2 : ZMod 1250873909741)
  · rw [← oneHundredFiftyERFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (7, 1), (13, 1), (17, 1), (40429021, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (7, 1), (13, 1), (17, 1), (40429021, 1)] : List FactorBlock).map factorBlockValue).prod) = 1250873909741 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyER_2
      · exact prime_oneHundredFiftyER_5
      · exact prime_oneHundredFiftyER_7
      · exact prime_oneHundredFiftyER_13
      · exact prime_oneHundredFiftyER_17
      · exact prime_oneHundredFiftyER_40429021
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1250873909741) ^ 625436954870 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 1250873909741) ^ 250174781948 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 1250873909741) ^ 178696272820 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 1250873909741) ^ 96221069980 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 1250873909741) ^ 73580818220 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 1250873909741) ^ 30940 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyER_1343356441067 : Nat.Prime 1343356441067 := by
  apply lucas_primality 1343356441067 (2 : ZMod 1343356441067)
  · rw [← oneHundredFiftyERFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (671678220533, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (671678220533, 1)] : List FactorBlock).map factorBlockValue).prod) = 1343356441067 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredFiftyER_2
      · exact prime_oneHundredFiftyER_671678220533
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 1343356441067) ^ 671678220533 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 1343356441067) ^ 2 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyER_1370014198489 : Nat.Prime 1370014198489 := by
  apply lucas_primality 1370014198489 (7 : ZMod 1370014198489)
  · rw [← oneHundredFiftyERFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (13, 1), (13711, 1), (106753, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (13, 1), (13711, 1), (106753, 1)] : List FactorBlock).map factorBlockValue).prod) = 1370014198489 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyER_2
      · exact prime_oneHundredFiftyER_3
      · exact prime_oneHundredFiftyER_13
      · exact prime_oneHundredFiftyER_13711
      · exact prime_oneHundredFiftyER_106753
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 1370014198489) ^ 685007099244 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (7 : ZMod 1370014198489) ^ 456671399496 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (7 : ZMod 1370014198489) ^ 105385707576 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (7 : ZMod 1370014198489) ^ 99920808 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (7 : ZMod 1370014198489) ^ 12833496 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyER_1585614248051 : Nat.Prime 1585614248051 := by
  apply lucas_primality 1585614248051 (7 : ZMod 1585614248051)
  · rw [← oneHundredFiftyERFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (7, 2), (6793, 1), (95273, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (7, 2), (6793, 1), (95273, 1)] : List FactorBlock).map factorBlockValue).prod) = 1585614248051 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyER_2
      · exact prime_oneHundredFiftyER_5
      · exact prime_oneHundredFiftyER_7
      · exact prime_oneHundredFiftyER_6793
      · exact prime_oneHundredFiftyER_95273
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 1585614248051) ^ 792807124025 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (7 : ZMod 1585614248051) ^ 317122849610 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (7 : ZMod 1585614248051) ^ 226516321150 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (7 : ZMod 1585614248051) ^ 233418850 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (7 : ZMod 1585614248051) ^ 16642850 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyER_1914633350029 : Nat.Prime 1914633350029 := by
  apply lucas_primality 1914633350029 (2 : ZMod 1914633350029)
  · rw [← oneHundredFiftyERFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (7, 1), (7597751389, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (7, 1), (7597751389, 1)] : List FactorBlock).map factorBlockValue).prod) = 1914633350029 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyER_2
      · exact prime_oneHundredFiftyER_3
      · exact prime_oneHundredFiftyER_7
      · exact prime_oneHundredFiftyER_7597751389
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1914633350029) ^ 957316675014 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 1914633350029) ^ 638211116676 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 1914633350029) ^ 273519050004 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 1914633350029) ^ 252 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyER_2729490688553 : Nat.Prime 2729490688553 := by
  apply lucas_primality 2729490688553 (3 : ZMod 2729490688553)
  · rw [← oneHundredFiftyERFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (173, 1), (35069, 1), (56237, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (173, 1), (35069, 1), (56237, 1)] : List FactorBlock).map factorBlockValue).prod) = 2729490688553 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyER_2
      · exact prime_oneHundredFiftyER_173
      · exact prime_oneHundredFiftyER_35069
      · exact prime_oneHundredFiftyER_56237
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 2729490688553) ^ 1364745344276 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (3 : ZMod 2729490688553) ^ 15777402824 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (3 : ZMod 2729490688553) ^ 77832008 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (3 : ZMod 2729490688553) ^ 48535496 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyER_2800878888487 : Nat.Prime 2800878888487 := by
  apply lucas_primality 2800878888487 (5 : ZMod 2800878888487)
  · rw [← oneHundredFiftyERFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (431, 1), (154727593, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (431, 1), (154727593, 1)] : List FactorBlock).map factorBlockValue).prod) = 2800878888487 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyER_2
      · exact prime_oneHundredFiftyER_3
      · exact prime_oneHundredFiftyER_7
      · exact prime_oneHundredFiftyER_431
      · exact prime_oneHundredFiftyER_154727593
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 2800878888487) ^ 1400439444243 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (5 : ZMod 2800878888487) ^ 933626296162 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (5 : ZMod 2800878888487) ^ 400125555498 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (5 : ZMod 2800878888487) ^ 6498558906 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (5 : ZMod 2800878888487) ^ 18102 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyER_2843538109751 : Nat.Prime 2843538109751 := by
  apply lucas_primality 2843538109751 (11 : ZMod 2843538109751)
  · rw [← oneHundredFiftyERFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 3), (13, 1), (43, 1), (20347321, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 3), (13, 1), (43, 1), (20347321, 1)] : List FactorBlock).map factorBlockValue).prod) = 2843538109751 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyER_2
      · exact prime_oneHundredFiftyER_5
      · exact prime_oneHundredFiftyER_13
      · exact prime_oneHundredFiftyER_43
      · exact prime_oneHundredFiftyER_20347321
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 2843538109751) ^ 1421769054875 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (11 : ZMod 2843538109751) ^ 568707621950 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (11 : ZMod 2843538109751) ^ 218733700750 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (11 : ZMod 2843538109751) ^ 66128793250 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (11 : ZMod 2843538109751) ^ 139750 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyER_3330937342157 : Nat.Prime 3330937342157 := by
  apply lucas_primality 3330937342157 (2 : ZMod 3330937342157)
  · rw [← oneHundredFiftyERFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (113, 1), (7369330403, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (113, 1), (7369330403, 1)] : List FactorBlock).map factorBlockValue).prod) = 3330937342157 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyER_2
      · exact prime_oneHundredFiftyER_113
      · exact prime_oneHundredFiftyER_7369330403
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 3330937342157) ^ 1665468671078 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 3330937342157) ^ 29477321612 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 3330937342157) ^ 452 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyER_3504061096069 : Nat.Prime 3504061096069 := by
  apply lucas_primality 3504061096069 (10 : ZMod 3504061096069)
  · rw [← oneHundredFiftyERFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (13, 1), (14029, 1), (1601107, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (13, 1), (14029, 1), (1601107, 1)] : List FactorBlock).map factorBlockValue).prod) = 3504061096069 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyER_2
      · exact prime_oneHundredFiftyER_3
      · exact prime_oneHundredFiftyER_13
      · exact prime_oneHundredFiftyER_14029
      · exact prime_oneHundredFiftyER_1601107
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 3504061096069) ^ 1752030548034 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (10 : ZMod 3504061096069) ^ 1168020365356 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (10 : ZMod 3504061096069) ^ 269543161236 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (10 : ZMod 3504061096069) ^ 249772692 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (10 : ZMod 3504061096069) ^ 2188524 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyER_7341888420457 : Nat.Prime 7341888420457 := by
  apply lucas_primality 7341888420457 (5 : ZMod 7341888420457)
  · rw [← oneHundredFiftyERFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (19, 1), (16100632501, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (19, 1), (16100632501, 1)] : List FactorBlock).map factorBlockValue).prod) = 7341888420457 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyER_2
      · exact prime_oneHundredFiftyER_3
      · exact prime_oneHundredFiftyER_19
      · exact prime_oneHundredFiftyER_16100632501
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 7341888420457) ^ 3670944210228 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (5 : ZMod 7341888420457) ^ 2447296140152 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (5 : ZMod 7341888420457) ^ 386415180024 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (5 : ZMod 7341888420457) ^ 456 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyER_7358318379431 : Nat.Prime 7358318379431 := by
  apply lucas_primality 7358318379431 (13 : ZMod 7358318379431)
  · rw [← oneHundredFiftyERFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (73, 1), (229, 1), (44016979, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (73, 1), (229, 1), (44016979, 1)] : List FactorBlock).map factorBlockValue).prod) = 7358318379431 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyER_2
      · exact prime_oneHundredFiftyER_5
      · exact prime_oneHundredFiftyER_73
      · exact prime_oneHundredFiftyER_229
      · exact prime_oneHundredFiftyER_44016979
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 7358318379431) ^ 3679159189715 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (13 : ZMod 7358318379431) ^ 1471663675886 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (13 : ZMod 7358318379431) ^ 100798881910 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (13 : ZMod 7358318379431) ^ 32132394670 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (13 : ZMod 7358318379431) ^ 167170 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyER_8524454832463 : Nat.Prime 8524454832463 := by
  apply lucas_primality 8524454832463 (3 : ZMod 8524454832463)
  · rw [← oneHundredFiftyERFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (19, 1), (74775919583, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (19, 1), (74775919583, 1)] : List FactorBlock).map factorBlockValue).prod) = 8524454832463 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyER_2
      · exact prime_oneHundredFiftyER_3
      · exact prime_oneHundredFiftyER_19
      · exact prime_oneHundredFiftyER_74775919583
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 8524454832463) ^ 4262227416231 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (3 : ZMod 8524454832463) ^ 2841484944154 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (3 : ZMod 8524454832463) ^ 448655517498 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (3 : ZMod 8524454832463) ^ 114 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyER_10223538369013 : Nat.Prime 10223538369013 := by
  apply lucas_primality 10223538369013 (2 : ZMod 10223538369013)
  · rw [← oneHundredFiftyERFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (29, 1), (13147, 1), (744859, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (29, 1), (13147, 1), (744859, 1)] : List FactorBlock).map factorBlockValue).prod) = 10223538369013 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyER_2
      · exact prime_oneHundredFiftyER_3
      · exact prime_oneHundredFiftyER_29
      · exact prime_oneHundredFiftyER_13147
      · exact prime_oneHundredFiftyER_744859
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 10223538369013) ^ 5111769184506 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 10223538369013) ^ 3407846123004 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 10223538369013) ^ 352535805828 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 10223538369013) ^ 777632796 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 10223538369013) ^ 13725468 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyER_13971226936099 : Nat.Prime 13971226936099 := by
  apply lucas_primality 13971226936099 (2 : ZMod 13971226936099)
  · rw [← oneHundredFiftyERFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (17, 1), (21617, 1), (6336347, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (17, 1), (21617, 1), (6336347, 1)] : List FactorBlock).map factorBlockValue).prod) = 13971226936099 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyER_2
      · exact prime_oneHundredFiftyER_3
      · exact prime_oneHundredFiftyER_17
      · exact prime_oneHundredFiftyER_21617
      · exact prime_oneHundredFiftyER_6336347
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 13971226936099) ^ 6985613468049 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 13971226936099) ^ 4657075645366 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 13971226936099) ^ 821836878594 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 13971226936099) ^ 646307394 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 13971226936099) ^ 2204934 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyER_21160885802867 : Nat.Prime 21160885802867 := by
  apply lucas_primality 21160885802867 (2 : ZMod 21160885802867)
  · rw [← oneHundredFiftyERFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (2797, 1), (3782782589, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (2797, 1), (3782782589, 1)] : List FactorBlock).map factorBlockValue).prod) = 21160885802867 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyER_2
      · exact prime_oneHundredFiftyER_2797
      · exact prime_oneHundredFiftyER_3782782589
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 21160885802867) ^ 10580442901433 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 21160885802867) ^ 7565565178 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 21160885802867) ^ 5594 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyER_21721386824381 : Nat.Prime 21721386824381 := by
  apply lucas_primality 21721386824381 (2 : ZMod 21721386824381)
  · rw [← oneHundredFiftyERFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (1289, 1), (8999, 1), (93629, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (1289, 1), (8999, 1), (93629, 1)] : List FactorBlock).map factorBlockValue).prod) = 21721386824381 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyER_2
      · exact prime_oneHundredFiftyER_5
      · exact prime_oneHundredFiftyER_1289
      · exact prime_oneHundredFiftyER_8999
      · exact prime_oneHundredFiftyER_93629
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 21721386824381) ^ 10860693412190 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 21721386824381) ^ 4344277364876 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 21721386824381) ^ 16851347420 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 21721386824381) ^ 2413755620 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 21721386824381) ^ 231994220 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyER_22849263327643 : Nat.Prime 22849263327643 := by
  apply lucas_primality 22849263327643 (2 : ZMod 22849263327643)
  · rw [← oneHundredFiftyERFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (19, 1), (47, 1), (4264513499, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (19, 1), (47, 1), (4264513499, 1)] : List FactorBlock).map factorBlockValue).prod) = 22849263327643 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyER_2
      · exact prime_oneHundredFiftyER_3
      · exact prime_oneHundredFiftyER_19
      · exact prime_oneHundredFiftyER_47
      · exact prime_oneHundredFiftyER_4264513499
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 22849263327643) ^ 11424631663821 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 22849263327643) ^ 7616421109214 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 22849263327643) ^ 1202592806718 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 22849263327643) ^ 486154538886 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 22849263327643) ^ 5358 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyER_30886550519203 : Nat.Prime 30886550519203 := by
  apply lucas_primality 30886550519203 (2 : ZMod 30886550519203)
  · rw [← oneHundredFiftyERFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (7, 2), (193, 1), (5419, 1), (11161, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (7, 2), (193, 1), (5419, 1), (11161, 1)] : List FactorBlock).map factorBlockValue).prod) = 30886550519203 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyER_2
      · exact prime_oneHundredFiftyER_3
      · exact prime_oneHundredFiftyER_7
      · exact prime_oneHundredFiftyER_193
      · exact prime_oneHundredFiftyER_5419
      · exact prime_oneHundredFiftyER_11161
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 30886550519203) ^ 15443275259601 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 30886550519203) ^ 10295516839734 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 30886550519203) ^ 4412364359886 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 30886550519203) ^ 160033940514 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 30886550519203) ^ 5699677158 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 30886550519203) ^ 2767364082 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyER_40012680077077 : Nat.Prime 40012680077077 := by
  apply lucas_primality 40012680077077 (2 : ZMod 40012680077077)
  · rw [← oneHundredFiftyERFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 1), (335633, 1), (1419233, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 1), (335633, 1), (1419233, 1)] : List FactorBlock).map factorBlockValue).prod) = 40012680077077 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyER_2
      · exact prime_oneHundredFiftyER_3
      · exact prime_oneHundredFiftyER_7
      · exact prime_oneHundredFiftyER_335633
      · exact prime_oneHundredFiftyER_1419233
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 40012680077077) ^ 20006340038538 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 40012680077077) ^ 13337560025692 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 40012680077077) ^ 5716097153868 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 40012680077077) ^ 119215572 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 40012680077077) ^ 28193172 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyER_45752552594669 : Nat.Prime 45752552594669 := by
  apply lucas_primality 45752552594669 (2 : ZMod 45752552594669)
  · rw [← oneHundredFiftyERFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (47, 1), (243364641461, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (47, 1), (243364641461, 1)] : List FactorBlock).map factorBlockValue).prod) = 45752552594669 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyER_2
      · exact prime_oneHundredFiftyER_47
      · exact prime_oneHundredFiftyER_243364641461
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 45752552594669) ^ 22876276297334 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 45752552594669) ^ 973458565844 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 45752552594669) ^ 188 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyER_47061672383657 : Nat.Prime 47061672383657 := by
  apply lucas_primality 47061672383657 (3 : ZMod 47061672383657)
  · rw [← oneHundredFiftyERFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (7, 2), (120055286693, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (7, 2), (120055286693, 1)] : List FactorBlock).map factorBlockValue).prod) = 47061672383657 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyER_2
      · exact prime_oneHundredFiftyER_7
      · exact prime_oneHundredFiftyER_120055286693
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 47061672383657) ^ 23530836191828 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (3 : ZMod 47061672383657) ^ 6723096054808 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (3 : ZMod 47061672383657) ^ 392 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyER_47568427441531 : Nat.Prime 47568427441531 := by
  apply lucas_primality 47568427441531 (2 : ZMod 47568427441531)
  · rw [← oneHundredFiftyERFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (1585614248051, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (1585614248051, 1)] : List FactorBlock).map factorBlockValue).prod) = 47568427441531 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyER_2
      · exact prime_oneHundredFiftyER_3
      · exact prime_oneHundredFiftyER_5
      · exact prime_oneHundredFiftyER_1585614248051
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 47568427441531) ^ 23784213720765 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 47568427441531) ^ 15856142480510 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 47568427441531) ^ 9513685488306 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 47568427441531) ^ 30 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyER_49288369108031 : Nat.Prime 49288369108031 := by
  apply lucas_primality 49288369108031 (7 : ZMod 49288369108031)
  · rw [← oneHundredFiftyERFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (13, 1), (88003, 1), (4308277, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (13, 1), (88003, 1), (4308277, 1)] : List FactorBlock).map factorBlockValue).prod) = 49288369108031 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyER_2
      · exact prime_oneHundredFiftyER_5
      · exact prime_oneHundredFiftyER_13
      · exact prime_oneHundredFiftyER_88003
      · exact prime_oneHundredFiftyER_4308277
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 49288369108031) ^ 24644184554015 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (7 : ZMod 49288369108031) ^ 9857673821606 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (7 : ZMod 49288369108031) ^ 3791413008310 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (7 : ZMod 49288369108031) ^ 560076010 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (7 : ZMod 49288369108031) ^ 11440390 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyER_51274419565151 : Nat.Prime 51274419565151 := by
  apply lucas_primality 51274419565151 (23 : ZMod 51274419565151)
  · rw [← oneHundredFiftyERFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (41, 1), (25011911983, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (41, 1), (25011911983, 1)] : List FactorBlock).map factorBlockValue).prod) = 51274419565151 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyER_2
      · exact prime_oneHundredFiftyER_5
      · exact prime_oneHundredFiftyER_41
      · exact prime_oneHundredFiftyER_25011911983
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (23 : ZMod 51274419565151) ^ 25637209782575 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (23 : ZMod 51274419565151) ^ 10254883913030 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (23 : ZMod 51274419565151) ^ 1250595599150 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (23 : ZMod 51274419565151) ^ 2050 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyER_51712334066891 : Nat.Prime 51712334066891 := by
  apply lucas_primality 51712334066891 (2 : ZMod 51712334066891)
  · rw [← oneHundredFiftyERFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 1), (738747629527, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 1), (738747629527, 1)] : List FactorBlock).map factorBlockValue).prod) = 51712334066891 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyER_2
      · exact prime_oneHundredFiftyER_5
      · exact prime_oneHundredFiftyER_7
      · exact prime_oneHundredFiftyER_738747629527
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 51712334066891) ^ 25856167033445 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 51712334066891) ^ 10342466813378 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 51712334066891) ^ 7387476295270 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 51712334066891) ^ 70 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyER_56032271914331 : Nat.Prime 56032271914331 := by
  apply lucas_primality 56032271914331 (2 : ZMod 56032271914331)
  · rw [← oneHundredFiftyERFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (12113, 1), (462579641, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (12113, 1), (462579641, 1)] : List FactorBlock).map factorBlockValue).prod) = 56032271914331 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyER_2
      · exact prime_oneHundredFiftyER_5
      · exact prime_oneHundredFiftyER_12113
      · exact prime_oneHundredFiftyER_462579641
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 56032271914331) ^ 28016135957165 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 56032271914331) ^ 11206454382866 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 56032271914331) ^ 4625796410 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 56032271914331) ^ 121130 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyER_57793874370247 : Nat.Prime 57793874370247 := by
  apply lucas_primality 57793874370247 (5 : ZMod 57793874370247)
  · rw [← oneHundredFiftyERFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (7, 1), (17, 1), (96697, 1), (279029, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (7, 1), (17, 1), (96697, 1), (279029, 1)] : List FactorBlock).map factorBlockValue).prod) = 57793874370247 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyER_2
      · exact prime_oneHundredFiftyER_3
      · exact prime_oneHundredFiftyER_7
      · exact prime_oneHundredFiftyER_17
      · exact prime_oneHundredFiftyER_96697
      · exact prime_oneHundredFiftyER_279029
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 57793874370247) ^ 28896937185123 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (5 : ZMod 57793874370247) ^ 19264624790082 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (5 : ZMod 57793874370247) ^ 8256267767178 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (5 : ZMod 57793874370247) ^ 3399639668838 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (5 : ZMod 57793874370247) ^ 597680118 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (5 : ZMod 57793874370247) ^ 207124974 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyER_79439825942629 : Nat.Prime 79439825942629 := by
  apply lucas_primality 79439825942629 (2 : ZMod 79439825942629)
  · rw [← oneHundredFiftyERFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (41, 1), (227, 1), (711291017, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (41, 1), (227, 1), (711291017, 1)] : List FactorBlock).map factorBlockValue).prod) = 79439825942629 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyER_2
      · exact prime_oneHundredFiftyER_3
      · exact prime_oneHundredFiftyER_41
      · exact prime_oneHundredFiftyER_227
      · exact prime_oneHundredFiftyER_711291017
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 79439825942629) ^ 39719912971314 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 79439825942629) ^ 26479941980876 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 79439825942629) ^ 1937556730308 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 79439825942629) ^ 349955180364 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 79439825942629) ^ 111684 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyER_100111140810529 : Nat.Prime 100111140810529 := by
  apply lucas_primality 100111140810529 (11 : ZMod 100111140810529)
  · rw [← oneHundredFiftyERFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (13043, 1), (79952801, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (13043, 1), (79952801, 1)] : List FactorBlock).map factorBlockValue).prod) = 100111140810529 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyER_2
      · exact prime_oneHundredFiftyER_3
      · exact prime_oneHundredFiftyER_13043
      · exact prime_oneHundredFiftyER_79952801
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 100111140810529) ^ 50055570405264 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (11 : ZMod 100111140810529) ^ 33370380270176 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (11 : ZMod 100111140810529) ^ 7675468896 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (11 : ZMod 100111140810529) ^ 1252128 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyER_100257985466497 : Nat.Prime 100257985466497 := by
  apply lucas_primality 100257985466497 (5 : ZMod 100257985466497)
  · rw [← oneHundredFiftyERFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (3, 2), (11, 1), (13, 1), (19, 1), (173, 1), (185153, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (3, 2), (11, 1), (13, 1), (19, 1), (173, 1), (185153, 1)] : List FactorBlock).map factorBlockValue).prod) = 100257985466497 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyER_2
      · exact prime_oneHundredFiftyER_3
      · exact prime_oneHundredFiftyER_11
      · exact prime_oneHundredFiftyER_13
      · exact prime_oneHundredFiftyER_19
      · exact prime_oneHundredFiftyER_173
      · exact prime_oneHundredFiftyER_185153
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 100257985466497) ^ 50128992733248 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (5 : ZMod 100257985466497) ^ 33419328488832 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (5 : ZMod 100257985466497) ^ 9114362315136 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (5 : ZMod 100257985466497) ^ 7712152728192 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (5 : ZMod 100257985466497) ^ 5276736077184 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (5 : ZMod 100257985466497) ^ 579525927552 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (5 : ZMod 100257985466497) ^ 541487232 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyER_103831152582167 : Nat.Prime 103831152582167 := by
  apply lucas_primality 103831152582167 (5 : ZMod 103831152582167)
  · rw [← oneHundredFiftyERFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (32371, 1), (1603768073, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (32371, 1), (1603768073, 1)] : List FactorBlock).map factorBlockValue).prod) = 103831152582167 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyER_2
      · exact prime_oneHundredFiftyER_32371
      · exact prime_oneHundredFiftyER_1603768073
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 103831152582167) ^ 51915576291083 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (5 : ZMod 103831152582167) ^ 3207536146 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (5 : ZMod 103831152582167) ^ 64742 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyER_112064543828663 : Nat.Prime 112064543828663 := by
  apply lucas_primality 112064543828663 (5 : ZMod 112064543828663)
  · rw [← oneHundredFiftyERFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (56032271914331, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (56032271914331, 1)] : List FactorBlock).map factorBlockValue).prod) = 112064543828663 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredFiftyER_2
      · exact prime_oneHundredFiftyER_56032271914331
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 112064543828663) ^ 56032271914331 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (5 : ZMod 112064543828663) ^ 2 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyER_129885093883087 : Nat.Prime 129885093883087 := by
  apply lucas_primality 129885093883087 (3 : ZMod 129885093883087)
  · rw [← oneHundredFiftyERFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (19, 1), (103, 1), (11061581833, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (19, 1), (103, 1), (11061581833, 1)] : List FactorBlock).map factorBlockValue).prod) = 129885093883087 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyER_2
      · exact prime_oneHundredFiftyER_3
      · exact prime_oneHundredFiftyER_19
      · exact prime_oneHundredFiftyER_103
      · exact prime_oneHundredFiftyER_11061581833
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 129885093883087) ^ 64942546941543 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (3 : ZMod 129885093883087) ^ 43295031294362 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (3 : ZMod 129885093883087) ^ 6836057572794 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (3 : ZMod 129885093883087) ^ 1261020328962 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (3 : ZMod 129885093883087) ^ 11742 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyER_135986788140349 : Nat.Prime 135986788140349 := by
  apply lucas_primality 135986788140349 (7 : ZMod 135986788140349)
  · rw [← oneHundredFiftyERFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (79, 1), (1063, 1), (1499, 1), (90023, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (79, 1), (1063, 1), (1499, 1), (90023, 1)] : List FactorBlock).map factorBlockValue).prod) = 135986788140349 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyER_2
      · exact prime_oneHundredFiftyER_3
      · exact prime_oneHundredFiftyER_79
      · exact prime_oneHundredFiftyER_1063
      · exact prime_oneHundredFiftyER_1499
      · exact prime_oneHundredFiftyER_90023
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 135986788140349) ^ 67993394070174 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (7 : ZMod 135986788140349) ^ 45328929380116 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (7 : ZMod 135986788140349) ^ 1721351748612 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (7 : ZMod 135986788140349) ^ 127927364196 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (7 : ZMod 135986788140349) ^ 90718337652 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (7 : ZMod 135986788140349) ^ 1510578276 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyER_138705063180113 : Nat.Prime 138705063180113 := by
  apply lucas_primality 138705063180113 (3 : ZMod 138705063180113)
  · rw [← oneHundredFiftyERFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (11, 1), (13, 1), (17, 1), (3566049547, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (11, 1), (13, 1), (17, 1), (3566049547, 1)] : List FactorBlock).map factorBlockValue).prod) = 138705063180113 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyER_2
      · exact prime_oneHundredFiftyER_11
      · exact prime_oneHundredFiftyER_13
      · exact prime_oneHundredFiftyER_17
      · exact prime_oneHundredFiftyER_3566049547
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 138705063180113) ^ 69352531590056 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (3 : ZMod 138705063180113) ^ 12609551198192 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (3 : ZMod 138705063180113) ^ 10669620244624 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (3 : ZMod 138705063180113) ^ 8159121363536 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (3 : ZMod 138705063180113) ^ 38896 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyER_189219299187727 : Nat.Prime 189219299187727 := by
  apply lucas_primality 189219299187727 (19 : ZMod 189219299187727)
  · rw [← oneHundredFiftyERFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (3504061096069, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (3504061096069, 1)] : List FactorBlock).map factorBlockValue).prod) = 189219299187727 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyER_2
      · exact prime_oneHundredFiftyER_3
      · exact prime_oneHundredFiftyER_3504061096069
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (19 : ZMod 189219299187727) ^ 94609649593863 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (19 : ZMod 189219299187727) ^ 63073099729242 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (19 : ZMod 189219299187727) ^ 54 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyER_189964067570743 : Nat.Prime 189964067570743 := by
  apply lucas_primality 189964067570743 (3 : ZMod 189964067570743)
  · rw [← oneHundredFiftyERFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (17, 1), (53, 1), (179969, 1), (195253, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (17, 1), (53, 1), (179969, 1), (195253, 1)] : List FactorBlock).map factorBlockValue).prod) = 189964067570743 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyER_2
      · exact prime_oneHundredFiftyER_3
      · exact prime_oneHundredFiftyER_17
      · exact prime_oneHundredFiftyER_53
      · exact prime_oneHundredFiftyER_179969
      · exact prime_oneHundredFiftyER_195253
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 189964067570743) ^ 94982033785371 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (3 : ZMod 189964067570743) ^ 63321355856914 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (3 : ZMod 189964067570743) ^ 11174356915926 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (3 : ZMod 189964067570743) ^ 3584227690014 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (3 : ZMod 189964067570743) ^ 1055537718 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (3 : ZMod 189964067570743) ^ 972912414 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyER_192103473542443 : Nat.Prime 192103473542443 := by
  apply lucas_primality 192103473542443 (5 : ZMod 192103473542443)
  · rw [← oneHundredFiftyERFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (11, 1), (17, 1), (193, 1), (283, 1), (447817, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (11, 1), (17, 1), (193, 1), (283, 1), (447817, 1)] : List FactorBlock).map factorBlockValue).prod) = 192103473542443 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyER_2
      · exact prime_oneHundredFiftyER_3
      · exact prime_oneHundredFiftyER_7
      · exact prime_oneHundredFiftyER_11
      · exact prime_oneHundredFiftyER_17
      · exact prime_oneHundredFiftyER_193
      · exact prime_oneHundredFiftyER_283
      · exact prime_oneHundredFiftyER_447817
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 192103473542443) ^ 96051736771221 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (5 : ZMod 192103473542443) ^ 64034491180814 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (5 : ZMod 192103473542443) ^ 27443353363206 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (5 : ZMod 192103473542443) ^ 17463952140222 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (5 : ZMod 192103473542443) ^ 11300204326026 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (5 : ZMod 192103473542443) ^ 995354785194 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (5 : ZMod 192103473542443) ^ 678810860574 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (5 : ZMod 192103473542443) ^ 428977626 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyER_236872066185113 : Nat.Prime 236872066185113 := by
  apply lucas_primality 236872066185113 (3 : ZMod 236872066185113)
  · rw [← oneHundredFiftyERFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (19, 2), (47417, 1), (1729747, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (19, 2), (47417, 1), (1729747, 1)] : List FactorBlock).map factorBlockValue).prod) = 236872066185113 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyER_2
      · exact prime_oneHundredFiftyER_19
      · exact prime_oneHundredFiftyER_47417
      · exact prime_oneHundredFiftyER_1729747
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 236872066185113) ^ 118436033092556 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (3 : ZMod 236872066185113) ^ 12466950851848 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (3 : ZMod 236872066185113) ^ 4995509336 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (3 : ZMod 236872066185113) ^ 136940296 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyER_239147013649849 : Nat.Prime 239147013649849 := by
  apply lucas_primality 239147013649849 (11 : ZMod 239147013649849)
  · rw [← oneHundredFiftyERFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (62303, 1), (159935459, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (62303, 1), (159935459, 1)] : List FactorBlock).map factorBlockValue).prod) = 239147013649849 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyER_2
      · exact prime_oneHundredFiftyER_3
      · exact prime_oneHundredFiftyER_62303
      · exact prime_oneHundredFiftyER_159935459
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 239147013649849) ^ 119573506824924 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (11 : ZMod 239147013649849) ^ 79715671216616 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (11 : ZMod 239147013649849) ^ 3838451016 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (11 : ZMod 239147013649849) ^ 1495272 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyER_247184120357417 : Nat.Prime 247184120357417 := by
  apply lucas_primality 247184120357417 (3 : ZMod 247184120357417)
  · rw [← oneHundredFiftyERFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (11, 2), (71191, 1), (3586907, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (11, 2), (71191, 1), (3586907, 1)] : List FactorBlock).map factorBlockValue).prod) = 247184120357417 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyER_2
      · exact prime_oneHundredFiftyER_11
      · exact prime_oneHundredFiftyER_71191
      · exact prime_oneHundredFiftyER_3586907
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 247184120357417) ^ 123592060178708 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (3 : ZMod 247184120357417) ^ 22471283668856 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (3 : ZMod 247184120357417) ^ 3472125976 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (3 : ZMod 247184120357417) ^ 68912888 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyER_269000696564003 : Nat.Prime 269000696564003 := by
  apply lucas_primality 269000696564003 (2 : ZMod 269000696564003)
  · rw [← oneHundredFiftyERFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (41, 1), (70957, 1), (3556321, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (41, 1), (70957, 1), (3556321, 1)] : List FactorBlock).map factorBlockValue).prod) = 269000696564003 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyER_2
      · exact prime_oneHundredFiftyER_13
      · exact prime_oneHundredFiftyER_41
      · exact prime_oneHundredFiftyER_70957
      · exact prime_oneHundredFiftyER_3556321
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 269000696564003) ^ 134500348282001 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 269000696564003) ^ 20692361274154 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 269000696564003) ^ 6560992599122 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 269000696564003) ^ 3791038186 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 269000696564003) ^ 75640162 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyER_273308408322643 : Nat.Prime 273308408322643 := by
  apply lucas_primality 273308408322643 (3 : ZMod 273308408322643)
  · rw [← oneHundredFiftyERFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (7, 1), (11, 1), (1109, 1), (5273, 1), (33721, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (7, 1), (11, 1), (1109, 1), (5273, 1), (33721, 1)] : List FactorBlock).map factorBlockValue).prod) = 273308408322643 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyER_2
      · exact prime_oneHundredFiftyER_3
      · exact prime_oneHundredFiftyER_7
      · exact prime_oneHundredFiftyER_11
      · exact prime_oneHundredFiftyER_1109
      · exact prime_oneHundredFiftyER_5273
      · exact prime_oneHundredFiftyER_33721
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 273308408322643) ^ 136654204161321 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (3 : ZMod 273308408322643) ^ 91102802774214 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (3 : ZMod 273308408322643) ^ 39044058331806 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (3 : ZMod 273308408322643) ^ 24846218938422 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (3 : ZMod 273308408322643) ^ 246445814538 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (3 : ZMod 273308408322643) ^ 51831672354 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (3 : ZMod 273308408322643) ^ 8104991202 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyER_281546073328321 : Nat.Prime 281546073328321 := by
  apply lucas_primality 281546073328321 (17 : ZMod 281546073328321)
  · rw [← oneHundredFiftyERFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 2), (5, 1), (797, 1), (122658787, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 2), (5, 1), (797, 1), (122658787, 1)] : List FactorBlock).map factorBlockValue).prod) = 281546073328321 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyER_2
      · exact prime_oneHundredFiftyER_3
      · exact prime_oneHundredFiftyER_5
      · exact prime_oneHundredFiftyER_797
      · exact prime_oneHundredFiftyER_122658787
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (17 : ZMod 281546073328321) ^ 140773036664160 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (17 : ZMod 281546073328321) ^ 93848691109440 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (17 : ZMod 281546073328321) ^ 56309214665664 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (17 : ZMod 281546073328321) ^ 353257306560 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (17 : ZMod 281546073328321) ^ 2295360 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyER_366020420757353 : Nat.Prime 366020420757353 := by
  apply lucas_primality 366020420757353 (3 : ZMod 366020420757353)
  · rw [← oneHundredFiftyERFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (45752552594669, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (45752552594669, 1)] : List FactorBlock).map factorBlockValue).prod) = 366020420757353 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredFiftyER_2
      · exact prime_oneHundredFiftyER_45752552594669
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 366020420757353) ^ 183010210378676 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (3 : ZMod 366020420757353) ^ 8 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyER_456215739524723 : Nat.Prime 456215739524723 := by
  apply lucas_primality 456215739524723 (2 : ZMod 456215739524723)
  · rw [← oneHundredFiftyERFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (31, 1), (7358318379431, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (31, 1), (7358318379431, 1)] : List FactorBlock).map factorBlockValue).prod) = 456215739524723 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyER_2
      · exact prime_oneHundredFiftyER_31
      · exact prime_oneHundredFiftyER_7358318379431
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 456215739524723) ^ 228107869762361 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 456215739524723) ^ 14716636758862 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 456215739524723) ^ 62 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyER_694929927928631 : Nat.Prime 694929927928631 := by
  apply lucas_primality 694929927928631 (13 : ZMod 694929927928631)
  · rw [← oneHundredFiftyERFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (569, 1), (1571, 1), (77741437, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (569, 1), (1571, 1), (77741437, 1)] : List FactorBlock).map factorBlockValue).prod) = 694929927928631 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyER_2
      · exact prime_oneHundredFiftyER_5
      · exact prime_oneHundredFiftyER_569
      · exact prime_oneHundredFiftyER_1571
      · exact prime_oneHundredFiftyER_77741437
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 694929927928631) ^ 347464963964315 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (13 : ZMod 694929927928631) ^ 138985985585726 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (13 : ZMod 694929927928631) ^ 1221317975270 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (13 : ZMod 694929927928631) ^ 442348776530 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (13 : ZMod 694929927928631) ^ 8938990 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyER_734440943417771 : Nat.Prime 734440943417771 := by
  apply lucas_primality 734440943417771 (6 : ZMod 734440943417771)
  · rw [← oneHundredFiftyERFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (1597, 1), (45988787941, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (1597, 1), (45988787941, 1)] : List FactorBlock).map factorBlockValue).prod) = 734440943417771 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyER_2
      · exact prime_oneHundredFiftyER_5
      · exact prime_oneHundredFiftyER_1597
      · exact prime_oneHundredFiftyER_45988787941
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 734440943417771) ^ 367220471708885 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (6 : ZMod 734440943417771) ^ 146888188683554 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (6 : ZMod 734440943417771) ^ 459887879410 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (6 : ZMod 734440943417771) ^ 15970 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyER_766253565009377 : Nat.Prime 766253565009377 := by
  apply lucas_primality 766253565009377 (3 : ZMod 766253565009377)
  · rw [← oneHundredFiftyERFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (23, 1), (11551, 1), (90131191, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (23, 1), (11551, 1), (90131191, 1)] : List FactorBlock).map factorBlockValue).prod) = 766253565009377 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyER_2
      · exact prime_oneHundredFiftyER_23
      · exact prime_oneHundredFiftyER_11551
      · exact prime_oneHundredFiftyER_90131191
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 766253565009377) ^ 383126782504688 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (3 : ZMod 766253565009377) ^ 33315372391712 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (3 : ZMod 766253565009377) ^ 66336556576 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (3 : ZMod 766253565009377) ^ 8501536 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyER_952352509668073 : Nat.Prime 952352509668073 := by
  apply lucas_primality 952352509668073 (7 : ZMod 952352509668073)
  · rw [← oneHundredFiftyERFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (37, 1), (6491, 1), (165224009, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (37, 1), (6491, 1), (165224009, 1)] : List FactorBlock).map factorBlockValue).prod) = 952352509668073 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyER_2
      · exact prime_oneHundredFiftyER_3
      · exact prime_oneHundredFiftyER_37
      · exact prime_oneHundredFiftyER_6491
      · exact prime_oneHundredFiftyER_165224009
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 952352509668073) ^ 476176254834036 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (7 : ZMod 952352509668073) ^ 317450836556024 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (7 : ZMod 952352509668073) ^ 25739257018056 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (7 : ZMod 952352509668073) ^ 146718919992 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (7 : ZMod 952352509668073) ^ 5764008 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyER_983326402410041 : Nat.Prime 983326402410041 := by
  apply lucas_primality 983326402410041 (6 : ZMod 983326402410041)
  · rw [← oneHundredFiftyERFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (13, 1), (79, 1), (32609, 1), (734057, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (13, 1), (79, 1), (32609, 1), (734057, 1)] : List FactorBlock).map factorBlockValue).prod) = 983326402410041 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyER_2
      · exact prime_oneHundredFiftyER_5
      · exact prime_oneHundredFiftyER_13
      · exact prime_oneHundredFiftyER_79
      · exact prime_oneHundredFiftyER_32609
      · exact prime_oneHundredFiftyER_734057
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 983326402410041) ^ 491663201205020 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (6 : ZMod 983326402410041) ^ 196665280482008 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (6 : ZMod 983326402410041) ^ 75640492493080 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (6 : ZMod 983326402410041) ^ 12447169650760 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (6 : ZMod 983326402410041) ^ 30155061560 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (6 : ZMod 983326402410041) ^ 1339577720 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyER_2230458273400883 : Nat.Prime 2230458273400883 := by
  apply lucas_primality 2230458273400883 (2 : ZMod 2230458273400883)
  · rw [← oneHundredFiftyERFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 2), (457, 1), (120091, 1), (414707, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 2), (457, 1), (120091, 1), (414707, 1)] : List FactorBlock).map factorBlockValue).prod) = 2230458273400883 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyER_2
      · exact prime_oneHundredFiftyER_7
      · exact prime_oneHundredFiftyER_457
      · exact prime_oneHundredFiftyER_120091
      · exact prime_oneHundredFiftyER_414707
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 2230458273400883) ^ 1115229136700441 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 2230458273400883) ^ 318636896200126 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 2230458273400883) ^ 4880652677026 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 2230458273400883) ^ 18573067702 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 2230458273400883) ^ 5378395526 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyER_4008755870781787 : Nat.Prime 4008755870781787 := by
  apply lucas_primality 4008755870781787 (2 : ZMod 4008755870781787)
  · rw [← oneHundredFiftyERFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (719, 1), (81559, 1), (3797837, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (719, 1), (81559, 1), (3797837, 1)] : List FactorBlock).map factorBlockValue).prod) = 4008755870781787 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyER_2
      · exact prime_oneHundredFiftyER_3
      · exact prime_oneHundredFiftyER_719
      · exact prime_oneHundredFiftyER_81559
      · exact prime_oneHundredFiftyER_3797837
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 4008755870781787) ^ 2004377935390893 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 4008755870781787) ^ 1336251956927262 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 4008755870781787) ^ 5575460181894 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 4008755870781787) ^ 49151606454 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 4008755870781787) ^ 1055536578 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyER_4613086018624079 : Nat.Prime 4613086018624079 := by
  apply lucas_primality 4613086018624079 (23 : ZMod 4613086018624079)
  · rw [← oneHundredFiftyERFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 1), (101, 1), (1343356441067, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 1), (101, 1), (1343356441067, 1)] : List FactorBlock).map factorBlockValue).prod) = 4613086018624079 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyER_2
      · exact prime_oneHundredFiftyER_17
      · exact prime_oneHundredFiftyER_101
      · exact prime_oneHundredFiftyER_1343356441067
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (23 : ZMod 4613086018624079) ^ 2306543009312039 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (23 : ZMod 4613086018624079) ^ 271358001095534 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (23 : ZMod 4613086018624079) ^ 45674118996278 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (23 : ZMod 4613086018624079) ^ 3434 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyER_5939149323450269 : Nat.Prime 5939149323450269 := by
  apply lucas_primality 5939149323450269 (2 : ZMod 5939149323450269)
  · rw [← oneHundredFiftyERFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (1187, 1), (1250873909741, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (1187, 1), (1250873909741, 1)] : List FactorBlock).map factorBlockValue).prod) = 5939149323450269 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyER_2
      · exact prime_oneHundredFiftyER_1187
      · exact prime_oneHundredFiftyER_1250873909741
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 5939149323450269) ^ 2969574661725134 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 5939149323450269) ^ 5003495638964 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 5939149323450269) ^ 4748 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyER_6376525061137417 : Nat.Prime 6376525061137417 := by
  apply lucas_primality 6376525061137417 (5 : ZMod 6376525061137417)
  · rw [← oneHundredFiftyERFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (71, 1), (89, 1), (1553, 1), (9024679, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (71, 1), (89, 1), (1553, 1), (9024679, 1)] : List FactorBlock).map factorBlockValue).prod) = 6376525061137417 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyER_2
      · exact prime_oneHundredFiftyER_3
      · exact prime_oneHundredFiftyER_71
      · exact prime_oneHundredFiftyER_89
      · exact prime_oneHundredFiftyER_1553
      · exact prime_oneHundredFiftyER_9024679
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 6376525061137417) ^ 3188262530568708 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (5 : ZMod 6376525061137417) ^ 2125508353712472 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (5 : ZMod 6376525061137417) ^ 89810212128696 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (5 : ZMod 6376525061137417) ^ 71646349001544 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (5 : ZMod 6376525061137417) ^ 4105940155272 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (5 : ZMod 6376525061137417) ^ 706565304 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyER_14447245053557023 : Nat.Prime 14447245053557023 := by
  apply lucas_primality 14447245053557023 (3 : ZMod 14447245053557023)
  · rw [← oneHundredFiftyERFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 3), (10909, 1), (643509151, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 3), (10909, 1), (643509151, 1)] : List FactorBlock).map factorBlockValue).prod) = 14447245053557023 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyER_2
      · exact prime_oneHundredFiftyER_3
      · exact prime_oneHundredFiftyER_7
      · exact prime_oneHundredFiftyER_10909
      · exact prime_oneHundredFiftyER_643509151
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 14447245053557023) ^ 7223622526778511 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (3 : ZMod 14447245053557023) ^ 4815748351185674 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (3 : ZMod 14447245053557023) ^ 2063892150508146 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (3 : ZMod 14447245053557023) ^ 1324341832758 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (3 : ZMod 14447245053557023) ^ 22450722 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyER_17204350304931341 : Nat.Prime 17204350304931341 := by
  apply lucas_primality 17204350304931341 (2 : ZMod 17204350304931341)
  · rw [← oneHundredFiftyERFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (37, 1), (100517, 1), (231295423, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (37, 1), (100517, 1), (231295423, 1)] : List FactorBlock).map factorBlockValue).prod) = 17204350304931341 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyER_2
      · exact prime_oneHundredFiftyER_5
      · exact prime_oneHundredFiftyER_37
      · exact prime_oneHundredFiftyER_100517
      · exact prime_oneHundredFiftyER_231295423
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 17204350304931341) ^ 8602175152465670 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 17204350304931341) ^ 3440870060986268 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 17204350304931341) ^ 464982440673820 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 17204350304931341) ^ 171158613020 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 17204350304931341) ^ 74382580 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyER_17575151329655131 : Nat.Prime 17575151329655131 := by
  apply lucas_primality 17575151329655131 (10 : ZMod 17575151329655131)
  · rw [← oneHundredFiftyERFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (67, 1), (366287, 1), (23871599, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (67, 1), (366287, 1), (23871599, 1)] : List FactorBlock).map factorBlockValue).prod) = 17575151329655131 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyER_2
      · exact prime_oneHundredFiftyER_3
      · exact prime_oneHundredFiftyER_5
      · exact prime_oneHundredFiftyER_67
      · exact prime_oneHundredFiftyER_366287
      · exact prime_oneHundredFiftyER_23871599
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 17575151329655131) ^ 8787575664827565 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (10 : ZMod 17575151329655131) ^ 5858383776551710 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (10 : ZMod 17575151329655131) ^ 3515030265931026 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (10 : ZMod 17575151329655131) ^ 262315691487390 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (10 : ZMod 17575151329655131) ^ 47981913990 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (10 : ZMod 17575151329655131) ^ 736236870 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyER_18026111139253033 : Nat.Prime 18026111139253033 := by
  apply lucas_primality 18026111139253033 (5 : ZMod 18026111139253033)
  · rw [← oneHundredFiftyERFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (219979, 1), (3414362117, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (219979, 1), (3414362117, 1)] : List FactorBlock).map factorBlockValue).prod) = 18026111139253033 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyER_2
      · exact prime_oneHundredFiftyER_3
      · exact prime_oneHundredFiftyER_219979
      · exact prime_oneHundredFiftyER_3414362117
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 18026111139253033) ^ 9013055569626516 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (5 : ZMod 18026111139253033) ^ 6008703713084344 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (5 : ZMod 18026111139253033) ^ 81944690808 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (5 : ZMod 18026111139253033) ^ 5279496 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyER_35191226542465943 : Nat.Prime 35191226542465943 := by
  apply lucas_primality 35191226542465943 (5 : ZMod 35191226542465943)
  · rw [← oneHundredFiftyERFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (28541, 1), (47423310787, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (28541, 1), (47423310787, 1)] : List FactorBlock).map factorBlockValue).prod) = 35191226542465943 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyER_2
      · exact prime_oneHundredFiftyER_13
      · exact prime_oneHundredFiftyER_28541
      · exact prime_oneHundredFiftyER_47423310787
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 35191226542465943) ^ 17595613271232971 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (5 : ZMod 35191226542465943) ^ 2707017426343534 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (5 : ZMod 35191226542465943) ^ 1233006080462 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (5 : ZMod 35191226542465943) ^ 742066 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyER_54505364198768423 : Nat.Prime 54505364198768423 := by
  apply lucas_primality 54505364198768423 (5 : ZMod 54505364198768423)
  · rw [← oneHundredFiftyERFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (23, 1), (139, 1), (8524454832463, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (23, 1), (139, 1), (8524454832463, 1)] : List FactorBlock).map factorBlockValue).prod) = 54505364198768423 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyER_2
      · exact prime_oneHundredFiftyER_23
      · exact prime_oneHundredFiftyER_139
      · exact prime_oneHundredFiftyER_8524454832463
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 54505364198768423) ^ 27252682099384211 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (5 : ZMod 54505364198768423) ^ 2369798443424714 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (5 : ZMod 54505364198768423) ^ 392124922293298 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (5 : ZMod 54505364198768423) ^ 6394 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyER_62560202419495043 : Nat.Prime 62560202419495043 := by
  apply lucas_primality 62560202419495043 (2 : ZMod 62560202419495043)
  · rw [← oneHundredFiftyERFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (131, 1), (839, 1), (284599998269, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (131, 1), (839, 1), (284599998269, 1)] : List FactorBlock).map factorBlockValue).prod) = 62560202419495043 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyER_2
      · exact prime_oneHundredFiftyER_131
      · exact prime_oneHundredFiftyER_839
      · exact prime_oneHundredFiftyER_284599998269
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 62560202419495043) ^ 31280101209747521 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 62560202419495043) ^ 477558797095382 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 62560202419495043) ^ 74565199546478 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 62560202419495043) ^ 219818 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyER_90271424483937779 : Nat.Prime 90271424483937779 := by
  apply lucas_primality 90271424483937779 (2 : ZMod 90271424483937779)
  · rw [← oneHundredFiftyERFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (131, 1), (771643, 1), (446511433, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (131, 1), (771643, 1), (446511433, 1)] : List FactorBlock).map factorBlockValue).prod) = 90271424483937779 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyER_2
      · exact prime_oneHundredFiftyER_131
      · exact prime_oneHundredFiftyER_771643
      · exact prime_oneHundredFiftyER_446511433
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 90271424483937779) ^ 45135712241968889 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 90271424483937779) ^ 689094843388838 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 90271424483937779) ^ 116985995446 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 90271424483937779) ^ 202170466 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyER_91950427801125241 : Nat.Prime 91950427801125241 := by
  apply lucas_primality 91950427801125241 (14 : ZMod 91950427801125241)
  · rw [← oneHundredFiftyERFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 1), (766253565009377, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 1), (766253565009377, 1)] : List FactorBlock).map factorBlockValue).prod) = 91950427801125241 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyER_2
      · exact prime_oneHundredFiftyER_3
      · exact prime_oneHundredFiftyER_5
      · exact prime_oneHundredFiftyER_766253565009377
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (14 : ZMod 91950427801125241) ^ 45975213900562620 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (14 : ZMod 91950427801125241) ^ 30650142600375080 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (14 : ZMod 91950427801125241) ^ 18390085560225048 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (14 : ZMod 91950427801125241) ^ 120 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyER_101506984564892419 : Nat.Prime 101506984564892419 := by
  apply lucas_primality 101506984564892419 (3 : ZMod 101506984564892419)
  · rw [← oneHundredFiftyERFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (1693, 1), (3330937342157, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (1693, 1), (3330937342157, 1)] : List FactorBlock).map factorBlockValue).prod) = 101506984564892419 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyER_2
      · exact prime_oneHundredFiftyER_3
      · exact prime_oneHundredFiftyER_1693
      · exact prime_oneHundredFiftyER_3330937342157
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 101506984564892419) ^ 50753492282446209 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (3 : ZMod 101506984564892419) ^ 33835661521630806 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (3 : ZMod 101506984564892419) ^ 59956872158826 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (3 : ZMod 101506984564892419) ^ 30474 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyER_112245164381890037 : Nat.Prime 112245164381890037 := by
  apply lucas_primality 112245164381890037 (2 : ZMod 112245164381890037)
  · rw [← oneHundredFiftyERFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (4008755870781787, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (4008755870781787, 1)] : List FactorBlock).map factorBlockValue).prod) = 112245164381890037 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyER_2
      · exact prime_oneHundredFiftyER_7
      · exact prime_oneHundredFiftyER_4008755870781787
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 112245164381890037) ^ 56122582190945018 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 112245164381890037) ^ 16035023483127148 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 112245164381890037) ^ 28 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyER_138328986999972149 : Nat.Prime 138328986999972149 := by
  apply lucas_primality 138328986999972149 (2 : ZMod 138328986999972149)
  · rw [← oneHundredFiftyERFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (727, 1), (47568427441531, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (727, 1), (47568427441531, 1)] : List FactorBlock).map factorBlockValue).prod) = 138328986999972149 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyER_2
      · exact prime_oneHundredFiftyER_727
      · exact prime_oneHundredFiftyER_47568427441531
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 138328986999972149) ^ 69164493499986074 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 138328986999972149) ^ 190273709766124 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 138328986999972149) ^ 2908 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyER_153088067484138301 : Nat.Prime 153088067484138301 := by
  apply lucas_primality 153088067484138301 (10 : ZMod 153088067484138301)
  · rw [← oneHundredFiftyERFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 2), (34603, 1), (45691, 1), (322757, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 2), (34603, 1), (45691, 1), (322757, 1)] : List FactorBlock).map factorBlockValue).prod) = 153088067484138301 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyER_2
      · exact prime_oneHundredFiftyER_3
      · exact prime_oneHundredFiftyER_5
      · exact prime_oneHundredFiftyER_34603
      · exact prime_oneHundredFiftyER_45691
      · exact prime_oneHundredFiftyER_322757
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 153088067484138301) ^ 76544033742069150 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (10 : ZMod 153088067484138301) ^ 51029355828046100 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (10 : ZMod 153088067484138301) ^ 30617613496827660 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (10 : ZMod 153088067484138301) ^ 4424127026100 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (10 : ZMod 153088067484138301) ^ 3350508141300 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (10 : ZMod 153088067484138301) ^ 474313701900 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyER_158812959932849581 : Nat.Prime 158812959932849581 := by
  apply lucas_primality 158812959932849581 (2 : ZMod 158812959932849581)
  · rw [← oneHundredFiftyERFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (59, 1), (997, 1), (44997410291, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (59, 1), (997, 1), (44997410291, 1)] : List FactorBlock).map factorBlockValue).prod) = 158812959932849581 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyER_2
      · exact prime_oneHundredFiftyER_3
      · exact prime_oneHundredFiftyER_5
      · exact prime_oneHundredFiftyER_59
      · exact prime_oneHundredFiftyER_997
      · exact prime_oneHundredFiftyER_44997410291
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 158812959932849581) ^ 79406479966424790 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 158812959932849581) ^ 52937653310949860 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 158812959932849581) ^ 31762591986569916 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 158812959932849581) ^ 2691745083607620 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 158812959932849581) ^ 159290832430140 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 158812959932849581) ^ 3529380 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyER_161555159326910779 : Nat.Prime 161555159326910779 := by
  apply lucas_primality 161555159326910779 (2 : ZMod 161555159326910779)
  · rw [← oneHundredFiftyERFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (11, 1), (13, 1), (1889, 1), (11075391241, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (11, 1), (13, 1), (1889, 1), (11075391241, 1)] : List FactorBlock).map factorBlockValue).prod) = 161555159326910779 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyER_2
      · exact prime_oneHundredFiftyER_3
      · exact prime_oneHundredFiftyER_11
      · exact prime_oneHundredFiftyER_13
      · exact prime_oneHundredFiftyER_1889
      · exact prime_oneHundredFiftyER_11075391241
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 161555159326910779) ^ 80777579663455389 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 161555159326910779) ^ 53851719775636926 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 161555159326910779) ^ 14686832666082798 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 161555159326910779) ^ 12427319948223906 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 161555159326910779) ^ 85524171163002 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 161555159326910779) ^ 14586858 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyER_165234188632483169 : Nat.Prime 165234188632483169 := by
  apply lucas_primality 165234188632483169 (3 : ZMod 165234188632483169)
  · rw [← oneHundredFiftyERFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (11, 1), (89, 1), (2777, 1), (1899290353, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (11, 1), (89, 1), (2777, 1), (1899290353, 1)] : List FactorBlock).map factorBlockValue).prod) = 165234188632483169 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyER_2
      · exact prime_oneHundredFiftyER_11
      · exact prime_oneHundredFiftyER_89
      · exact prime_oneHundredFiftyER_2777
      · exact prime_oneHundredFiftyER_1899290353
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 165234188632483169) ^ 82617094316241584 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (3 : ZMod 165234188632483169) ^ 15021289875680288 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (3 : ZMod 165234188632483169) ^ 1856563917218912 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (3 : ZMod 165234188632483169) ^ 59500968178784 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (3 : ZMod 165234188632483169) ^ 86997856 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyER_166201589441944417 : Nat.Prime 166201589441944417 := by
  apply lucas_primality 166201589441944417 (10 : ZMod 166201589441944417)
  · rw [← oneHundredFiftyERFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (631, 1), (15377, 1), (178427983, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (631, 1), (15377, 1), (178427983, 1)] : List FactorBlock).map factorBlockValue).prod) = 166201589441944417 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyER_2
      · exact prime_oneHundredFiftyER_3
      · exact prime_oneHundredFiftyER_631
      · exact prime_oneHundredFiftyER_15377
      · exact prime_oneHundredFiftyER_178427983
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 166201589441944417) ^ 83100794720972208 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (10 : ZMod 166201589441944417) ^ 55400529813981472 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (10 : ZMod 166201589441944417) ^ 263393961080736 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (10 : ZMod 166201589441944417) ^ 10808453498208 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (10 : ZMod 166201589441944417) ^ 931477152 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyER_258268827641370407 : Nat.Prime 258268827641370407 := by
  apply lucas_primality 258268827641370407 (7 : ZMod 258268827641370407)
  · rw [← oneHundredFiftyERFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 2), (19, 1), (138705063180113, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 2), (19, 1), (138705063180113, 1)] : List FactorBlock).map factorBlockValue).prod) = 258268827641370407 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyER_2
      · exact prime_oneHundredFiftyER_7
      · exact prime_oneHundredFiftyER_19
      · exact prime_oneHundredFiftyER_138705063180113
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 258268827641370407) ^ 129134413820685203 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (7 : ZMod 258268827641370407) ^ 36895546805910058 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (7 : ZMod 258268827641370407) ^ 13593096191651074 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (7 : ZMod 258268827641370407) ^ 1862 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyER_1129558801352365613 : Nat.Prime 1129558801352365613 := by
  apply lucas_primality 1129558801352365613 (2 : ZMod 1129558801352365613)
  · rw [← oneHundredFiftyERFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (229, 1), (8105401, 1), (152138407, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (229, 1), (8105401, 1), (152138407, 1)] : List FactorBlock).map factorBlockValue).prod) = 1129558801352365613 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyER_2
      · exact prime_oneHundredFiftyER_229
      · exact prime_oneHundredFiftyER_8105401
      · exact prime_oneHundredFiftyER_152138407
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1129558801352365613) ^ 564779400676182806 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 1129558801352365613) ^ 4932571184944828 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 1129558801352365613) ^ 139358780812 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 1129558801352365613) ^ 7424547316 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyER_2108574390836795111 : Nat.Prime 2108574390836795111 := by
  apply lucas_primality 2108574390836795111 (17 : ZMod 2108574390836795111)
  · rw [← oneHundredFiftyERFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (31, 1), (11059, 1), (615051349459, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (31, 1), (11059, 1), (615051349459, 1)] : List FactorBlock).map factorBlockValue).prod) = 2108574390836795111 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyER_2
      · exact prime_oneHundredFiftyER_5
      · exact prime_oneHundredFiftyER_31
      · exact prime_oneHundredFiftyER_11059
      · exact prime_oneHundredFiftyER_615051349459
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (17 : ZMod 2108574390836795111) ^ 1054287195418397555 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (17 : ZMod 2108574390836795111) ^ 421714878167359022 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (17 : ZMod 2108574390836795111) ^ 68018528736670810 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (17 : ZMod 2108574390836795111) ^ 190665918332290 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (17 : ZMod 2108574390836795111) ^ 3428290 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyER_2220502305087140441 : Nat.Prime 2220502305087140441 := by
  apply lucas_primality 2220502305087140441 (3 : ZMod 2220502305087140441)
  · rw [← oneHundredFiftyERFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (101, 1), (191, 1), (48017, 1), (59929613, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (101, 1), (191, 1), (48017, 1), (59929613, 1)] : List FactorBlock).map factorBlockValue).prod) = 2220502305087140441 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyER_2
      · exact prime_oneHundredFiftyER_5
      · exact prime_oneHundredFiftyER_101
      · exact prime_oneHundredFiftyER_191
      · exact prime_oneHundredFiftyER_48017
      · exact prime_oneHundredFiftyER_59929613
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 2220502305087140441) ^ 1110251152543570220 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (3 : ZMod 2220502305087140441) ^ 444100461017428088 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (3 : ZMod 2220502305087140441) ^ 21985171337496440 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (3 : ZMod 2220502305087140441) ^ 11625666518780840 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (3 : ZMod 2220502305087140441) ^ 46244086575320 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (3 : ZMod 2220502305087140441) ^ 37051837880 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyER_2356980392894937077 : Nat.Prime 2356980392894937077 := by
  apply lucas_primality 2356980392894937077 (2 : ZMod 2356980392894937077)
  · rw [← oneHundredFiftyERFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (1487, 1), (125183, 1), (3165480589, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (1487, 1), (125183, 1), (3165480589, 1)] : List FactorBlock).map factorBlockValue).prod) = 2356980392894937077 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyER_2
      · exact prime_oneHundredFiftyER_1487
      · exact prime_oneHundredFiftyER_125183
      · exact prime_oneHundredFiftyER_3165480589
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 2356980392894937077) ^ 1178490196447468538 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 2356980392894937077) ^ 1585057426291148 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 2356980392894937077) ^ 18828278543372 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 2356980392894937077) ^ 744588484 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyER_2410219617571552777 : Nat.Prime 2410219617571552777 := by
  apply lucas_primality 2410219617571552777 (10 : ZMod 2410219617571552777)
  · rw [← oneHundredFiftyERFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (11, 1), (19, 1), (47, 1), (10223538369013, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (11, 1), (19, 1), (47, 1), (10223538369013, 1)] : List FactorBlock).map factorBlockValue).prod) = 2410219617571552777 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyER_2
      · exact prime_oneHundredFiftyER_3
      · exact prime_oneHundredFiftyER_11
      · exact prime_oneHundredFiftyER_19
      · exact prime_oneHundredFiftyER_47
      · exact prime_oneHundredFiftyER_10223538369013
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 2410219617571552777) ^ 1205109808785776388 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (10 : ZMod 2410219617571552777) ^ 803406539190517592 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (10 : ZMod 2410219617571552777) ^ 219110874324686616 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (10 : ZMod 2410219617571552777) ^ 126853664082713304 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (10 : ZMod 2410219617571552777) ^ 51281268458969208 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (10 : ZMod 2410219617571552777) ^ 235752 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyER_2472719233313884279 : Nat.Prime 2472719233313884279 := by
  apply lucas_primality 2472719233313884279 (3 : ZMod 2472719233313884279)
  · rw [← oneHundredFiftyERFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (18973, 1), (21721386824381, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (18973, 1), (21721386824381, 1)] : List FactorBlock).map factorBlockValue).prod) = 2472719233313884279 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyER_2
      · exact prime_oneHundredFiftyER_3
      · exact prime_oneHundredFiftyER_18973
      · exact prime_oneHundredFiftyER_21721386824381
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 2472719233313884279) ^ 1236359616656942139 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (3 : ZMod 2472719233313884279) ^ 824239744437961426 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (3 : ZMod 2472719233313884279) ^ 130328320946286 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (3 : ZMod 2472719233313884279) ^ 113838 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyER_4527184655447032079 : Nat.Prime 4527184655447032079 := by
  apply lucas_primality 4527184655447032079 (7 : ZMod 4527184655447032079)
  · rw [← oneHundredFiftyERFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (23, 1), (5821, 1), (152597, 1), (110796689, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (23, 1), (5821, 1), (152597, 1), (110796689, 1)] : List FactorBlock).map factorBlockValue).prod) = 4527184655447032079 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyER_2
      · exact prime_oneHundredFiftyER_23
      · exact prime_oneHundredFiftyER_5821
      · exact prime_oneHundredFiftyER_152597
      · exact prime_oneHundredFiftyER_110796689
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 4527184655447032079) ^ 2263592327723516039 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (7 : ZMod 4527184655447032079) ^ 196834115454218786 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (7 : ZMod 4527184655447032079) ^ 777733148161318 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (7 : ZMod 4527184655447032079) ^ 29667586226774 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (7 : ZMod 4527184655447032079) ^ 40860288302 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyER_14461317705429316663 : Nat.Prime 14461317705429316663 := by
  apply lucas_primality 14461317705429316663 (3 : ZMod 14461317705429316663)
  · rw [← oneHundredFiftyERFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (2410219617571552777, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (2410219617571552777, 1)] : List FactorBlock).map factorBlockValue).prod) = 14461317705429316663 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyER_2
      · exact prime_oneHundredFiftyER_3
      · exact prime_oneHundredFiftyER_2410219617571552777
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 14461317705429316663) ^ 7230658852714658331 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (3 : ZMod 14461317705429316663) ^ 4820439235143105554 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (3 : ZMod 14461317705429316663) ^ 6 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyER_19096906877256609199 : Nat.Prime 19096906877256609199 := by
  apply lucas_primality 19096906877256609199 (6 : ZMod 19096906877256609199)
  · rw [← oneHundredFiftyERFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (7, 1), (53, 1), (6697657, 1), (426966413, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (7, 1), (53, 1), (6697657, 1), (426966413, 1)] : List FactorBlock).map factorBlockValue).prod) = 19096906877256609199 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyER_2
      · exact prime_oneHundredFiftyER_3
      · exact prime_oneHundredFiftyER_7
      · exact prime_oneHundredFiftyER_53
      · exact prime_oneHundredFiftyER_6697657
      · exact prime_oneHundredFiftyER_426966413
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 19096906877256609199) ^ 9548453438628304599 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (6 : ZMod 19096906877256609199) ^ 6365635625752203066 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (6 : ZMod 19096906877256609199) ^ 2728129553893801314 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (6 : ZMod 19096906877256609199) ^ 360318997684086966 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (6 : ZMod 19096906877256609199) ^ 2851281706014 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (6 : ZMod 19096906877256609199) ^ 44726953446 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyER_35782558080826260923 : Nat.Prime 35782558080826260923 := by
  apply lucas_primality 35782558080826260923 (2 : ZMod 35782558080826260923)
  · rw [← oneHundredFiftyERFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (335860201, 1), (53270018261, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (335860201, 1), (53270018261, 1)] : List FactorBlock).map factorBlockValue).prod) = 35782558080826260923 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyER_2
      · exact prime_oneHundredFiftyER_335860201
      · exact prime_oneHundredFiftyER_53270018261
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 35782558080826260923) ^ 17891279040413130461 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 35782558080826260923) ^ 106540036522 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 35782558080826260923) ^ 671720402 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyER_36265159998777480317 : Nat.Prime 36265159998777480317 := by
  apply lucas_primality 36265159998777480317 (5 : ZMod 36265159998777480317)
  · rw [← oneHundredFiftyERFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (13, 1), (29, 1), (73, 1), (47061672383657, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (13, 1), (29, 1), (73, 1), (47061672383657, 1)] : List FactorBlock).map factorBlockValue).prod) = 36265159998777480317 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyER_2
      · exact prime_oneHundredFiftyER_7
      · exact prime_oneHundredFiftyER_13
      · exact prime_oneHundredFiftyER_29
      · exact prime_oneHundredFiftyER_73
      · exact prime_oneHundredFiftyER_47061672383657
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 36265159998777480317) ^ 18132579999388740158 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (5 : ZMod 36265159998777480317) ^ 5180737142682497188 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (5 : ZMod 36265159998777480317) ^ 2789627692213652332 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (5 : ZMod 36265159998777480317) ^ 1250522758578533804 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (5 : ZMod 36265159998777480317) ^ 496783013681883292 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (5 : ZMod 36265159998777480317) ^ 770588 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyER_37600086952193652409 : Nat.Prime 37600086952193652409 := by
  apply lucas_primality 37600086952193652409 (7 : ZMod 37600086952193652409)
  · rw [← oneHundredFiftyERFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (6039659, 1), (259397143063, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (6039659, 1), (259397143063, 1)] : List FactorBlock).map factorBlockValue).prod) = 37600086952193652409 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyER_2
      · exact prime_oneHundredFiftyER_3
      · exact prime_oneHundredFiftyER_6039659
      · exact prime_oneHundredFiftyER_259397143063
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 37600086952193652409) ^ 18800043476096826204 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (7 : ZMod 37600086952193652409) ^ 12533362317397884136 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (7 : ZMod 37600086952193652409) ^ 6225531433512 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (7 : ZMod 37600086952193652409) ^ 144951816 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyER_41449211920200238027 : Nat.Prime 41449211920200238027 := by
  apply lucas_primality 41449211920200238027 (3 : ZMod 41449211920200238027)
  · rw [← oneHundredFiftyERFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (19, 1), (198637, 1), (1336579, 1), (1369483, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (19, 1), (198637, 1), (1336579, 1), (1369483, 1)] : List FactorBlock).map factorBlockValue).prod) = 41449211920200238027 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyER_2
      · exact prime_oneHundredFiftyER_3
      · exact prime_oneHundredFiftyER_19
      · exact prime_oneHundredFiftyER_198637
      · exact prime_oneHundredFiftyER_1336579
      · exact prime_oneHundredFiftyER_1369483
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 41449211920200238027) ^ 20724605960100119013 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (3 : ZMod 41449211920200238027) ^ 13816403973400079342 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (3 : ZMod 41449211920200238027) ^ 2181537469484223054 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (3 : ZMod 41449211920200238027) ^ 208668132926898 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (3 : ZMod 41449211920200238027) ^ 31011419392494 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (3 : ZMod 41449211920200238027) ^ 30266320881822 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyER_52354586721756688477 : Nat.Prime 52354586721756688477 := by
  apply lucas_primality 52354586721756688477 (2 : ZMod 52354586721756688477)
  · rw [← oneHundredFiftyERFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (19, 1), (53, 1), (151, 1), (1471, 1), (14843, 1), (1314113, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (19, 1), (53, 1), (151, 1), (1471, 1), (14843, 1), (1314113, 1)] : List FactorBlock).map factorBlockValue).prod) = 52354586721756688477 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyER_2
      · exact prime_oneHundredFiftyER_3
      · exact prime_oneHundredFiftyER_19
      · exact prime_oneHundredFiftyER_53
      · exact prime_oneHundredFiftyER_151
      · exact prime_oneHundredFiftyER_1471
      · exact prime_oneHundredFiftyER_14843
      · exact prime_oneHundredFiftyER_1314113
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 52354586721756688477) ^ 26177293360878344238 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 52354586721756688477) ^ 17451528907252229492 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 52354586721756688477) ^ 2755504564302983604 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 52354586721756688477) ^ 987822390976541292 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 52354586721756688477) ^ 346719117362627076 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 52354586721756688477) ^ 35591153447829156 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 52354586721756688477) ^ 3527224059944532 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 52354586721756688477) ^ 39840247164252 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyER_52983531609217552957 : Nat.Prime 52983531609217552957 := by
  apply lucas_primality 52983531609217552957 (5 : ZMod 52983531609217552957)
  · rw [← oneHundredFiftyERFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (2063, 1), (15269, 1), (140168308879, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (2063, 1), (15269, 1), (140168308879, 1)] : List FactorBlock).map factorBlockValue).prod) = 52983531609217552957 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyER_2
      · exact prime_oneHundredFiftyER_3
      · exact prime_oneHundredFiftyER_2063
      · exact prime_oneHundredFiftyER_15269
      · exact prime_oneHundredFiftyER_140168308879
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 52983531609217552957) ^ 26491765804608776478 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (5 : ZMod 52983531609217552957) ^ 17661177203072517652 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (5 : ZMod 52983531609217552957) ^ 25682758899281412 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (5 : ZMod 52983531609217552957) ^ 3470006654608524 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (5 : ZMod 52983531609217552957) ^ 377999364 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyER_77911803317743343159 : Nat.Prime 77911803317743343159 := by
  apply lucas_primality 77911803317743343159 (7 : ZMod 77911803317743343159)
  · rw [← oneHundredFiftyERFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (29411, 1), (189219299187727, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (29411, 1), (189219299187727, 1)] : List FactorBlock).map factorBlockValue).prod) = 77911803317743343159 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyER_2
      · exact prime_oneHundredFiftyER_7
      · exact prime_oneHundredFiftyER_29411
      · exact prime_oneHundredFiftyER_189219299187727
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 77911803317743343159) ^ 38955901658871671579 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (7 : ZMod 77911803317743343159) ^ 11130257616820477594 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (7 : ZMod 77911803317743343159) ^ 2649070188628178 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (7 : ZMod 77911803317743343159) ^ 411754 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyER_98102383559288524519 : Nat.Prime 98102383559288524519 := by
  apply lucas_primality 98102383559288524519 (3 : ZMod 98102383559288524519)
  · rw [← oneHundredFiftyERFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (17, 1), (61, 1), (83, 1), (189964067570743, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (17, 1), (61, 1), (83, 1), (189964067570743, 1)] : List FactorBlock).map factorBlockValue).prod) = 98102383559288524519 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyER_2
      · exact prime_oneHundredFiftyER_3
      · exact prime_oneHundredFiftyER_17
      · exact prime_oneHundredFiftyER_61
      · exact prime_oneHundredFiftyER_83
      · exact prime_oneHundredFiftyER_189964067570743
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 98102383559288524519) ^ 49051191779644262259 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (3 : ZMod 98102383559288524519) ^ 32700794519762841506 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (3 : ZMod 98102383559288524519) ^ 5770728444664030854 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (3 : ZMod 98102383559288524519) ^ 1608235796053910238 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (3 : ZMod 98102383559288524519) ^ 1181956428425162946 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (3 : ZMod 98102383559288524519) ^ 516426 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyER_142762338978465458017 : Nat.Prime 142762338978465458017 := by
  apply lucas_primality 142762338978465458017 (7 : ZMod 142762338978465458017)
  · rw [← oneHundredFiftyERFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 3), (165234188632483169, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 3), (165234188632483169, 1)] : List FactorBlock).map factorBlockValue).prod) = 142762338978465458017 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyER_2
      · exact prime_oneHundredFiftyER_3
      · exact prime_oneHundredFiftyER_165234188632483169
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 142762338978465458017) ^ 71381169489232729008 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (7 : ZMod 142762338978465458017) ^ 47587446326155152672 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (7 : ZMod 142762338978465458017) ^ 864 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyER_172236773115593411261 : Nat.Prime 172236773115593411261 := by
  apply lucas_primality 172236773115593411261 (2 : ZMod 172236773115593411261)
  · rw [← oneHundredFiftyERFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (7, 1), (29, 1), (79, 1), (241, 1), (40357, 1), (55212427, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (7, 1), (29, 1), (79, 1), (241, 1), (40357, 1), (55212427, 1)] : List FactorBlock).map factorBlockValue).prod) = 172236773115593411261 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyER_2
      · exact prime_oneHundredFiftyER_5
      · exact prime_oneHundredFiftyER_7
      · exact prime_oneHundredFiftyER_29
      · exact prime_oneHundredFiftyER_79
      · exact prime_oneHundredFiftyER_241
      · exact prime_oneHundredFiftyER_40357
      · exact prime_oneHundredFiftyER_55212427
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 172236773115593411261) ^ 86118386557796705630 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 172236773115593411261) ^ 34447354623118682252 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 172236773115593411261) ^ 24605253302227630180 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 172236773115593411261) ^ 5939199072951496940 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 172236773115593411261) ^ 2180212317918903940 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 172236773115593411261) ^ 714675407118644860 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 172236773115593411261) ^ 4267828954471180 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 172236773115593411261) ^ 3119529107380 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyER_221728109174929132697 : Nat.Prime 221728109174929132697 := by
  apply lucas_primality 221728109174929132697 (3 : ZMod 221728109174929132697)
  · rw [← oneHundredFiftyERFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (19, 1), (83, 1), (17575151329655131, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (19, 1), (83, 1), (17575151329655131, 1)] : List FactorBlock).map factorBlockValue).prod) = 221728109174929132697 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyER_2
      · exact prime_oneHundredFiftyER_19
      · exact prime_oneHundredFiftyER_83
      · exact prime_oneHundredFiftyER_17575151329655131
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 221728109174929132697) ^ 110864054587464566348 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (3 : ZMod 221728109174929132697) ^ 11669900482891006984 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (3 : ZMod 221728109174929132697) ^ 2671423002107579912 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (3 : ZMod 221728109174929132697) ^ 12616 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyER_256223811061086791179 : Nat.Prime 256223811061086791179 := by
  apply lucas_primality 256223811061086791179 (2 : ZMod 256223811061086791179)
  · rw [← oneHundredFiftyERFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (17, 1), (6863, 1), (366020420757353, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (17, 1), (6863, 1), (366020420757353, 1)] : List FactorBlock).map factorBlockValue).prod) = 256223811061086791179 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyER_2
      · exact prime_oneHundredFiftyER_3
      · exact prime_oneHundredFiftyER_17
      · exact prime_oneHundredFiftyER_6863
      · exact prime_oneHundredFiftyER_366020420757353
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 256223811061086791179) ^ 128111905530543395589 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 256223811061086791179) ^ 85407937020362263726 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 256223811061086791179) ^ 15071988885946281834 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 256223811061086791179) ^ 37334082917250006 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 256223811061086791179) ^ 700026 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyER_829821849978416232493 : Nat.Prime 829821849978416232493 := by
  apply lucas_primality 829821849978416232493 (5 : ZMod 829821849978416232493)
  · rw [← oneHundredFiftyERFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 4), (127, 1), (947, 1), (11437, 1), (1861975811, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 4), (127, 1), (947, 1), (11437, 1), (1861975811, 1)] : List FactorBlock).map factorBlockValue).prod) = 829821849978416232493 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyER_2
      · exact prime_oneHundredFiftyER_3
      · exact prime_oneHundredFiftyER_127
      · exact prime_oneHundredFiftyER_947
      · exact prime_oneHundredFiftyER_11437
      · exact prime_oneHundredFiftyER_1861975811
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 829821849978416232493) ^ 414910924989208116246 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (5 : ZMod 829821849978416232493) ^ 276607283326138744164 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (5 : ZMod 829821849978416232493) ^ 6534030314790678996 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (5 : ZMod 829821849978416232493) ^ 876263833134547236 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (5 : ZMod 829821849978416232493) ^ 72555901895463516 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (5 : ZMod 829821849978416232493) ^ 445667363172 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyER_877597476325376642987 : Nat.Prime 877597476325376642987 := by
  apply lucas_primality 877597476325376642987 (2 : ZMod 877597476325376642987)
  · rw [← oneHundredFiftyERFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (1699, 1), (258268827641370407, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (1699, 1), (258268827641370407, 1)] : List FactorBlock).map factorBlockValue).prod) = 877597476325376642987 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyER_2
      · exact prime_oneHundredFiftyER_1699
      · exact prime_oneHundredFiftyER_258268827641370407
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 877597476325376642987) ^ 438798738162688321493 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 877597476325376642987) ^ 516537655282740814 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 877597476325376642987) ^ 3398 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyER_1081687868363620552253 : Nat.Prime 1081687868363620552253 := by
  apply lucas_primality 1081687868363620552253 (2 : ZMod 1081687868363620552253)
  · rw [← oneHundredFiftyERFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (71, 1), (199, 1), (52864081, 1), (362051087, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (71, 1), (199, 1), (52864081, 1), (362051087, 1)] : List FactorBlock).map factorBlockValue).prod) = 1081687868363620552253 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyER_2
      · exact prime_oneHundredFiftyER_71
      · exact prime_oneHundredFiftyER_199
      · exact prime_oneHundredFiftyER_52864081
      · exact prime_oneHundredFiftyER_362051087
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1081687868363620552253) ^ 540843934181810276126 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 1081687868363620552253) ^ 15235040399487613412 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 1081687868363620552253) ^ 5435617428962917348 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 1081687868363620552253) ^ 20461679232892 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 1081687868363620552253) ^ 2987666401796 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyER_1205269042013298899237 : Nat.Prime 1205269042013298899237 := by
  apply lucas_primality 1205269042013298899237 (2 : ZMod 1205269042013298899237)
  · rw [← oneHundredFiftyERFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (23, 1), (1549, 1), (47713, 1), (341461, 1), (519119, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (23, 1), (1549, 1), (47713, 1), (341461, 1), (519119, 1)] : List FactorBlock).map factorBlockValue).prod) = 1205269042013298899237 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyER_2
      · exact prime_oneHundredFiftyER_23
      · exact prime_oneHundredFiftyER_1549
      · exact prime_oneHundredFiftyER_47713
      · exact prime_oneHundredFiftyER_341461
      · exact prime_oneHundredFiftyER_519119
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1205269042013298899237) ^ 602634521006649449618 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 1205269042013298899237) ^ 52403001826665169532 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 1205269042013298899237) ^ 778094927058294964 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 1205269042013298899237) ^ 25260810303550372 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 1205269042013298899237) ^ 3529741440496276 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 1205269042013298899237) ^ 2321758675782044 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyER_1631258631477497784079 : Nat.Prime 1631258631477497784079 := by
  apply lucas_primality 1631258631477497784079 (3 : ZMod 1631258631477497784079)
  · rw [← oneHundredFiftyERFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (15259, 1), (5939149323450269, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (15259, 1), (5939149323450269, 1)] : List FactorBlock).map factorBlockValue).prod) = 1631258631477497784079 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyER_2
      · exact prime_oneHundredFiftyER_3
      · exact prime_oneHundredFiftyER_15259
      · exact prime_oneHundredFiftyER_5939149323450269
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1631258631477497784079) ^ 815629315738748892039 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (3 : ZMod 1631258631477497784079) ^ 543752877159165928026 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (3 : ZMod 1631258631477497784079) ^ 106904687822104842 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (3 : ZMod 1631258631477497784079) ^ 274662 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyER_1827155873176070515703 : Nat.Prime 1827155873176070515703 := by
  apply lucas_primality 1827155873176070515703 (5 : ZMod 1827155873176070515703)
  · rw [← oneHundredFiftyERFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (17, 2), (33427, 1), (174481, 1), (41692589, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (17, 2), (33427, 1), (174481, 1), (41692589, 1)] : List FactorBlock).map factorBlockValue).prod) = 1827155873176070515703 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyER_2
      · exact prime_oneHundredFiftyER_13
      · exact prime_oneHundredFiftyER_17
      · exact prime_oneHundredFiftyER_33427
      · exact prime_oneHundredFiftyER_174481
      · exact prime_oneHundredFiftyER_41692589
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 1827155873176070515703) ^ 913577936588035257851 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (5 : ZMod 1827155873176070515703) ^ 140550451782774655054 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (5 : ZMod 1827155873176070515703) ^ 107479757245651206806 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (5 : ZMod 1827155873176070515703) ^ 54661078564515826 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (5 : ZMod 1827155873176070515703) ^ 10471947508187542 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (5 : ZMod 1827155873176070515703) ^ 43824476171918 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyER_2143658149365335926627 : Nat.Prime 2143658149365335926627 := by
  apply lucas_primality 2143658149365335926627 (2 : ZMod 2143658149365335926627)
  · rw [← oneHundredFiftyERFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (1061, 1), (112245164381890037, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (1061, 1), (112245164381890037, 1)] : List FactorBlock).map factorBlockValue).prod) = 2143658149365335926627 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyER_2
      · exact prime_oneHundredFiftyER_3
      · exact prime_oneHundredFiftyER_1061
      · exact prime_oneHundredFiftyER_112245164381890037
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 2143658149365335926627) ^ 1071829074682667963313 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 2143658149365335926627) ^ 714552716455111975542 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 2143658149365335926627) ^ 2020412958874020666 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 2143658149365335926627) ^ 19098 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyER_2307642263509371299503 : Nat.Prime 2307642263509371299503 := by
  apply lucas_primality 2307642263509371299503 (5 : ZMod 2307642263509371299503)
  · rw [← oneHundredFiftyERFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (31, 1), (59, 1), (77041, 1), (2729490688553, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (31, 1), (59, 1), (77041, 1), (2729490688553, 1)] : List FactorBlock).map factorBlockValue).prod) = 2307642263509371299503 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyER_2
      · exact prime_oneHundredFiftyER_3
      · exact prime_oneHundredFiftyER_31
      · exact prime_oneHundredFiftyER_59
      · exact prime_oneHundredFiftyER_77041
      · exact prime_oneHundredFiftyER_2729490688553
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 2307642263509371299503) ^ 1153821131754685649751 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (5 : ZMod 2307642263509371299503) ^ 769214087836457099834 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (5 : ZMod 2307642263509371299503) ^ 74440073016431332242 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (5 : ZMod 2307642263509371299503) ^ 39112580737446971178 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (5 : ZMod 2307642263509371299503) ^ 29953430816180622 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (5 : ZMod 2307642263509371299503) ^ 845447934 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyER_3019418713742564280571 : Nat.Prime 3019418713742564280571 := by
  apply lucas_primality 3019418713742564280571 (10 : ZMod 3019418713742564280571)
  · rw [← oneHundredFiftyERFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (97, 1), (4671071, 1), (222133410637, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (97, 1), (4671071, 1), (222133410637, 1)] : List FactorBlock).map factorBlockValue).prod) = 3019418713742564280571 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyER_2
      · exact prime_oneHundredFiftyER_3
      · exact prime_oneHundredFiftyER_5
      · exact prime_oneHundredFiftyER_97
      · exact prime_oneHundredFiftyER_4671071
      · exact prime_oneHundredFiftyER_222133410637
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 3019418713742564280571) ^ 1509709356871282140285 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (10 : ZMod 3019418713742564280571) ^ 1006472904580854760190 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (10 : ZMod 3019418713742564280571) ^ 603883742748512856114 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (10 : ZMod 3019418713742564280571) ^ 31128027976727466810 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (10 : ZMod 3019418713742564280571) ^ 646408224953670 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (10 : ZMod 3019418713742564280571) ^ 13592816610 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyER_3074685732733041494149 : Nat.Prime 3074685732733041494149 := by
  apply lucas_primality 3074685732733041494149 (2 : ZMod 3074685732733041494149)
  · rw [← oneHundredFiftyERFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (256223811061086791179, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (256223811061086791179, 1)] : List FactorBlock).map factorBlockValue).prod) = 3074685732733041494149 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyER_2
      · exact prime_oneHundredFiftyER_3
      · exact prime_oneHundredFiftyER_256223811061086791179
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 3074685732733041494149) ^ 1537342866366520747074 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 3074685732733041494149) ^ 1024895244244347164716 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 3074685732733041494149) ^ 12 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyER_3159922268410800013747 : Nat.Prime 3159922268410800013747 := by
  apply lucas_primality 3159922268410800013747 (3 : ZMod 3159922268410800013747)
  · rw [← oneHundredFiftyERFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (113, 1), (4621, 1), (112064543828663, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (113, 1), (4621, 1), (112064543828663, 1)] : List FactorBlock).map factorBlockValue).prod) = 3159922268410800013747 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyER_2
      · exact prime_oneHundredFiftyER_3
      · exact prime_oneHundredFiftyER_113
      · exact prime_oneHundredFiftyER_4621
      · exact prime_oneHundredFiftyER_112064543828663
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 3159922268410800013747) ^ 1579961134205400006873 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (3 : ZMod 3159922268410800013747) ^ 1053307422803600004582 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (3 : ZMod 3159922268410800013747) ^ 27963913879741593042 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (3 : ZMod 3159922268410800013747) ^ 683817846442501626 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (3 : ZMod 3159922268410800013747) ^ 28197342 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyER_7389175414818054990001 : Nat.Prime 7389175414818054990001 := by
  apply lucas_primality 7389175414818054990001 (17 : ZMod 7389175414818054990001)
  · rw [← oneHundredFiftyERFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (5, 4), (11, 1), (433, 1), (51712334066891, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (5, 4), (11, 1), (433, 1), (51712334066891, 1)] : List FactorBlock).map factorBlockValue).prod) = 7389175414818054990001 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyER_2
      · exact prime_oneHundredFiftyER_3
      · exact prime_oneHundredFiftyER_5
      · exact prime_oneHundredFiftyER_11
      · exact prime_oneHundredFiftyER_433
      · exact prime_oneHundredFiftyER_51712334066891
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (17 : ZMod 7389175414818054990001) ^ 3694587707409027495000 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (17 : ZMod 7389175414818054990001) ^ 2463058471606018330000 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (17 : ZMod 7389175414818054990001) ^ 1477835082963610998000 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (17 : ZMod 7389175414818054990001) ^ 671743219528914090000 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (17 : ZMod 7389175414818054990001) ^ 17065070242074030000 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (17 : ZMod 7389175414818054990001) ^ 142890000 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyER_8993759679696815118617 : Nat.Prime 8993759679696815118617 := by
  apply lucas_primality 8993759679696815118617 (3 : ZMod 8993759679696815118617)
  · rw [← oneHundredFiftyERFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (31, 1), (36265159998777480317, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (31, 1), (36265159998777480317, 1)] : List FactorBlock).map factorBlockValue).prod) = 8993759679696815118617 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyER_2
      · exact prime_oneHundredFiftyER_31
      · exact prime_oneHundredFiftyER_36265159998777480317
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 8993759679696815118617) ^ 4496879839848407559308 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (3 : ZMod 8993759679696815118617) ^ 290121279990219842536 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (3 : ZMod 8993759679696815118617) ^ 248 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyER_10168288329773995248227 : Nat.Prime 10168288329773995248227 := by
  apply lucas_primality 10168288329773995248227 (2 : ZMod 10168288329773995248227)
  · rw [← oneHundredFiftyERFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (643, 1), (1129558801352365613, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (643, 1), (1129558801352365613, 1)] : List FactorBlock).map factorBlockValue).prod) = 10168288329773995248227 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyER_2
      · exact prime_oneHundredFiftyER_7
      · exact prime_oneHundredFiftyER_643
      · exact prime_oneHundredFiftyER_1129558801352365613
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 10168288329773995248227) ^ 5084144164886997624113 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 10168288329773995248227) ^ 1452612618539142178318 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 10168288329773995248227) ^ 15813823218933118582 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 10168288329773995248227) ^ 9002 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyER_13256972514058216452869 : Nat.Prime 13256972514058216452869 := by
  apply lucas_primality 13256972514058216452869 (2 : ZMod 13256972514058216452869)
  · rw [← oneHundredFiftyERFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (82829821, 1), (40012680077077, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (82829821, 1), (40012680077077, 1)] : List FactorBlock).map factorBlockValue).prod) = 13256972514058216452869 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyER_2
      · exact prime_oneHundredFiftyER_82829821
      · exact prime_oneHundredFiftyER_40012680077077
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 13256972514058216452869) ^ 6628486257029108226434 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 13256972514058216452869) ^ 160050720308308 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 13256972514058216452869) ^ 331319284 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyER_13648309482050318656237 : Nat.Prime 13648309482050318656237 := by
  apply lucas_primality 13648309482050318656237 (2 : ZMod 13648309482050318656237)
  · rw [← oneHundredFiftyERFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (10499, 1), (25717303, 1), (4212348149, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (10499, 1), (25717303, 1), (4212348149, 1)] : List FactorBlock).map factorBlockValue).prod) = 13648309482050318656237 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyER_2
      · exact prime_oneHundredFiftyER_3
      · exact prime_oneHundredFiftyER_10499
      · exact prime_oneHundredFiftyER_25717303
      · exact prime_oneHundredFiftyER_4212348149
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 13648309482050318656237) ^ 6824154741025159328118 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 13648309482050318656237) ^ 4549436494016772885412 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 13648309482050318656237) ^ 1299962804271865764 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 13648309482050318656237) ^ 530705318596212 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 13648309482050318656237) ^ 3240071570364 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyER_15923379646956395154271 : Nat.Prime 15923379646956395154271 := by
  apply lucas_primality 15923379646956395154271 (6 : ZMod 15923379646956395154271)
  · rw [← oneHundredFiftyERFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (23, 1), (765941959, 1), (30129387137, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (23, 1), (765941959, 1), (30129387137, 1)] : List FactorBlock).map factorBlockValue).prod) = 15923379646956395154271 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyER_2
      · exact prime_oneHundredFiftyER_3
      · exact prime_oneHundredFiftyER_5
      · exact prime_oneHundredFiftyER_23
      · exact prime_oneHundredFiftyER_765941959
      · exact prime_oneHundredFiftyER_30129387137
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 15923379646956395154271) ^ 7961689823478197577135 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (6 : ZMod 15923379646956395154271) ^ 5307793215652131718090 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (6 : ZMod 15923379646956395154271) ^ 3184675929391279030854 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (6 : ZMod 15923379646956395154271) ^ 692320854215495441490 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (6 : ZMod 15923379646956395154271) ^ 20789277124530 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (6 : ZMod 15923379646956395154271) ^ 528499951710 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyER_38788105438584679319431 : Nat.Prime 38788105438584679319431 := by
  apply lucas_primality 38788105438584679319431 (3 : ZMod 38788105438584679319431)
  · rw [← oneHundredFiftyERFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (2834047, 1), (456215739524723, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (2834047, 1), (456215739524723, 1)] : List FactorBlock).map factorBlockValue).prod) = 38788105438584679319431 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyER_2
      · exact prime_oneHundredFiftyER_3
      · exact prime_oneHundredFiftyER_5
      · exact prime_oneHundredFiftyER_2834047
      · exact prime_oneHundredFiftyER_456215739524723
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 38788105438584679319431) ^ 19394052719292339659715 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (3 : ZMod 38788105438584679319431) ^ 12929368479528226439810 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (3 : ZMod 38788105438584679319431) ^ 7757621087716935863886 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (3 : ZMod 38788105438584679319431) ^ 13686472185741690 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (3 : ZMod 38788105438584679319431) ^ 85021410 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyER_65209761317544108371111 : Nat.Prime 65209761317544108371111 := by
  apply lucas_primality 65209761317544108371111 (11 : ZMod 65209761317544108371111)
  · rw [← oneHundredFiftyERFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (43, 1), (97, 1), (30491, 1), (51274419565151, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (43, 1), (97, 1), (30491, 1), (51274419565151, 1)] : List FactorBlock).map factorBlockValue).prod) = 65209761317544108371111 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyER_2
      · exact prime_oneHundredFiftyER_5
      · exact prime_oneHundredFiftyER_43
      · exact prime_oneHundredFiftyER_97
      · exact prime_oneHundredFiftyER_30491
      · exact prime_oneHundredFiftyER_51274419565151
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 65209761317544108371111) ^ 32604880658772054185555 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (11 : ZMod 65209761317544108371111) ^ 13041952263508821674222 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (11 : ZMod 65209761317544108371111) ^ 1516506077152188566770 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (11 : ZMod 65209761317544108371111) ^ 672265580593238230630 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (11 : ZMod 65209761317544108371111) ^ 2138656040062448210 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (11 : ZMod 65209761317544108371111) ^ 1271779610 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyER_77347805818148234432941 : Nat.Prime 77347805818148234432941 := by
  apply lucas_primality 77347805818148234432941 (2 : ZMod 77347805818148234432941)
  · rw [← oneHundredFiftyERFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (17, 1), (67, 1), (1151, 1), (983326402410041, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (17, 1), (67, 1), (1151, 1), (983326402410041, 1)] : List FactorBlock).map factorBlockValue).prod) = 77347805818148234432941 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyER_2
      · exact prime_oneHundredFiftyER_3
      · exact prime_oneHundredFiftyER_5
      · exact prime_oneHundredFiftyER_17
      · exact prime_oneHundredFiftyER_67
      · exact prime_oneHundredFiftyER_1151
      · exact prime_oneHundredFiftyER_983326402410041
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 77347805818148234432941) ^ 38673902909074117216470 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 77347805818148234432941) ^ 25782601939382744810980 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 77347805818148234432941) ^ 15469561163629646886588 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 77347805818148234432941) ^ 4549870930479307907820 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 77347805818148234432941) ^ 1154444862957436334820 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 77347805818148234432941) ^ 67200526340702201940 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 77347805818148234432941) ^ 78659340 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyER_85148937446427031458481 : Nat.Prime 85148937446427031458481 := by
  apply lucas_primality 85148937446427031458481 (13 : ZMod 85148937446427031458481)
  · rw [← oneHundredFiftyERFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (5, 1), (71, 1), (62903, 1), (79439825942629, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (5, 1), (71, 1), (62903, 1), (79439825942629, 1)] : List FactorBlock).map factorBlockValue).prod) = 85148937446427031458481 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyER_2
      · exact prime_oneHundredFiftyER_3
      · exact prime_oneHundredFiftyER_5
      · exact prime_oneHundredFiftyER_71
      · exact prime_oneHundredFiftyER_62903
      · exact prime_oneHundredFiftyER_79439825942629
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 85148937446427031458481) ^ 42574468723213515729240 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (13 : ZMod 85148937446427031458481) ^ 28382979148809010486160 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (13 : ZMod 85148937446427031458481) ^ 17029787489285406291696 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (13 : ZMod 85148937446427031458481) ^ 1199280809104606076880 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (13 : ZMod 85148937446427031458481) ^ 1353654634062398160 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (13 : ZMod 85148937446427031458481) ^ 1071867120 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyER_110508825696209439627199 : Nat.Prime 110508825696209439627199 := by
  apply lucas_primality 110508825696209439627199 (11 : ZMod 110508825696209439627199)
  · rw [← oneHundredFiftyERFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 2), (31, 1), (593, 1), (1924837, 1), (10622806927, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 2), (31, 1), (593, 1), (1924837, 1), (10622806927, 1)] : List FactorBlock).map factorBlockValue).prod) = 110508825696209439627199 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyER_2
      · exact prime_oneHundredFiftyER_3
      · exact prime_oneHundredFiftyER_7
      · exact prime_oneHundredFiftyER_31
      · exact prime_oneHundredFiftyER_593
      · exact prime_oneHundredFiftyER_1924837
      · exact prime_oneHundredFiftyER_10622806927
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 110508825696209439627199) ^ 55254412848104719813599 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (11 : ZMod 110508825696209439627199) ^ 36836275232069813209066 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (11 : ZMod 110508825696209439627199) ^ 15786975099458491375314 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (11 : ZMod 110508825696209439627199) ^ 3564800828909981923458 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (11 : ZMod 110508825696209439627199) ^ 186355523939644923486 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (11 : ZMod 110508825696209439627199) ^ 57412043563278054 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (11 : ZMod 110508825696209439627199) ^ 10402977899874 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyER_122240495837953388238407 : Nat.Prime 122240495837953388238407 := by
  apply lucas_primality 122240495837953388238407 (5 : ZMod 122240495837953388238407)
  · rw [← oneHundredFiftyERFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (17, 1), (47, 1), (79, 1), (138328986999972149, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (17, 1), (47, 1), (79, 1), (138328986999972149, 1)] : List FactorBlock).map factorBlockValue).prod) = 122240495837953388238407 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyER_2
      · exact prime_oneHundredFiftyER_7
      · exact prime_oneHundredFiftyER_17
      · exact prime_oneHundredFiftyER_47
      · exact prime_oneHundredFiftyER_79
      · exact prime_oneHundredFiftyER_138328986999972149
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 122240495837953388238407) ^ 61120247918976694119203 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (5 : ZMod 122240495837953388238407) ^ 17462927976850484034058 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (5 : ZMod 122240495837953388238407) ^ 7190617402232552249318 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (5 : ZMod 122240495837953388238407) ^ 2600861613573476345498 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (5 : ZMod 122240495837953388238407) ^ 1547348048581688458714 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (5 : ZMod 122240495837953388238407) ^ 883694 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyER_142356036616835933475179 : Nat.Prime 142356036616835933475179 := by
  apply lucas_primality 142356036616835933475179 (6 : ZMod 142356036616835933475179)
  · rw [← oneHundredFiftyERFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (10168288329773995248227, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (10168288329773995248227, 1)] : List FactorBlock).map factorBlockValue).prod) = 142356036616835933475179 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyER_2
      · exact prime_oneHundredFiftyER_7
      · exact prime_oneHundredFiftyER_10168288329773995248227
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (6 : ZMod 142356036616835933475179) ^ 71178018308417966737589 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (6 : ZMod 142356036616835933475179) ^ 20336576659547990496454 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (6 : ZMod 142356036616835933475179) ^ 14 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyER_220926376510877967446197 : Nat.Prime 220926376510877967446197 := by
  apply lucas_primality 220926376510877967446197 (2 : ZMod 220926376510877967446197)
  · rw [← oneHundredFiftyERFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (17, 1), (23, 1), (1493, 1), (3697, 1), (2843538109751, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (17, 1), (23, 1), (1493, 1), (3697, 1), (2843538109751, 1)] : List FactorBlock).map factorBlockValue).prod) = 220926376510877967446197 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyER_2
      · exact prime_oneHundredFiftyER_3
      · exact prime_oneHundredFiftyER_17
      · exact prime_oneHundredFiftyER_23
      · exact prime_oneHundredFiftyER_1493
      · exact prime_oneHundredFiftyER_3697
      · exact prime_oneHundredFiftyER_2843538109751
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 220926376510877967446197) ^ 110463188255438983723098 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 220926376510877967446197) ^ 73642125503625989148732 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 220926376510877967446197) ^ 12995669206522233379188 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 220926376510877967446197) ^ 9605494630907737715052 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 220926376510877967446197) ^ 147974800074265215972 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 220926376510877967446197) ^ 59758284152252628468 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 220926376510877967446197) ^ 77694185196 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyER_259193266026634557332219 : Nat.Prime 259193266026634557332219 := by
  apply lucas_primality 259193266026634557332219 (2 : ZMod 259193266026634557332219)
  · rw [← oneHundredFiftyERFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 3), (71, 1), (19471, 1), (273308408322643, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 3), (71, 1), (19471, 1), (273308408322643, 1)] : List FactorBlock).map factorBlockValue).prod) = 259193266026634557332219 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyER_2
      · exact prime_oneHundredFiftyER_7
      · exact prime_oneHundredFiftyER_71
      · exact prime_oneHundredFiftyER_19471
      · exact prime_oneHundredFiftyER_273308408322643
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 259193266026634557332219) ^ 129596633013317278666109 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 259193266026634557332219) ^ 37027609432376365333174 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 259193266026634557332219) ^ 3650609380656824751158 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 259193266026634557332219) ^ 13311759335762649958 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 259193266026634557332219) ^ 948354526 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyER_260096876484693775549819 : Nat.Prime 260096876484693775549819 := by
  apply lucas_primality 260096876484693775549819 (10 : ZMod 260096876484693775549819)
  · rw [← oneHundredFiftyERFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (31, 1), (37, 1), (61, 1), (691381, 1), (896134490989, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (31, 1), (37, 1), (61, 1), (691381, 1), (896134490989, 1)] : List FactorBlock).map factorBlockValue).prod) = 260096876484693775549819 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyER_2
      · exact prime_oneHundredFiftyER_3
      · exact prime_oneHundredFiftyER_31
      · exact prime_oneHundredFiftyER_37
      · exact prime_oneHundredFiftyER_61
      · exact prime_oneHundredFiftyER_691381
      · exact prime_oneHundredFiftyER_896134490989
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 260096876484693775549819) ^ 130048438242346887774909 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (10 : ZMod 260096876484693775549819) ^ 86698958828231258516606 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (10 : ZMod 260096876484693775549819) ^ 8390221822086895985478 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (10 : ZMod 260096876484693775549819) ^ 7029645310397129068914 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (10 : ZMod 260096876484693775549819) ^ 4263883221060553697538 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (10 : ZMod 260096876484693775549819) ^ 376199051586164178 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (10 : ZMod 260096876484693775549819) ^ 290243126562 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyER_558426407371653470016797 : Nat.Prime 558426407371653470016797 := by
  apply lucas_primality 558426407371653470016797 (2 : ZMod 558426407371653470016797)
  · rw [← oneHundredFiftyERFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (11, 1), (13, 1), (463, 1), (2108574390836795111, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (11, 1), (13, 1), (463, 1), (2108574390836795111, 1)] : List FactorBlock).map factorBlockValue).prod) = 558426407371653470016797 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyER_2
      · exact prime_oneHundredFiftyER_11
      · exact prime_oneHundredFiftyER_13
      · exact prime_oneHundredFiftyER_463
      · exact prime_oneHundredFiftyER_2108574390836795111
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 558426407371653470016797) ^ 279213203685826735008398 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 558426407371653470016797) ^ 50766037033786679092436 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 558426407371653470016797) ^ 42955877490127190001292 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 558426407371653470016797) ^ 1206104551558646803492 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 558426407371653470016797) ^ 264836 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyER_700038418875941420550763 : Nat.Prime 700038418875941420550763 := by
  apply lucas_primality 700038418875941420550763 (2 : ZMod 700038418875941420550763)
  · rw [← oneHundredFiftyERFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (29, 1), (107, 1), (37600086952193652409, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (29, 1), (107, 1), (37600086952193652409, 1)] : List FactorBlock).map factorBlockValue).prod) = 700038418875941420550763 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyER_2
      · exact prime_oneHundredFiftyER_3
      · exact prime_oneHundredFiftyER_29
      · exact prime_oneHundredFiftyER_107
      · exact prime_oneHundredFiftyER_37600086952193652409
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 700038418875941420550763) ^ 350019209437970710275381 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 700038418875941420550763) ^ 233346139625313806850254 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 700038418875941420550763) ^ 24139255823308324846578 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 700038418875941420550763) ^ 6542415129681695519166 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 700038418875941420550763) ^ 18618 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyER_878899926231809511221431 : Nat.Prime 878899926231809511221431 := by
  apply lucas_primality 878899926231809511221431 (6 : ZMod 878899926231809511221431)
  · rw [← oneHundredFiftyERFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (7, 1), (797, 1), (125287, 1), (13971226936099, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (7, 1), (797, 1), (125287, 1), (13971226936099, 1)] : List FactorBlock).map factorBlockValue).prod) = 878899926231809511221431 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyER_2
      · exact prime_oneHundredFiftyER_3
      · exact prime_oneHundredFiftyER_5
      · exact prime_oneHundredFiftyER_7
      · exact prime_oneHundredFiftyER_797
      · exact prime_oneHundredFiftyER_125287
      · exact prime_oneHundredFiftyER_13971226936099
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 878899926231809511221431) ^ 439449963115904755610715 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (6 : ZMod 878899926231809511221431) ^ 292966642077269837073810 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (6 : ZMod 878899926231809511221431) ^ 175779985246361902244286 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (6 : ZMod 878899926231809511221431) ^ 125557132318829930174490 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (6 : ZMod 878899926231809511221431) ^ 1102760258760112310190 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (6 : ZMod 878899926231809511221431) ^ 7015092756884668890 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (6 : ZMod 878899926231809511221431) ^ 62907855570 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyER_1085817348432706547272319 : Nat.Prime 1085817348432706547272319 := by
  apply lucas_primality 1085817348432706547272319 (11 : ZMod 1085817348432706547272319)
  · rw [← oneHundredFiftyERFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (19, 1), (1983853, 1), (5730737, 1), (228486491, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (19, 1), (1983853, 1), (5730737, 1), (228486491, 1)] : List FactorBlock).map factorBlockValue).prod) = 1085817348432706547272319 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyER_2
      · exact prime_oneHundredFiftyER_11
      · exact prime_oneHundredFiftyER_19
      · exact prime_oneHundredFiftyER_1983853
      · exact prime_oneHundredFiftyER_5730737
      · exact prime_oneHundredFiftyER_228486491
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 1085817348432706547272319) ^ 542908674216353273636159 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (11 : ZMod 1085817348432706547272319) ^ 98710668039336958842938 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (11 : ZMod 1085817348432706547272319) ^ 57148281496458239330122 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (11 : ZMod 1085817348432706547272319) ^ 547327522973076406 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (11 : ZMod 1085817348432706547272319) ^ 189472549243266014 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (11 : ZMod 1085817348432706547272319) ^ 4752216832078298 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyER_1654692673740117604332247 : Nat.Prime 1654692673740117604332247 := by
  apply lucas_primality 1654692673740117604332247 (6 : ZMod 1654692673740117604332247)
  · rw [← oneHundredFiftyERFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (13, 1), (73, 1), (131893, 1), (734440943417771, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (13, 1), (73, 1), (131893, 1), (734440943417771, 1)] : List FactorBlock).map factorBlockValue).prod) = 1654692673740117604332247 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyER_2
      · exact prime_oneHundredFiftyER_3
      · exact prime_oneHundredFiftyER_13
      · exact prime_oneHundredFiftyER_73
      · exact prime_oneHundredFiftyER_131893
      · exact prime_oneHundredFiftyER_734440943417771
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 1654692673740117604332247) ^ 827346336870058802166123 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (6 : ZMod 1654692673740117604332247) ^ 551564224580039201444082 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (6 : ZMod 1654692673740117604332247) ^ 127284051826162892640942 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (6 : ZMod 1654692673740117604332247) ^ 22667022927946816497702 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (6 : ZMod 1654692673740117604332247) ^ 12545720195462364222 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (6 : ZMod 1654692673740117604332247) ^ 2252996226 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyER_3794262449248451274667927 : Nat.Prime 3794262449248451274667927 := by
  apply lucas_primality 3794262449248451274667927 (3 : ZMod 3794262449248451274667927)
  · rw [← oneHundredFiftyERFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (43, 1), (67, 1), (926657, 1), (236872066185113, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (43, 1), (67, 1), (926657, 1), (236872066185113, 1)] : List FactorBlock).map factorBlockValue).prod) = 3794262449248451274667927 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyER_2
      · exact prime_oneHundredFiftyER_3
      · exact prime_oneHundredFiftyER_43
      · exact prime_oneHundredFiftyER_67
      · exact prime_oneHundredFiftyER_926657
      · exact prime_oneHundredFiftyER_236872066185113
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 3794262449248451274667927) ^ 1897131224624225637333963 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (3 : ZMod 3794262449248451274667927) ^ 1264754149749483758222642 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (3 : ZMod 3794262449248451274667927) ^ 88238661610429099410882 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (3 : ZMod 3794262449248451274667927) ^ 56630782824603750368178 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (3 : ZMod 3794262449248451274667927) ^ 4094570536075863318 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (3 : ZMod 3794262449248451274667927) ^ 16018192902 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyER_6375239336212509045788699 : Nat.Prime 6375239336212509045788699 := by
  apply lucas_primality 6375239336212509045788699 (2 : ZMod 6375239336212509045788699)
  · rw [← oneHundredFiftyERFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (1487, 1), (2143658149365335926627, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (1487, 1), (2143658149365335926627, 1)] : List FactorBlock).map factorBlockValue).prod) = 6375239336212509045788699 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyER_2
      · exact prime_oneHundredFiftyER_1487
      · exact prime_oneHundredFiftyER_2143658149365335926627
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 6375239336212509045788699) ^ 3187619668106254522894349 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 6375239336212509045788699) ^ 4287316298730671853254 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 6375239336212509045788699) ^ 2974 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyER_6471319245928454390844557 : Nat.Prime 6471319245928454390844557 := by
  apply lucas_primality 6471319245928454390844557 (2 : ZMod 6471319245928454390844557)
  · rw [← oneHundredFiftyERFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (19, 1), (85148937446427031458481, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (19, 1), (85148937446427031458481, 1)] : List FactorBlock).map factorBlockValue).prod) = 6471319245928454390844557 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyER_2
      · exact prime_oneHundredFiftyER_19
      · exact prime_oneHundredFiftyER_85148937446427031458481
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 6471319245928454390844557) ^ 3235659622964227195422278 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 6471319245928454390844557) ^ 340595749785708125833924 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 6471319245928454390844557) ^ 76 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyER_8268757057650177839637443 : Nat.Prime 8268757057650177839637443 := by
  apply lucas_primality 8268757057650177839637443 (2 : ZMod 8268757057650177839637443)
  · rw [← oneHundredFiftyERFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 1), (23, 1), (3463, 1), (1090151, 1), (2800878888487, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 1), (23, 1), (3463, 1), (1090151, 1), (2800878888487, 1)] : List FactorBlock).map factorBlockValue).prod) = 8268757057650177839637443 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyER_2
      · exact prime_oneHundredFiftyER_17
      · exact prime_oneHundredFiftyER_23
      · exact prime_oneHundredFiftyER_3463
      · exact prime_oneHundredFiftyER_1090151
      · exact prime_oneHundredFiftyER_2800878888487
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 8268757057650177839637443) ^ 4134378528825088919818721 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 8268757057650177839637443) ^ 486397473979422225861026 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 8268757057650177839637443) ^ 359511176419572949549454 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 8268757057650177839637443) ^ 2387743880349459381934 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 8268757057650177839637443) ^ 7584964888029436142 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 8268757057650177839637443) ^ 2952200857966 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyER_14696281811172898328226091 : Nat.Prime 14696281811172898328226091 := by
  apply lucas_primality 14696281811172898328226091 (2 : ZMod 14696281811172898328226091)
  · rw [← oneHundredFiftyERFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (79, 1), (409, 1), (619, 1), (41291881, 1), (593171807, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (79, 1), (409, 1), (619, 1), (41291881, 1), (593171807, 1)] : List FactorBlock).map factorBlockValue).prod) = 14696281811172898328226091 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyER_2
      · exact prime_oneHundredFiftyER_3
      · exact prime_oneHundredFiftyER_5
      · exact prime_oneHundredFiftyER_79
      · exact prime_oneHundredFiftyER_409
      · exact prime_oneHundredFiftyER_619
      · exact prime_oneHundredFiftyER_41291881
      · exact prime_oneHundredFiftyER_593171807
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 14696281811172898328226091) ^ 7348140905586449164113045 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 14696281811172898328226091) ^ 4898760603724299442742030 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 14696281811172898328226091) ^ 2939256362234579665645218 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 14696281811172898328226091) ^ 186028883685732890230710 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 14696281811172898328226091) ^ 35932229367170900558010 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 14696281811172898328226091) ^ 23741973846805974682110 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 14696281811172898328226091) ^ 355912141933492890 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 14696281811172898328226091) ^ 24775759127022870 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyER_15201442878057891661812467 : Nat.Prime 15201442878057891661812467 := by
  apply lucas_primality 15201442878057891661812467 (2 : ZMod 15201442878057891661812467)
  · rw [← oneHundredFiftyERFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (1085817348432706547272319, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (1085817348432706547272319, 1)] : List FactorBlock).map factorBlockValue).prod) = 15201442878057891661812467 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyER_2
      · exact prime_oneHundredFiftyER_7
      · exact prime_oneHundredFiftyER_1085817348432706547272319
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 15201442878057891661812467) ^ 7600721439028945830906233 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 15201442878057891661812467) ^ 2171634696865413094544638 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 15201442878057891661812467) ^ 14 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyER_24430366801959410955600529 : Nat.Prime 24430366801959410955600529 := by
  apply lucas_primality 24430366801959410955600529 (17 : ZMod 24430366801959410955600529)
  · rw [← oneHundredFiftyERFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (283, 1), (266797, 1), (3095341, 1), (2177774321, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (283, 1), (266797, 1), (3095341, 1), (2177774321, 1)] : List FactorBlock).map factorBlockValue).prod) = 24430366801959410955600529 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyER_2
      · exact prime_oneHundredFiftyER_3
      · exact prime_oneHundredFiftyER_283
      · exact prime_oneHundredFiftyER_266797
      · exact prime_oneHundredFiftyER_3095341
      · exact prime_oneHundredFiftyER_2177774321
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (17 : ZMod 24430366801959410955600529) ^ 12215183400979705477800264 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (17 : ZMod 24430366801959410955600529) ^ 8143455600653136985200176 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (17 : ZMod 24430366801959410955600529) ^ 86326384459220533412016 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (17 : ZMod 24430366801959410955600529) ^ 91569121099410454224 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (17 : ZMod 24430366801959410955600529) ^ 7892625336581465808 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (17 : ZMod 24430366801959410955600529) ^ 11218043378682768 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyER_119340533388575615159289529 : Nat.Prime 119340533388575615159289529 := by
  apply lucas_primality 119340533388575615159289529 (11 : ZMod 119340533388575615159289529)
  · rw [← oneHundredFiftyERFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (61, 1), (491, 1), (7537657, 1), (7341888420457, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (61, 1), (491, 1), (7537657, 1), (7341888420457, 1)] : List FactorBlock).map factorBlockValue).prod) = 119340533388575615159289529 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyER_2
      · exact prime_oneHundredFiftyER_3
      · exact prime_oneHundredFiftyER_61
      · exact prime_oneHundredFiftyER_491
      · exact prime_oneHundredFiftyER_7537657
      · exact prime_oneHundredFiftyER_7341888420457
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 119340533388575615159289529) ^ 59670266694287807579644764 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (11 : ZMod 119340533388575615159289529) ^ 39780177796191871719763176 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (11 : ZMod 119340533388575615159289529) ^ 1956402186697960904250648 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (11 : ZMod 119340533388575615159289529) ^ 243056076147811843501608 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (11 : ZMod 119340533388575615159289529) ^ 15832576805839747704 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (11 : ZMod 119340533388575615159289529) ^ 16254746266104 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyER_234887460417779290234045351 : Nat.Prime 234887460417779290234045351 := by
  apply lucas_primality 234887460417779290234045351 (3 : ZMod 234887460417779290234045351)
  · rw [← oneHundredFiftyERFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 2), (11, 1), (142356036616835933475179, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 2), (11, 1), (142356036616835933475179, 1)] : List FactorBlock).map factorBlockValue).prod) = 234887460417779290234045351 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyER_2
      · exact prime_oneHundredFiftyER_3
      · exact prime_oneHundredFiftyER_5
      · exact prime_oneHundredFiftyER_11
      · exact prime_oneHundredFiftyER_142356036616835933475179
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 234887460417779290234045351) ^ 117443730208889645117022675 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (3 : ZMod 234887460417779290234045351) ^ 78295820139259763411348450 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (3 : ZMod 234887460417779290234045351) ^ 46977492083555858046809070 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (3 : ZMod 234887460417779290234045351) ^ 21353405492525390021276850 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (3 : ZMod 234887460417779290234045351) ^ 1650 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyER_806091057342833473303201091 : Nat.Prime 806091057342833473303201091 := by
  apply lucas_primality 806091057342833473303201091 (2 : ZMod 806091057342833473303201091)
  · rw [← oneHundredFiftyERFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (311, 1), (259193266026634557332219, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (311, 1), (259193266026634557332219, 1)] : List FactorBlock).map factorBlockValue).prod) = 806091057342833473303201091 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyER_2
      · exact prime_oneHundredFiftyER_5
      · exact prime_oneHundredFiftyER_311
      · exact prime_oneHundredFiftyER_259193266026634557332219
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 806091057342833473303201091) ^ 403045528671416736651600545 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 806091057342833473303201091) ^ 161218211468566694660640218 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 806091057342833473303201091) ^ 2591932660266345573322190 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 806091057342833473303201091) ^ 3110 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyER_909436064694478790393355077 : Nat.Prime 909436064694478790393355077 := by
  apply lucas_primality 909436064694478790393355077 (2 : ZMod 909436064694478790393355077)
  · rw [← oneHundredFiftyERFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (4171314503, 1), (54505364198768423, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (4171314503, 1), (54505364198768423, 1)] : List FactorBlock).map factorBlockValue).prod) = 909436064694478790393355077 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyER_2
      · exact prime_oneHundredFiftyER_4171314503
      · exact prime_oneHundredFiftyER_54505364198768423
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 909436064694478790393355077) ^ 454718032347239395196677538 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 909436064694478790393355077) ^ 218021456795073692 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 909436064694478790393355077) ^ 16685258012 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyER_2273590161736196975983387693 : Nat.Prime 2273590161736196975983387693 := by
  apply lucas_primality 2273590161736196975983387693 (2 : ZMod 2273590161736196975983387693)
  · rw [← oneHundredFiftyERFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (7, 1), (11, 1), (37, 1), (7389175414818054990001, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (7, 1), (11, 1), (37, 1), (7389175414818054990001, 1)] : List FactorBlock).map factorBlockValue).prod) = 2273590161736196975983387693 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyER_2
      · exact prime_oneHundredFiftyER_3
      · exact prime_oneHundredFiftyER_7
      · exact prime_oneHundredFiftyER_11
      · exact prime_oneHundredFiftyER_37
      · exact prime_oneHundredFiftyER_7389175414818054990001
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 2273590161736196975983387693) ^ 1136795080868098487991693846 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 2273590161736196975983387693) ^ 757863387245398991994462564 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 2273590161736196975983387693) ^ 324798594533742425140483956 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 2273590161736196975983387693) ^ 206690014703290634180307972 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 2273590161736196975983387693) ^ 61448382749626945296848316 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 2273590161736196975983387693) ^ 307692 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyER_4325366649156667417724493659 : Nat.Prime 4325366649156667417724493659 := by
  apply lucas_primality 4325366649156667417724493659 (2 : ZMod 4325366649156667417724493659)
  · rw [← oneHundredFiftyERFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (1307, 1), (1654692673740117604332247, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (1307, 1), (1654692673740117604332247, 1)] : List FactorBlock).map factorBlockValue).prod) = 4325366649156667417724493659 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyER_2
      · exact prime_oneHundredFiftyER_1307
      · exact prime_oneHundredFiftyER_1654692673740117604332247
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 4325366649156667417724493659) ^ 2162683324578333708862246829 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 4325366649156667417724493659) ^ 3309385347480235208664494 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 4325366649156667417724493659) ^ 2614 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyER_6115173538462874625058766899 : Nat.Prime 6115173538462874625058766899 := by
  apply lucas_primality 6115173538462874625058766899 (2 : ZMod 6115173538462874625058766899)
  · rw [← oneHundredFiftyERFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (40151, 1), (2307642263509371299503, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (40151, 1), (2307642263509371299503, 1)] : List FactorBlock).map factorBlockValue).prod) = 6115173538462874625058766899 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyER_2
      · exact prime_oneHundredFiftyER_3
      · exact prime_oneHundredFiftyER_11
      · exact prime_oneHundredFiftyER_40151
      · exact prime_oneHundredFiftyER_2307642263509371299503
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 6115173538462874625058766899) ^ 3057586769231437312529383449 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 6115173538462874625058766899) ^ 2038391179487624875019588966 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 6115173538462874625058766899) ^ 555924867132988602278069718 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 6115173538462874625058766899) ^ 152304389391618505767198 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (2 : ZMod 6115173538462874625058766899) ^ 2649966 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyER_6820770485208590927950163077 : Nat.Prime 6820770485208590927950163077 := by
  apply lucas_primality 6820770485208590927950163077 (5 : ZMod 6820770485208590927950163077)
  · rw [← oneHundredFiftyERFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 4), (7, 1), (11, 1), (37, 1), (7389175414818054990001, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 4), (7, 1), (11, 1), (37, 1), (7389175414818054990001, 1)] : List FactorBlock).map factorBlockValue).prod) = 6820770485208590927950163077 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyER_2
      · exact prime_oneHundredFiftyER_3
      · exact prime_oneHundredFiftyER_7
      · exact prime_oneHundredFiftyER_11
      · exact prime_oneHundredFiftyER_37
      · exact prime_oneHundredFiftyER_7389175414818054990001
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 6820770485208590927950163077) ^ 3410385242604295463975081538 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (5 : ZMod 6820770485208590927950163077) ^ 2273590161736196975983387692 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (5 : ZMod 6820770485208590927950163077) ^ 974395783601227275421451868 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (5 : ZMod 6820770485208590927950163077) ^ 620070044109871902540923916 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (5 : ZMod 6820770485208590927950163077) ^ 184345148248880835890544948 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (5 : ZMod 6820770485208590927950163077) ^ 923076 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyER_12667145186815954580478874289 : Nat.Prime 12667145186815954580478874289 := by
  apply lucas_primality 12667145186815954580478874289 (3 : ZMod 12667145186815954580478874289)
  · rw [← oneHundredFiftyERFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (7, 1), (1867, 1), (9500191, 1), (6376525061137417, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (7, 1), (1867, 1), (9500191, 1), (6376525061137417, 1)] : List FactorBlock).map factorBlockValue).prod) = 12667145186815954580478874289 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyER_2
      · exact prime_oneHundredFiftyER_7
      · exact prime_oneHundredFiftyER_1867
      · exact prime_oneHundredFiftyER_9500191
      · exact prime_oneHundredFiftyER_6376525061137417
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 12667145186815954580478874289) ^ 6333572593407977290239437144 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (3 : ZMod 12667145186815954580478874289) ^ 1809592169545136368639839184 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (3 : ZMod 12667145186815954580478874289) ^ 6784759071674319539624464 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (3 : ZMod 12667145186815954580478874289) ^ 1333356896384078444368 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (3 : ZMod 12667145186815954580478874289) ^ 1986527938864 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyER_88670016307711682063352120041 : Nat.Prime 88670016307711682063352120041 := by
  apply lucas_primality 88670016307711682063352120041 (6 : ZMod 88670016307711682063352120041)
  · rw [← oneHundredFiftyERFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (13, 1), (67, 1), (3067, 1), (829821849978416232493, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (13, 1), (67, 1), (3067, 1), (829821849978416232493, 1)] : List FactorBlock).map factorBlockValue).prod) = 88670016307711682063352120041 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyER_2
      · exact prime_oneHundredFiftyER_5
      · exact prime_oneHundredFiftyER_13
      · exact prime_oneHundredFiftyER_67
      · exact prime_oneHundredFiftyER_3067
      · exact prime_oneHundredFiftyER_829821849978416232493
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 88670016307711682063352120041) ^ 44335008153855841031676060020 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (6 : ZMod 88670016307711682063352120041) ^ 17734003261542336412670424008 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (6 : ZMod 88670016307711682063352120041) ^ 6820770485208590927950163080 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (6 : ZMod 88670016307711682063352120041) ^ 1323433079219577344229136120 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (6 : ZMod 88670016307711682063352120041) ^ 28910993253248021540056120 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide
    · change (6 : ZMod 88670016307711682063352120041) ^ 106854280 ≠ 1
      rw [← oneHundredFiftyERFastPow_eq_pow]
      decide

private theorem phi_oneHundredFiftyER_177340032615423364126704240000 : Nat.totient 177340032615423364126704240000 = 47290399383401874189158400000 := by
  rw [← show ((([(2, 7), (3, 1), (5, 4), (171401, 1), (714027719, 1), (6037638679, 1)] : List FactorBlock).map factorBlockValue).prod) = 177340032615423364126704240000 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyER_2, prime_oneHundredFiftyER_3, prime_oneHundredFiftyER_5, prime_oneHundredFiftyER_171401, prime_oneHundredFiftyER_714027719, prime_oneHundredFiftyER_6037638679]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyER_177340032615423364126704240001 : Nat.totient 177340032615423364126704240001 = 177333017467284755779357987920 := by
  rw [← show ((([(33811, 1), (100183, 1), (52354586721756688477, 1)] : List FactorBlock).map factorBlockValue).prod) = 177340032615423364126704240001 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyER_33811, prime_oneHundredFiftyER_100183, prime_oneHundredFiftyER_52354586721756688477]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyER_177340032615423364126704240002 : Nat.totient 177340032615423364126704240002 = 81849245822503091135401956912 := by
  rw [← show ((([(2, 1), (13, 1), (6820770485208590927950163077, 1)] : List FactorBlock).map factorBlockValue).prod) = 177340032615423364126704240002 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyER_2, prime_oneHundredFiftyER_13, prime_oneHundredFiftyER_6820770485208590927950163077]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyER_177340032615423364126704240003 : Nat.totient 177340032615423364126704240003 = 110105854326389881265356071072 := by
  rw [← show ((([(3, 3), (19, 1), (59, 1), (276887636227, 1), (21160885802867, 1)] : List FactorBlock).map factorBlockValue).prod) = 177340032615423364126704240003 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyER_3, prime_oneHundredFiftyER_19, prime_oneHundredFiftyER_59, prime_oneHundredFiftyER_276887636227, prime_oneHundredFiftyER_21160885802867]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyER_177340032615423364126704240004 : Nat.totient 177340032615423364126704240004 = 76001856663501747458350135200 := by
  rw [← show ((([(2, 2), (7, 1), (74923, 1), (1715098811, 1), (49288369108031, 1)] : List FactorBlock).map factorBlockValue).prod) = 177340032615423364126704240004 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyER_2, prime_oneHundredFiftyER_7, prime_oneHundredFiftyER_74923, prime_oneHundredFiftyER_1715098811, prime_oneHundredFiftyER_49288369108031]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyER_177340032615423364126704240005 : Nat.totient 177340032615423364126704240005 = 140932476250667574140427210000 := by
  rw [← show ((([(5, 1), (151, 1), (234887460417779290234045351, 1)] : List FactorBlock).map factorBlockValue).prod) = 177340032615423364126704240005 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyER_5, prime_oneHundredFiftyER_151, prime_oneHundredFiftyER_234887460417779290234045351]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyER_177340032615423364126704240006 : Nat.totient 177340032615423364126704240006 = 59113318351244137588060128000 := by
  rw [← show ((([(2, 1), (3, 1), (4674151, 1), (6380281, 1), (22998923, 1), (43092877, 1)] : List FactorBlock).map factorBlockValue).prod) = 177340032615423364126704240006 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyER_2, prime_oneHundredFiftyER_3, prime_oneHundredFiftyER_4674151, prime_oneHundredFiftyER_6380281, prime_oneHundredFiftyER_22998923, prime_oneHundredFiftyER_43092877]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyER_177340032615423364126704240007 : Nat.totient 177340032615423364126704240007 = 177339835290026079109980170784 := by
  rw [← show ((([(898727, 1), (103060768229, 1), (1914633350029, 1)] : List FactorBlock).map factorBlockValue).prod) = 177340032615423364126704240007 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyER_898727, prime_oneHundredFiftyER_103060768229, prime_oneHundredFiftyER_1914633350029]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyER_177340032615423364126704240008 : Nat.totient 177340032615423364126704240008 = 87971314937219945407909345536 := by
  rw [← show ((([(2, 3), (127, 1), (171733, 1), (18239870917, 1), (55723393783, 1)] : List FactorBlock).map factorBlockValue).prod) = 177340032615423364126704240008 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyER_2, prime_oneHundredFiftyER_127, prime_oneHundredFiftyER_171733, prime_oneHundredFiftyER_18239870917, prime_oneHundredFiftyER_55723393783]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyER_177340032615423364126704240009 : Nat.totient 177340032615423364126704240009 = 107017525125822280898572154880 := by
  rw [← show ((([(3, 1), (11, 1), (233, 1), (1279484057, 1), (18026111139253033, 1)] : List FactorBlock).map factorBlockValue).prod) = 177340032615423364126704240009 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyER_3, prime_oneHundredFiftyER_11, prime_oneHundredFiftyER_233, prime_oneHundredFiftyER_1279484057, prime_oneHundredFiftyER_18026111139253033]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyER_177340032615423364126704240010 : Nat.totient 177340032615423364126704240010 = 67356515489913542860938268672 := by
  rw [← show ((([(2, 1), (5, 1), (23, 1), (137, 1), (1243169, 1), (4527184655447032079, 1)] : List FactorBlock).map factorBlockValue).prod) = 177340032615423364126704240010 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyER_2, prime_oneHundredFiftyER_5, prime_oneHundredFiftyER_23, prime_oneHundredFiftyER_137, prime_oneHundredFiftyER_1243169, prime_oneHundredFiftyER_4527184655447032079]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyER_177340032615423364126704240011 : Nat.totient 177340032615423364126704240011 = 140718912779286207104259041280 := by
  rw [← show ((([(7, 1), (17, 1), (61, 1), (24430366801959410955600529, 1)] : List FactorBlock).map factorBlockValue).prod) = 177340032615423364126704240011 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyER_7, prime_oneHundredFiftyER_17, prime_oneHundredFiftyER_61, prime_oneHundredFiftyER_24430366801959410955600529]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyER_177340032615423364126704240012 : Nat.totient 177340032615423364126704240012 = 57143367364815166529092239360 := by
  rw [← show ((([(2, 2), (3, 2), (43, 1), (97, 1), (12844297, 1), (91950427801125241, 1)] : List FactorBlock).map factorBlockValue).prod) = 177340032615423364126704240012 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyER_2, prime_oneHundredFiftyER_3, prime_oneHundredFiftyER_43, prime_oneHundredFiftyER_97, prime_oneHundredFiftyER_12844297, prime_oneHundredFiftyER_91950427801125241]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyER_177340032615423364126704240013 : Nat.totient 177340032615423364126704240013 = 163759220767298312542898620416 := by
  rw [← show ((([(29, 1), (37, 2), (67, 1), (467, 1), (142762338978465458017, 1)] : List FactorBlock).map factorBlockValue).prod) = 177340032615423364126704240013 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyER_29, prime_oneHundredFiftyER_37, prime_oneHundredFiftyER_67, prime_oneHundredFiftyER_467, prime_oneHundredFiftyER_142762338978465458017]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyER_177340032615423364126704240014 : Nat.totient 177340032615423364126704240014 = 88669859512521972204364545792 := by
  rw [← show ((([(2, 1), (888109, 1), (1577353, 1), (184175687, 1), (343676093, 1)] : List FactorBlock).map factorBlockValue).prod) = 177340032615423364126704240014 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyER_2, prime_oneHundredFiftyER_888109, prime_oneHundredFiftyER_1577353, prime_oneHundredFiftyER_184175687, prime_oneHundredFiftyER_343676093]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyER_177340032615423364126704240015 : Nat.totient 177340032615423364126704240015 = 87305862210669963877762087296 := by
  rw [← show ((([(3, 1), (5, 1), (13, 1), (909436064694478790393355077, 1)] : List FactorBlock).map factorBlockValue).prod) = 177340032615423364126704240015 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyER_3, prime_oneHundredFiftyER_5, prime_oneHundredFiftyER_13, prime_oneHundredFiftyER_909436064694478790393355077]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyER_177340032615423364126704240016 : Nat.totient 177340032615423364126704240016 = 88670014533886808663519154176 := by
  rw [← show ((([(2, 4), (49988033, 1), (221728109174929132697, 1)] : List FactorBlock).map factorBlockValue).prod) = 177340032615423364126704240016 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyER_2, prime_oneHundredFiftyER_49988033, prime_oneHundredFiftyER_221728109174929132697]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyER_177340032615423364126704240017 : Nat.totient 177340032615423364126704240017 = 177334024738785424059229927632 := by
  rw [← show ((([(29527, 1), (96003997, 1), (62560202419495043, 1)] : List FactorBlock).map factorBlockValue).prod) = 177340032615423364126704240017 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyER_29527, prime_oneHundredFiftyER_96003997, prime_oneHundredFiftyER_62560202419495043]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyER_177340032615423364126704240018 : Nat.totient 177340032615423364126704240018 = 50618561308710241179351344832 := by
  rw [← show ((([(2, 1), (3, 1), (7, 1), (1013, 1), (46174027, 1), (90271424483937779, 1)] : List FactorBlock).map factorBlockValue).prod) = 177340032615423364126704240018 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyER_2, prime_oneHundredFiftyER_3, prime_oneHundredFiftyER_7, prime_oneHundredFiftyER_1013, prime_oneHundredFiftyER_46174027, prime_oneHundredFiftyER_90271424483937779]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyER_177340032615423364126704240019 : Nat.totient 177340032615423364126704240019 = 173014665966266696708979746320 := by
  rw [← show ((([(41, 1), (4325366649156667417724493659, 1)] : List FactorBlock).map factorBlockValue).prod) = 177340032615423364126704240019 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyER_41, prime_oneHundredFiftyER_4325366649156667417724493659]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyER_177340032615423364126704240020 : Nat.totient 177340032615423364126704240020 = 64487284587426677864256087200 := by
  rw [← show ((([(2, 2), (5, 1), (11, 1), (806091057342833473303201091, 1)] : List FactorBlock).map factorBlockValue).prod) = 177340032615423364126704240020 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyER_2, prime_oneHundredFiftyER_5, prime_oneHundredFiftyER_11, prime_oneHundredFiftyER_806091057342833473303201091]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyER_177340032615423364126704240021 : Nat.totient 177340032615423364126704240021 = 118177075867936341684098321064 := by
  rw [← show ((([(3, 2), (2383, 1), (8268757057650177839637443, 1)] : List FactorBlock).map factorBlockValue).prod) = 177340032615423364126704240021 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyER_3, prime_oneHundredFiftyER_2383, prime_oneHundredFiftyER_8268757057650177839637443]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyER_177340032615423364126704240022 : Nat.totient 177340032615423364126704240022 = 83729547372342867273263062728 := by
  rw [← show ((([(2, 1), (19, 1), (307, 1), (15201442878057891661812467, 1)] : List FactorBlock).map factorBlockValue).prod) = 177340032615423364126704240022 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyER_2, prime_oneHundredFiftyER_19, prime_oneHundredFiftyER_307, prime_oneHundredFiftyER_15201442878057891661812467]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyER_177340032615423364126704240023 : Nat.totient 177340032615423364126704240023 = 177272966334796832542003153920 := by
  rw [← show ((([(2731, 1), (93997, 1), (725393, 1), (952352509668073, 1)] : List FactorBlock).map factorBlockValue).prod) = 177340032615423364126704240023 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyER_2731, prime_oneHundredFiftyER_93997, prime_oneHundredFiftyER_725393, prime_oneHundredFiftyER_952352509668073]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyER_177340032615423364126704240024 : Nat.totient 177340032615423364126704240024 = 58725076372807273625823105024 := by
  rw [← show ((([(2, 3), (3, 1), (157, 1), (4999, 1), (87683238689, 1), (107373267763, 1)] : List FactorBlock).map factorBlockValue).prod) = 177340032615423364126704240024 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyER_2, prime_oneHundredFiftyER_3, prime_oneHundredFiftyER_157, prime_oneHundredFiftyER_4999, prime_oneHundredFiftyER_87683238689, prime_oneHundredFiftyER_107373267763]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyER_177340032615423364126704240025 : Nat.totient 177340032615423364126704240025 = 121499125802285346831250483200 := by
  rw [← show ((([(5, 2), (7, 1), (1153, 1), (878899926231809511221431, 1)] : List FactorBlock).map factorBlockValue).prod) = 177340032615423364126704240025 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyER_5, prime_oneHundredFiftyER_7, prime_oneHundredFiftyER_1153, prime_oneHundredFiftyER_878899926231809511221431]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyER_177340032615423364126704240026 : Nat.totient 177340032615423364126704240026 = 88041309287427748489207968000 := by
  rw [← show ((([(2, 1), (271, 1), (293, 1), (1606937041, 1), (694929927928631, 1)] : List FactorBlock).map factorBlockValue).prod) = 177340032615423364126704240026 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyER_2, prime_oneHundredFiftyER_271, prime_oneHundredFiftyER_293, prime_oneHundredFiftyER_1606937041, prime_oneHundredFiftyER_694929927928631]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyER_177340032615423364126704240027 : Nat.totient 177340032615423364126704240027 = 118225288333444490868294889608 := by
  rw [← show ((([(3, 1), (84443, 1), (700038418875941420550763, 1)] : List FactorBlock).map factorBlockValue).prod) = 177340032615423364126704240027 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyER_3, prime_oneHundredFiftyER_84443, prime_oneHundredFiftyER_700038418875941420550763]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyER_177340032615423364126704240028 : Nat.totient 177340032615423364126704240028 = 74549597713095794582529285120 := by
  rw [← show ((([(2, 2), (13, 1), (17, 1), (31, 1), (6471319245928454390844557, 1)] : List FactorBlock).map factorBlockValue).prod) = 177340032615423364126704240028 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyER_2, prime_oneHundredFiftyER_13, prime_oneHundredFiftyER_17, prime_oneHundredFiftyER_31, prime_oneHundredFiftyER_6471319245928454390844557]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyER_177340032615423364126704240029 : Nat.totient 177340032615423364126704240029 = 177339910374927526173314550876 := by
  rw [← show ((([(1450747, 1), (122240495837953388238407, 1)] : List FactorBlock).map factorBlockValue).prod) = 177340032615423364126704240029 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyER_1450747, prime_oneHundredFiftyER_122240495837953388238407]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyER_177340032615423364126704240030 : Nat.totient 177340032615423364126704240030 = 47290597482586374919730982528 := by
  rw [← show ((([(2, 1), (3, 3), (5, 1), (607213, 1), (1081687868363620552253, 1)] : List FactorBlock).map factorBlockValue).prod) = 177340032615423364126704240030 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyER_2, prime_oneHundredFiftyER_3, prime_oneHundredFiftyER_5, prime_oneHundredFiftyER_607213, prime_oneHundredFiftyER_1081687868363620552253]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyER_177340032615423364126704240031 : Nat.totient 177340032615423364126704240031 = 156726234781662476655151843200 := by
  rw [← show ((([(11, 1), (47, 1), (149, 1), (55541, 1), (41449211920200238027, 1)] : List FactorBlock).map factorBlockValue).prod) = 177340032615423364126704240031 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyER_11, prime_oneHundredFiftyER_47, prime_oneHundredFiftyER_149, prime_oneHundredFiftyER_55541, prime_oneHundredFiftyER_41449211920200238027]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyER_177340032615423364126704240032 : Nat.totient 177340032615423364126704240032 = 75962154570609316189466926080 := by
  rw [← show ((([(2, 5), (7, 2), (1867, 1), (9500191, 1), (6376525061137417, 1)] : List FactorBlock).map factorBlockValue).prod) = 177340032615423364126704240032 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyER_2, prime_oneHundredFiftyER_7, prime_oneHundredFiftyER_1867, prime_oneHundredFiftyER_9500191, prime_oneHundredFiftyER_6376525061137417]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyER_177340032615423364126704240033 : Nat.totient 177340032615423364126704240033 = 113086393293330312108630248784 := by
  rw [← show ((([(3, 1), (23, 1), (26198603, 1), (98102383559288524519, 1)] : List FactorBlock).map factorBlockValue).prod) = 177340032615423364126704240033 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyER_3, prime_oneHundredFiftyER_23, prime_oneHundredFiftyER_26198603, prime_oneHundredFiftyER_98102383559288524519]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyER_177340032615423364126704240034 : Nat.totient 177340032615423364126704240034 = 88482229768342183410348042240 := by
  rw [← show ((([(2, 1), (479, 1), (37493, 1), (287149, 1), (26270561, 1), (654507199, 1)] : List FactorBlock).map factorBlockValue).prod) = 177340032615423364126704240034 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyER_2, prime_oneHundredFiftyER_479, prime_oneHundredFiftyER_37493, prime_oneHundredFiftyER_287149, prime_oneHundredFiftyER_26270561, prime_oneHundredFiftyER_654507199]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyER_177340032615423364126704240035 : Nat.totient 177340032615423364126704240035 = 141871962398820103475773865280 := by
  rw [← show ((([(5, 1), (2227417, 1), (15923379646956395154271, 1)] : List FactorBlock).map factorBlockValue).prod) = 177340032615423364126704240035 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyER_5, prime_oneHundredFiftyER_2227417, prime_oneHundredFiftyER_15923379646956395154271]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyER_177340032615423364126704240036 : Nat.totient 177340032615423364126704240036 = 59109728488805247745218285312 := by
  rw [← show ((([(2, 2), (3, 1), (16349, 1), (659795388823, 1), (1370014198489, 1)] : List FactorBlock).map factorBlockValue).prod) = 177340032615423364126704240036 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyER_2, prime_oneHundredFiftyER_3, prime_oneHundredFiftyER_16349, prime_oneHundredFiftyER_659795388823, prime_oneHundredFiftyER_1370014198489]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyER_177340032615423364126704240037 : Nat.totient 177340032615423364126704240037 = 177339772518546879432928008396 := by
  rw [← show ((([(681823, 1), (260096876484693775549819, 1)] : List FactorBlock).map factorBlockValue).prod) = 177340032615423364126704240037 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyER_681823, prime_oneHundredFiftyER_260096876484693775549819]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyER_177340032615423364126704240038 : Nat.totient 177340032615423364126704240038 = 87547518275776514247048007680 := by
  rw [← show ((([(2, 1), (79, 1), (1033741, 1), (10845649, 1), (100111140810529, 1)] : List FactorBlock).map factorBlockValue).prod) = 177340032615423364126704240038 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyER_2, prime_oneHundredFiftyER_79, prime_oneHundredFiftyER_1033741, prime_oneHundredFiftyER_10845649, prime_oneHundredFiftyER_100111140810529]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyER_177340032615423364126704240039 : Nat.totient 177340032615423364126704240039 = 101337081081441724564713385920 := by
  rw [← show ((([(3, 2), (7, 1), (1260341, 1), (12748193219, 1), (175198156807, 1)] : List FactorBlock).map factorBlockValue).prod) = 177340032615423364126704240039 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyER_3, prime_oneHundredFiftyER_7, prime_oneHundredFiftyER_1260341, prime_oneHundredFiftyER_12748193219, prime_oneHundredFiftyER_175198156807]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyER_177340032615423364126704240040 : Nat.totient 177340032615423364126704240040 = 68093553286920526626065459200 := by
  rw [← show ((([(2, 3), (5, 1), (53, 1), (71, 1), (131, 1), (8993759679696815118617, 1)] : List FactorBlock).map factorBlockValue).prod) = 177340032615423364126704240040 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyER_2, prime_oneHundredFiftyER_5, prime_oneHundredFiftyER_53, prime_oneHundredFiftyER_71, prime_oneHundredFiftyER_131, prime_oneHundredFiftyER_8993759679696815118617]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyER_177340032615423364126704240041 : Nat.totient 177340032615423364126704240041 = 151239726636015530047232130048 := by
  rw [← show ((([(13, 1), (19, 1), (73, 1), (89, 1), (110508825696209439627199, 1)] : List FactorBlock).map factorBlockValue).prod) = 177340032615423364126704240041 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyER_13, prime_oneHundredFiftyER_19, prime_oneHundredFiftyER_73, prime_oneHundredFiftyER_89, prime_oneHundredFiftyER_110508825696209439627199]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyER_177340032615423364126704240042 : Nat.totient 177340032615423364126704240042 = 51885028652744704298002968000 := by
  rw [← show ((([(2, 1), (3, 1), (11, 1), (29, 1), (40151, 1), (2307642263509371299503, 1)] : List FactorBlock).map factorBlockValue).prod) = 177340032615423364126704240042 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyER_2, prime_oneHundredFiftyER_3, prime_oneHundredFiftyER_11, prime_oneHundredFiftyER_29, prime_oneHundredFiftyER_40151, prime_oneHundredFiftyER_2307642263509371299503]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyER_177340032615423364126704240043 : Nat.totient 177340032615423364126704240043 = 177340032612950644821671727048 := by
  rw [← show ((([(71718628717, 1), (2472719233313884279, 1)] : List FactorBlock).map factorBlockValue).prod) = 177340032615423364126704240043 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyER_71718628717, prime_oneHundredFiftyER_2472719233313884279]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyER_177340032615423364126704240044 : Nat.totient 177340032615423364126704240044 = 88558029443897325103810010112 := by
  rw [← show ((([(2, 2), (809, 1), (37657, 1), (4419907, 1), (12042907, 1), (27340603, 1)] : List FactorBlock).map factorBlockValue).prod) = 177340032615423364126704240044 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyER_2, prime_oneHundredFiftyER_809, prime_oneHundredFiftyER_37657, prime_oneHundredFiftyER_4419907, prime_oneHundredFiftyER_12042907, prime_oneHundredFiftyER_27340603]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyER_177340032615423364126704240045 : Nat.totient 177340032615423364126704240045 = 88846882468641101506988482560 := by
  rw [← show ((([(3, 1), (5, 1), (17, 1), (521, 1), (23096547757, 1), (57793874370247, 1)] : List FactorBlock).map factorBlockValue).prod) = 177340032615423364126704240045 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyER_3, prime_oneHundredFiftyER_5, prime_oneHundredFiftyER_17, prime_oneHundredFiftyER_521, prime_oneHundredFiftyER_23096547757, prime_oneHundredFiftyER_57793874370247]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyER_177340032615423364126704240046 : Nat.totient 177340032615423364126704240046 = 76002871120895727482873245728 := by
  rw [← show ((([(2, 1), (7, 1), (12667145186815954580478874289, 1)] : List FactorBlock).map factorBlockValue).prod) = 177340032615423364126704240046 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyER_2, prime_oneHundredFiftyER_7, prime_oneHundredFiftyER_12667145186815954580478874289]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyER_177340032615423364126704240047 : Nat.totient 177340032615423364126704240047 = 177340032615257161470244626240 := by
  rw [← show ((([(1067017669391, 1), (166201589441944417, 1)] : List FactorBlock).map factorBlockValue).prod) = 177340032615423364126704240047 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyER_1067017669391, prime_oneHundredFiftyER_166201589441944417]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyER_177340032615423364126704240048 : Nat.totient 177340032615423364126704240048 = 59112405745661049662303308800 := by
  rw [← show ((([(2, 4), (3, 2), (63907, 1), (6496339, 1), (14483401, 1), (204812579, 1)] : List FactorBlock).map factorBlockValue).prod) = 177340032615423364126704240048 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyER_2, prime_oneHundredFiftyER_3, prime_oneHundredFiftyER_63907, prime_oneHundredFiftyER_6496339, prime_oneHundredFiftyER_14483401, prime_oneHundredFiftyER_204812579]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyER_177340032615423364126704240049 : Nat.totient 177340032615423364126704240049 = 177340026684123410150637530400 := by
  rw [← show ((([(29967017, 1), (13587090151, 1), (435548791247, 1)] : List FactorBlock).map factorBlockValue).prod) = 177340032615423364126704240049 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyER_29967017, prime_oneHundredFiftyER_13587090151, prime_oneHundredFiftyER_435548791247]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyER_177340032615423364126704240050 : Nat.totient 177340032615423364126704240050 = 69016609730653417167521794560 := by
  rw [← show ((([(2, 1), (5, 2), (37, 1), (31177, 1), (3074685732733041494149, 1)] : List FactorBlock).map factorBlockValue).prod) = 177340032615423364126704240050 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyER_2, prime_oneHundredFiftyER_5, prime_oneHundredFiftyER_37, prime_oneHundredFiftyER_31177, prime_oneHundredFiftyER_3074685732733041494149]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyER_177340032615423364126704240051 : Nat.totient 177340032615423364126704240051 = 118226610834071365581774473160 := by
  rw [← show ((([(3, 1), (1524007, 1), (38788105438584679319431, 1)] : List FactorBlock).map factorBlockValue).prod) = 177340032615423364126704240051 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyER_3, prime_oneHundredFiftyER_1524007, prime_oneHundredFiftyER_38788105438584679319431]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyER_177340032615423364126704240052 : Nat.totient 177340032615423364126704240052 = 88669885888189046975134018040 := by
  rw [← show ((([(2, 2), (679883, 1), (65209761317544108371111, 1)] : List FactorBlock).map factorBlockValue).prod) = 177340032615423364126704240052 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyER_2, prime_oneHundredFiftyER_679883, prime_oneHundredFiftyER_65209761317544108371111]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyER_177340032615423364126704240053 : Nat.totient 177340032615423364126704240053 = 137959382654673688346925789360 := by
  rw [← show ((([(7, 1), (11, 1), (607, 1), (3794262449248451274667927, 1)] : List FactorBlock).map factorBlockValue).prod) = 177340032615423364126704240053 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyER_7, prime_oneHundredFiftyER_11, prime_oneHundredFiftyER_607, prime_oneHundredFiftyER_3794262449248451274667927]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyER_177340032615423364126704240054 : Nat.totient 177340032615423364126704240054 = 54566163881668727423601304608 := by
  rw [← show ((([(2, 1), (3, 1), (13, 1), (2273590161736196975983387693, 1)] : List FactorBlock).map factorBlockValue).prod) = 177340032615423364126704240054 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyER_2, prime_oneHundredFiftyER_3, prime_oneHundredFiftyER_13, prime_oneHundredFiftyER_2273590161736196975983387693]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyER_177340032615423364126704240055 : Nat.totient 177340032615423364126704240055 = 138570149002820180868299064960 := by
  rw [← show ((([(5, 1), (43, 1), (54829, 1), (487066871, 1), (30886550519203, 1)] : List FactorBlock).map factorBlockValue).prod) = 177340032615423364126704240055 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyER_5, prime_oneHundredFiftyER_43, prime_oneHundredFiftyER_54829, prime_oneHundredFiftyER_487066871, prime_oneHundredFiftyER_30886550519203]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyER_177340032615423364126704240056 : Nat.totient 177340032615423364126704240056 = 84808459708031388975286088448 := by
  rw [← show ((([(2, 3), (23, 1), (13417, 1), (4972199, 1), (14447245053557023, 1)] : List FactorBlock).map factorBlockValue).prod) = 177340032615423364126704240056 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyER_2, prime_oneHundredFiftyER_23, prime_oneHundredFiftyER_13417, prime_oneHundredFiftyER_4972199, prime_oneHundredFiftyER_14447245053557023]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyER_177340032615423364126704240057 : Nat.totient 177340032615423364126704240057 = 117850317452314068191629213440 := by
  rw [← show ((([(3, 4), (457, 1), (1039, 1), (28541, 1), (161555159326910779, 1)] : List FactorBlock).map factorBlockValue).prod) = 177340032615423364126704240057 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyER_3, prime_oneHundredFiftyER_457, prime_oneHundredFiftyER_1039, prime_oneHundredFiftyER_28541, prime_oneHundredFiftyER_161555159326910779]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyER_177340032615423364126704240058 : Nat.totient 177340032615423364126704240058 = 88438543397416542933743486976 := by
  rw [← show ((([(2, 1), (523, 1), (1429, 1), (5192430209, 1), (22849263327643, 1)] : List FactorBlock).map factorBlockValue).prod) = 177340032615423364126704240058 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyER_2, prime_oneHundredFiftyER_523, prime_oneHundredFiftyER_1429, prime_oneHundredFiftyER_5192430209, prime_oneHundredFiftyER_22849263327643]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyER_177340032615423364126704240059 : Nat.totient 177340032615423364126704240059 = 171619337464263666120158922600 := by
  rw [← show ((([(31, 1), (3506891, 1), (1631258631477497784079, 1)] : List FactorBlock).map factorBlockValue).prod) = 177340032615423364126704240059 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyER_31, prime_oneHundredFiftyER_3506891, prime_oneHundredFiftyER_1631258631477497784079]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyER_177340032615423364126704240060 : Nat.totient 177340032615423364126704240060 = 37370457330634725440398295040 := by
  rw [← show ((([(2, 2), (3, 1), (5, 1), (7, 1), (19, 1), (41, 1), (397, 1), (13617913, 1), (100257985466497, 1)] : List FactorBlock).map factorBlockValue).prod) = 177340032615423364126704240060 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyER_2, prime_oneHundredFiftyER_3, prime_oneHundredFiftyER_5, prime_oneHundredFiftyER_7, prime_oneHundredFiftyER_19, prime_oneHundredFiftyER_41, prime_oneHundredFiftyER_397, prime_oneHundredFiftyER_13617913, prime_oneHundredFiftyER_100257985466497]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyER_177340032615423364126704240061 : Nat.totient 177340032615423364126704240061 = 175616892598386065245385482800 := by
  rw [← show ((([(103, 1), (126151, 1), (13648309482050318656237, 1)] : List FactorBlock).map factorBlockValue).prod) = 177340032615423364126704240061 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyER_103, prime_oneHundredFiftyER_126151, prime_oneHundredFiftyER_13648309482050318656237]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyER_177340032615423364126704240062 : Nat.totient 177340032615423364126704240062 = 81219741977090680528916736000 := by
  rw [← show ((([(2, 1), (17, 1), (59, 1), (101, 1), (10909, 1), (417671, 1), (192103473542443, 1)] : List FactorBlock).map factorBlockValue).prod) = 177340032615423364126704240062 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyER_2, prime_oneHundredFiftyER_17, prime_oneHundredFiftyER_59, prime_oneHundredFiftyER_101, prime_oneHundredFiftyER_10909, prime_oneHundredFiftyER_417671, prime_oneHundredFiftyER_192103473542443]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyER_177340032615423364126704240063 : Nat.totient 177340032615423364126704240063 = 117508366686021233866175792736 := by
  rw [← show ((([(3, 1), (199, 1), (947, 1), (67997183, 1), (4613086018624079, 1)] : List FactorBlock).map factorBlockValue).prod) = 177340032615423364126704240063 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyER_3, prime_oneHundredFiftyER_199, prime_oneHundredFiftyER_947, prime_oneHundredFiftyER_67997183, prime_oneHundredFiftyER_4613086018624079]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyER_177340032615423364126704240064 : Nat.totient 177340032615423364126704240064 = 80397164253638893852172083200 := by
  rw [← show ((([(2, 6), (11, 1), (383, 1), (54581, 1), (97346663, 1), (123786360409, 1)] : List FactorBlock).map factorBlockValue).prod) = 177340032615423364126704240064 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyER_2, prime_oneHundredFiftyER_11, prime_oneHundredFiftyER_383, prime_oneHundredFiftyER_54581, prime_oneHundredFiftyER_97346663, prime_oneHundredFiftyER_123786360409]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyER_177340032615423364126704240065 : Nat.totient 177340032615423364126704240065 = 141818428799561424956412810240 := by
  rw [← show ((([(5, 1), (2647, 1), (47591935099, 1), (281546073328321, 1)] : List FactorBlock).map factorBlockValue).prod) = 177340032615423364126704240065 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyER_5, prime_oneHundredFiftyER_2647, prime_oneHundredFiftyER_47591935099, prime_oneHundredFiftyER_281546073328321]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyER_177340032615423364126704240066 : Nat.totient 177340032615423364126704240066 = 59113264663306037026264903776 := by
  rw [← show ((([(2, 1), (3, 2), (743173, 1), (13256972514058216452869, 1)] : List FactorBlock).map factorBlockValue).prod) = 177340032615423364126704240066 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyER_2, prime_oneHundredFiftyER_3, prime_oneHundredFiftyER_743173, prime_oneHundredFiftyER_13256972514058216452869]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyER_177340032615423364126704240067 : Nat.totient 177340032615423364126704240067 = 140297086139467944447032307840 := by
  rw [← show ((([(7, 1), (13, 1), (8821, 1), (220926376510877967446197, 1)] : List FactorBlock).map factorBlockValue).prod) = 177340032615423364126704240067 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyER_7, prime_oneHundredFiftyER_13, prime_oneHundredFiftyER_8821, prime_oneHundredFiftyER_220926376510877967446197]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyER_177340032615423364126704240068 : Nat.totient 177340032615423364126704240068 = 88670009987867145241724031720 := by
  rw [← show ((([(2, 2), (14030411, 1), (3159922268410800013747, 1)] : List FactorBlock).map factorBlockValue).prod) = 177340032615423364126704240068 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyER_2, prime_oneHundredFiftyER_14030411, prime_oneHundredFiftyER_3159922268410800013747]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyER_177340032615423364126704240069 : Nat.totient 177340032615423364126704240069 = 118198382873100656754310260480 := by
  rw [← show ((([(3, 1), (4177, 1), (89111779, 1), (158812959932849581, 1)] : List FactorBlock).map factorBlockValue).prod) = 177340032615423364126704240069 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyER_3, prime_oneHundredFiftyER_4177, prime_oneHundredFiftyER_89111779, prime_oneHundredFiftyER_158812959932849581]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyER_177340032615423364126704240070 : Nat.totient 177340032615423364126704240070 = 70873728476942264034678604800 := by
  rw [← show ((([(2, 1), (5, 1), (1697, 1), (3461, 1), (3019418713742564280571, 1)] : List FactorBlock).map factorBlockValue).prod) = 177340032615423364126704240070 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyER_2, prime_oneHundredFiftyER_5, prime_oneHundredFiftyER_1697, prime_oneHundredFiftyER_3461, prime_oneHundredFiftyER_3019418713742564280571]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyER_177340032615423364126704240071 : Nat.totient 177340032615423364126704240071 = 171224859076960489501645473144 := by
  rw [← show ((([(29, 1), (6115173538462874625058766899, 1)] : List FactorBlock).map factorBlockValue).prod) = 177340032615423364126704240071 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyER_29, prime_oneHundredFiftyER_6115173538462874625058766899]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyER_177340032615423364126704240072 : Nat.totient 177340032615423364126704240072 = 57409197342493262598097931520 := by
  rw [← show ((([(2, 3), (3, 1), (61, 1), (83, 1), (1663, 1), (877597476325376642987, 1)] : List FactorBlock).map factorBlockValue).prod) = 177340032615423364126704240072 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyER_2, prime_oneHundredFiftyER_3, prime_oneHundredFiftyER_61, prime_oneHundredFiftyER_83, prime_oneHundredFiftyER_1663, prime_oneHundredFiftyER_877597476325376642987]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyER_177340032615423364126704240073 : Nat.totient 177340032615423364126704240073 = 177336601305400445151350296848 := by
  rw [← show ((([(51683, 1), (25232620319, 1), (135986788140349, 1)] : List FactorBlock).map factorBlockValue).prod) = 177340032615423364126704240073 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyER_51683, prime_oneHundredFiftyER_25232620319, prime_oneHundredFiftyER_135986788140349]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyER_177340032615423364126704240074 : Nat.totient 177340032615423364126704240074 = 75085000723965314858572650240 := by
  rw [← show ((([(2, 1), (7, 1), (107, 1), (373, 1), (13159, 1), (2720280181, 1), (8866446839, 1)] : List FactorBlock).map factorBlockValue).prod) = 177340032615423364126704240074 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyER_2, prime_oneHundredFiftyER_7, prime_oneHundredFiftyER_107, prime_oneHundredFiftyER_373, prime_oneHundredFiftyER_13159, prime_oneHundredFiftyER_2720280181, prime_oneHundredFiftyER_8866446839]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyER_177340032615423364126704240075 : Nat.totient 177340032615423364126704240075 = 85795306199477474195508480000 := by
  rw [← show ((([(3, 2), (5, 2), (11, 1), (461, 1), (69997, 1), (2220502305087140441, 1)] : List FactorBlock).map factorBlockValue).prod) = 177340032615423364126704240075 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyER_3, prime_oneHundredFiftyER_5, prime_oneHundredFiftyER_11, prime_oneHundredFiftyER_461, prime_oneHundredFiftyER_69997, prime_oneHundredFiftyER_2220502305087140441]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyER_177340032615423364126704240076 : Nat.totient 177340032615423364126704240076 = 88582137203133109206321944832 := by
  rw [← show ((([(2, 2), (1009, 1), (423182745173, 1), (103831152582167, 1)] : List FactorBlock).map factorBlockValue).prod) = 177340032615423364126704240076 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyER_2, prime_oneHundredFiftyER_1009, prime_oneHundredFiftyER_423182745173, prime_oneHundredFiftyER_103831152582167]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyER_177340032615423364126704240077 : Nat.totient 177340032615423364126704240077 = 177268322086596010073780778240 := by
  rw [← show ((([(2473, 1), (4168160089, 1), (17204350304931341, 1)] : List FactorBlock).map factorBlockValue).prod) = 177340032615423364126704240077 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyER_2473, prime_oneHundredFiftyER_4168160089, prime_oneHundredFiftyER_17204350304931341]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyER_177340032615423364126704240078 : Nat.totient 177340032615423364126704240078 = 57855530902346824085692921584 := by
  rw [← show ((([(2, 1), (3, 1), (47, 2), (700643, 1), (19096906877256609199, 1)] : List FactorBlock).map factorBlockValue).prod) = 177340032615423364126704240078 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyER_2, prime_oneHundredFiftyER_3, prime_oneHundredFiftyER_47, prime_oneHundredFiftyER_700643, prime_oneHundredFiftyER_19096906877256609199]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyER_177340032615423364126704240079 : Nat.totient 177340032615423364126704240079 = 151248186745392511675253574144 := by
  rw [← show ((([(17, 1), (19, 1), (23, 1), (306389, 1), (77911803317743343159, 1)] : List FactorBlock).map factorBlockValue).prod) = 177340032615423364126704240079 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyER_17, prime_oneHundredFiftyER_19, prime_oneHundredFiftyER_23, prime_oneHundredFiftyER_306389, prime_oneHundredFiftyER_77911803317743343159]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyER_177340032615423364126704240080 : Nat.totient 177340032615423364126704240080 = 64481061225305239734586042368 := by
  rw [← show ((([(2, 4), (5, 1), (13, 1), (67, 1), (3067, 1), (829821849978416232493, 1)] : List FactorBlock).map factorBlockValue).prod) = 177340032615423364126704240080 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyER_2, prime_oneHundredFiftyER_5, prime_oneHundredFiftyER_13, prime_oneHundredFiftyER_67, prime_oneHundredFiftyER_3067, prime_oneHundredFiftyER_829821849978416232493]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyER_177340032615423364126704240081 : Nat.totient 177340032615423364126704240081 = 101130767985554066156883403680 := by
  rw [← show ((([(3, 1), (7, 2), (491, 1), (24205387, 1), (101506984564892419, 1)] : List FactorBlock).map factorBlockValue).prod) = 177340032615423364126704240081 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyER_3, prime_oneHundredFiftyER_7, prime_oneHundredFiftyER_491, prime_oneHundredFiftyER_24205387, prime_oneHundredFiftyER_101506984564892419]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyER_177340032615423364126704240082 : Nat.totient 177340032615423364126704240082 = 88670016307711682063352120040 := by
  rw [← show ((([(2, 1), (88670016307711682063352120041, 1)] : List FactorBlock).map factorBlockValue).prod) = 177340032615423364126704240082 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyER_2, prime_oneHundredFiftyER_88670016307711682063352120041]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyER_177340032615423364126704240083 : Nat.totient 177340032615423364126704240083 = 177333657376087151617658423568 := by
  rw [← show ((([(27817, 1), (6375239336212509045788699, 1)] : List FactorBlock).map factorBlockValue).prod) = 177340032615423364126704240083 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyER_27817, prime_oneHundredFiftyER_6375239336212509045788699]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyER_177340032615423364126704240084 : Nat.totient 177340032615423364126704240084 = 58490355248087555963193319296 := by
  rw [← show ((([(2, 2), (3, 3), (109, 1), (727, 1), (588827, 1), (35191226542465943, 1)] : List FactorBlock).map factorBlockValue).prod) = 177340032615423364126704240084 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyER_2, prime_oneHundredFiftyER_3, prime_oneHundredFiftyER_109, prime_oneHundredFiftyER_727, prime_oneHundredFiftyER_588827, prime_oneHundredFiftyER_35191226542465943]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyER_177340032615423364126704240085 : Nat.totient 177340032615423364126704240085 = 141644242387692009792026929920 := by
  rw [← show ((([(5, 1), (653, 1), (13463, 1), (10868173573, 1), (371214717911, 1)] : List FactorBlock).map factorBlockValue).prod) = 177340032615423364126704240085 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyER_5, prime_oneHundredFiftyER_653, prime_oneHundredFiftyER_13463, prime_oneHundredFiftyER_10868173573, prime_oneHundredFiftyER_371214717911]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyER_177340032615423364126704240086 : Nat.totient 177340032615423364126704240086 = 80482248183780519314656768000 := by
  rw [← show ((([(2, 1), (11, 1), (641, 1), (73013, 1), (172236773115593411261, 1)] : List FactorBlock).map factorBlockValue).prod) = 177340032615423364126704240086 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyER_2, prime_oneHundredFiftyER_11, prime_oneHundredFiftyER_641, prime_oneHundredFiftyER_73013, prime_oneHundredFiftyER_172236773115593411261]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyER_177340032615423364126704240087 : Nat.totient 177340032615423364126704240087 = 114991165805970882545858632320 := by
  rw [← show ((([(3, 1), (37, 1), (2861, 1), (558426407371653470016797, 1)] : List FactorBlock).map factorBlockValue).prod) = 177340032615423364126704240087 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyER_3, prime_oneHundredFiftyER_37, prime_oneHundredFiftyER_2861, prime_oneHundredFiftyER_558426407371653470016797]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyER_177340032615423364126704240088 : Nat.totient 177340032615423364126704240088 = 75110966926821628829257996800 := by
  rw [← show ((([(2, 3), (7, 1), (167, 1), (173, 1), (716003, 1), (153088067484138301, 1)] : List FactorBlock).map factorBlockValue).prod) = 177340032615423364126704240088 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyER_2, prime_oneHundredFiftyER_7, prime_oneHundredFiftyER_167, prime_oneHundredFiftyER_173, prime_oneHundredFiftyER_716003, prime_oneHundredFiftyER_153088067484138301]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyER_177340032615423364126704240089 : Nat.totient 177340032615423364126704240089 = 177330654960606355986073396240 := by
  rw [← show ((([(18911, 1), (4204343453, 1), (2230458273400883, 1)] : List FactorBlock).map factorBlockValue).prod) = 177340032615423364126704240089 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyER_18911, prime_oneHundredFiftyER_4204343453, prime_oneHundredFiftyER_2230458273400883]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyER_177340032615423364126704240090 : Nat.totient 177340032615423364126704240090 = 45765156991158443238976235520 := by
  rw [← show ((([(2, 1), (3, 1), (5, 1), (31, 1), (3599009, 1), (52983531609217552957, 1)] : List FactorBlock).map factorBlockValue).prod) = 177340032615423364126704240090 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyER_2, prime_oneHundredFiftyER_3, prime_oneHundredFiftyER_5, prime_oneHundredFiftyER_31, prime_oneHundredFiftyER_3599009, prime_oneHundredFiftyER_52983531609217552957]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyER_177340032615423364126704240091 : Nat.totient 177340032615423364126704240091 = 177340008592870446660597455520 := by
  rw [← show ((([(8120677, 1), (81182261, 1), (269000696564003, 1)] : List FactorBlock).map factorBlockValue).prod) = 177340032615423364126704240091 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyER_8120677, prime_oneHundredFiftyER_81182261, prime_oneHundredFiftyER_269000696564003]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyER_177340032615423364126704240092 : Nat.totient 177340032615423364126704240092 = 88670016236146565899221574800 := by
  rw [← show ((([(2, 2), (1239011701, 1), (35782558080826260923, 1)] : List FactorBlock).map factorBlockValue).prod) = 177340032615423364126704240092 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyER_2, prime_oneHundredFiftyER_1239011701, prime_oneHundredFiftyER_35782558080826260923]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyER_177340032615423364126704240093 : Nat.totient 177340032615423364126704240093 = 107073227233178307437027462784 := by
  rw [← show ((([(3, 2), (13, 2), (53, 1), (16937230103, 1), (129885093883087, 1)] : List FactorBlock).map factorBlockValue).prod) = 177340032615423364126704240093 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyER_3, prime_oneHundredFiftyER_13, prime_oneHundredFiftyER_53, prime_oneHundredFiftyER_16937230103, prime_oneHundredFiftyER_129885093883087]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyER_177340032615423364126704240094 : Nat.totient 177340032615423364126704240094 = 88550675774323106448192829776 := by
  rw [← show ((([(2, 1), (743, 1), (119340533388575615159289529, 1)] : List FactorBlock).map factorBlockValue).prod) = 177340032615423364126704240094 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyER_2, prime_oneHundredFiftyER_743, prime_oneHundredFiftyER_119340533388575615159289529]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyER_177340032615423364126704240095 : Nat.totient 177340032615423364126704240095 = 121604593736865634491525319680 := by
  rw [← show ((([(5, 1), (7, 1), (2149724321, 1), (2356980392894937077, 1)] : List FactorBlock).map factorBlockValue).prod) = 177340032615423364126704240095 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyER_5, prime_oneHundredFiftyER_7, prime_oneHundredFiftyER_2149724321, prime_oneHundredFiftyER_2356980392894937077]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyER_177340032615423364126704240096 : Nat.totient 177340032615423364126704240096 = 55343393444353008804754022400 := by
  rw [← show ((([(2, 5), (3, 1), (17, 1), (191, 1), (39341, 1), (14461317705429316663, 1)] : List FactorBlock).map factorBlockValue).prod) = 177340032615423364126704240096 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyER_2, prime_oneHundredFiftyER_3, prime_oneHundredFiftyER_17, prime_oneHundredFiftyER_191, prime_oneHundredFiftyER_39341, prime_oneHundredFiftyER_14461317705429316663]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyER_177340032615423364126704240097 : Nat.totient 177340032615423364126704240097 = 161071248650454965677357946400 := by
  rw [← show ((([(11, 1), (1097, 1), (14696281811172898328226091, 1)] : List FactorBlock).map factorBlockValue).prod) = 177340032615423364126704240097 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyER_11, prime_oneHundredFiftyER_1097, prime_oneHundredFiftyER_14696281811172898328226091]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyER_177340032615423364126704240098 : Nat.totient 177340032615423364126704240098 = 82048229843513650787700551376 := by
  rw [← show ((([(2, 1), (19, 1), (43, 1), (59399, 1), (1827155873176070515703, 1)] : List FactorBlock).map factorBlockValue).prod) = 177340032615423364126704240098 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyER_2, prime_oneHundredFiftyER_19, prime_oneHundredFiftyER_43, prime_oneHundredFiftyER_59399, prime_oneHundredFiftyER_1827155873176070515703]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyER_177340032615423364126704240099 : Nat.totient 177340032615423364126704240099 = 118226688410281270088868145536 := by
  rw [← show ((([(3, 1), (239147013649849, 1), (247184120357417, 1)] : List FactorBlock).map factorBlockValue).prod) = 177340032615423364126704240099 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyER_3, prime_oneHundredFiftyER_239147013649849, prime_oneHundredFiftyER_247184120357417]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyER_177340032615423364126704240100 : Nat.totient 177340032615423364126704240100 = 67732648986306399836233400320 := by
  rw [← show ((([(2, 2), (5, 2), (29, 1), (113, 1), (449, 1), (1205269042013298899237, 1)] : List FactorBlock).map factorBlockValue).prod) = 177340032615423364126704240100 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyER_2, prime_oneHundredFiftyER_5, prime_oneHundredFiftyER_29, prime_oneHundredFiftyER_113, prime_oneHundredFiftyER_449, prime_oneHundredFiftyER_1205269042013298899237]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyER_177340032615423364126704240101 : Nat.totient 177340032615423364126704240101 = 173011572054033970779600192000 := by
  rw [← show ((([(41, 1), (55921, 1), (77347805818148234432941, 1)] : List FactorBlock).map factorBlockValue).prod) = 177340032615423364126704240101 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyER_41, prime_oneHundredFiftyER_55921, prime_oneHundredFiftyER_77347805818148234432941]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

theorem freeKill_64OneHundredFiftyER : certifiedKill 1 177340032615423364126704239999 101 := by
  norm_num [certifiedKill, windowDiscrepancy, Finset.sum_range_succ,
    phi_oneHundredFiftyER_177340032615423364126704240000, phi_oneHundredFiftyER_177340032615423364126704240001, phi_oneHundredFiftyER_177340032615423364126704240002,
    phi_oneHundredFiftyER_177340032615423364126704240003, phi_oneHundredFiftyER_177340032615423364126704240004, phi_oneHundredFiftyER_177340032615423364126704240005,
    phi_oneHundredFiftyER_177340032615423364126704240006, phi_oneHundredFiftyER_177340032615423364126704240007, phi_oneHundredFiftyER_177340032615423364126704240008,
    phi_oneHundredFiftyER_177340032615423364126704240009, phi_oneHundredFiftyER_177340032615423364126704240010, phi_oneHundredFiftyER_177340032615423364126704240011,
    phi_oneHundredFiftyER_177340032615423364126704240012, phi_oneHundredFiftyER_177340032615423364126704240013, phi_oneHundredFiftyER_177340032615423364126704240014,
    phi_oneHundredFiftyER_177340032615423364126704240015, phi_oneHundredFiftyER_177340032615423364126704240016, phi_oneHundredFiftyER_177340032615423364126704240017,
    phi_oneHundredFiftyER_177340032615423364126704240018, phi_oneHundredFiftyER_177340032615423364126704240019, phi_oneHundredFiftyER_177340032615423364126704240020,
    phi_oneHundredFiftyER_177340032615423364126704240021, phi_oneHundredFiftyER_177340032615423364126704240022, phi_oneHundredFiftyER_177340032615423364126704240023,
    phi_oneHundredFiftyER_177340032615423364126704240024, phi_oneHundredFiftyER_177340032615423364126704240025, phi_oneHundredFiftyER_177340032615423364126704240026,
    phi_oneHundredFiftyER_177340032615423364126704240027, phi_oneHundredFiftyER_177340032615423364126704240028, phi_oneHundredFiftyER_177340032615423364126704240029,
    phi_oneHundredFiftyER_177340032615423364126704240030, phi_oneHundredFiftyER_177340032615423364126704240031, phi_oneHundredFiftyER_177340032615423364126704240032,
    phi_oneHundredFiftyER_177340032615423364126704240033, phi_oneHundredFiftyER_177340032615423364126704240034, phi_oneHundredFiftyER_177340032615423364126704240035,
    phi_oneHundredFiftyER_177340032615423364126704240036, phi_oneHundredFiftyER_177340032615423364126704240037, phi_oneHundredFiftyER_177340032615423364126704240038,
    phi_oneHundredFiftyER_177340032615423364126704240039, phi_oneHundredFiftyER_177340032615423364126704240040, phi_oneHundredFiftyER_177340032615423364126704240041,
    phi_oneHundredFiftyER_177340032615423364126704240042, phi_oneHundredFiftyER_177340032615423364126704240043, phi_oneHundredFiftyER_177340032615423364126704240044,
    phi_oneHundredFiftyER_177340032615423364126704240045, phi_oneHundredFiftyER_177340032615423364126704240046, phi_oneHundredFiftyER_177340032615423364126704240047,
    phi_oneHundredFiftyER_177340032615423364126704240048, phi_oneHundredFiftyER_177340032615423364126704240049, phi_oneHundredFiftyER_177340032615423364126704240050,
    phi_oneHundredFiftyER_177340032615423364126704240051, phi_oneHundredFiftyER_177340032615423364126704240052, phi_oneHundredFiftyER_177340032615423364126704240053,
    phi_oneHundredFiftyER_177340032615423364126704240054, phi_oneHundredFiftyER_177340032615423364126704240055, phi_oneHundredFiftyER_177340032615423364126704240056,
    phi_oneHundredFiftyER_177340032615423364126704240057, phi_oneHundredFiftyER_177340032615423364126704240058, phi_oneHundredFiftyER_177340032615423364126704240059,
    phi_oneHundredFiftyER_177340032615423364126704240060, phi_oneHundredFiftyER_177340032615423364126704240061, phi_oneHundredFiftyER_177340032615423364126704240062,
    phi_oneHundredFiftyER_177340032615423364126704240063, phi_oneHundredFiftyER_177340032615423364126704240064, phi_oneHundredFiftyER_177340032615423364126704240065,
    phi_oneHundredFiftyER_177340032615423364126704240066, phi_oneHundredFiftyER_177340032615423364126704240067, phi_oneHundredFiftyER_177340032615423364126704240068,
    phi_oneHundredFiftyER_177340032615423364126704240069, phi_oneHundredFiftyER_177340032615423364126704240070, phi_oneHundredFiftyER_177340032615423364126704240071,
    phi_oneHundredFiftyER_177340032615423364126704240072, phi_oneHundredFiftyER_177340032615423364126704240073, phi_oneHundredFiftyER_177340032615423364126704240074,
    phi_oneHundredFiftyER_177340032615423364126704240075, phi_oneHundredFiftyER_177340032615423364126704240076, phi_oneHundredFiftyER_177340032615423364126704240077,
    phi_oneHundredFiftyER_177340032615423364126704240078, phi_oneHundredFiftyER_177340032615423364126704240079, phi_oneHundredFiftyER_177340032615423364126704240080,
    phi_oneHundredFiftyER_177340032615423364126704240081, phi_oneHundredFiftyER_177340032615423364126704240082, phi_oneHundredFiftyER_177340032615423364126704240083,
    phi_oneHundredFiftyER_177340032615423364126704240084, phi_oneHundredFiftyER_177340032615423364126704240085, phi_oneHundredFiftyER_177340032615423364126704240086,
    phi_oneHundredFiftyER_177340032615423364126704240087, phi_oneHundredFiftyER_177340032615423364126704240088, phi_oneHundredFiftyER_177340032615423364126704240089,
    phi_oneHundredFiftyER_177340032615423364126704240090, phi_oneHundredFiftyER_177340032615423364126704240091, phi_oneHundredFiftyER_177340032615423364126704240092,
    phi_oneHundredFiftyER_177340032615423364126704240093, phi_oneHundredFiftyER_177340032615423364126704240094, phi_oneHundredFiftyER_177340032615423364126704240095,
    phi_oneHundredFiftyER_177340032615423364126704240096, phi_oneHundredFiftyER_177340032615423364126704240097, phi_oneHundredFiftyER_177340032615423364126704240098,
    phi_oneHundredFiftyER_177340032615423364126704240099, phi_oneHundredFiftyER_177340032615423364126704240100, phi_oneHundredFiftyER_177340032615423364126704240101]

end TotientTailPeriodKiller
end Erdos249257
